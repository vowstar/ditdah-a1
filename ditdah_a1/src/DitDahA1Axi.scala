// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

class DitDahA1AxiIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val hartId = Flipped(UInt(4))
  val memory = Flipped(new MemoryPort)
  val axi = Aligned(new AxiBundle(parameter))

@generator
object DitDahA1Axi extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1AxiIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Axi"
  def address(parameter: DitDahA1Parameter, channel: Referable[AxiAddress], request: Referable[MemoryRequest],
    id: Referable[UInt])(using Arena, Context, Block, InstanceContext): Unit =
    channel.addr := request.address.asBits.bits(parameter.physicalAddressBits - 1, 0).asUInt
    channel.id := id
    channel.len := 0.U(8)
    channel.size := request.size
    channel.burst := 1.U(2)
    channel.lock := request.atomic
    channel.cache := 0.U(4)
    if parameter.l2CacheBytes != 0 then
      for size <- Seq(0, 1, 2, 3, 6) do
        val bytes = 1 << size
        val cacheable = request.fetch.?(DitDahA1Memory.executable(parameter, request.address, bytes),
          DitDahA1Memory.dataCacheable(parameter, request.address, bytes)) & !request.atomic
        for region <- parameter.memoryRegions.filter(r => !r.device && r.size >= bytes) do
          when((request.size === size.U(3)) & (request.address >= region.base.U(64)) &
            (request.address <= (region.base + region.size - bytes).U(64))) {
            channel.cache := cacheable.?(request.write.?(6.U(4), 14.U(4)), 2.U(4))
          }
    val privileged = if parameter.enableUserMode then request.privileged else true.B
    channel.prot := (request.fetch.asBits ## 0.B(1) ## privileged.asBits).asUInt
    channel.qos := 0.U(4)

  def lineRead(parameter: DitDahA1Parameter, request: Referable[MemoryRequest])
    (using Arena, Context, Block, InstanceContext): Referable[Bool] =
    val client = (if parameter.enableBurstRefill then request.fetch else false.B) |
      (if parameter.enableDataBurstRefill then !request.fetch else false.B)
    client & !request.write & !request.atomic & (request.size === 6.U(3))

  def readAddress(parameter: DitDahA1Parameter, channel: Referable[AxiAddress], request: Referable[MemoryRequest],
    id: Referable[UInt])(using Arena, Context, Block, InstanceContext): Unit =
    address(parameter, channel, request, id)
    if parameter.enableLineRefill then
      when(lineRead(parameter, request)) {
        channel.len := (512 / parameter.axiDataBits - 1).U(8)
        channel.size := Integer.numberOfTrailingZeros(parameter.axiDataBits / 8).U(3)
      }

  def readData(size: Referable[UInt], data: Referable[UInt], shift: Referable[UInt])
    (using Arena, Context, Block, InstanceContext): Referable[UInt] =
    val shifted = (data >> shift).asBits.bits(63, 0)
    val result = Wire(UInt(64))
    result := 0.U(64)
    for width <- 0 to 3 do
      when(size === width.U(3)) { result := shifted.bits((8 << width) - 1, 0).asUInt }
    result

  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1AxiIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val state = RegInit(0.U(3))
    val request = Reg(new MemoryRequest)
    val idBits = parameter.axiIdBits
    val hartId = Reg(UInt(idBits))
    val lr = request.atomic & (request.atomicOperation === 2.U(5))
    val sc = request.atomic & (request.atomicOperation === 3.U(5))
    val amo = request.atomic & !lr & !sc
    val data = RegInit(0.U(64))
    val fault = RegInit(false.B)
    val awDone = RegInit(false.B)
    val wDone = RegInit(false.B)
    val line = lineRead(parameter, request)
    val beat = Option.when(parameter.enableLineRefill)(RegInit(0.U(3)))
    val terminal = Option.when(parameter.enableLineRefill)(Reg(Bool()))
    val slices = parameter.axiDataBits / 64
    val sliceBits = math.max(1, Integer.numberOfTrailingZeros(slices))
    val slice = Option.when(parameter.enableLineRefill && slices > 1)(RegInit(0.U(sliceBits)))
    val block = Option.when(slice.isDefined)(Reg(UInt(parameter.axiDataBits)))
    val finalSlice = slice.map(_ === (slices - 1).U(sliceBits)).getOrElse(true.B)
    val aw = io.axi.aw
    val w = io.axi.w
    val b = io.axi.b
    val ar = io.axi.ar
    val r = io.axi.r
    io.memory.request.ready := state === 0.U(3)
    io.memory.response.valid := (state === 4.U(3)) | (if parameter.enableLineRefill then state === 5.U(3) else false.B)
    io.memory.response.bits.data := data
    block.foreach { value =>
      when(state === 5.U(3)) { io.memory.response.bits.data := (value >> (slice.get.asBits ## 0.B(6)).asUInt).asBits.bits(63, 0).asUInt }
    }
    io.memory.response.bits.fault := fault
    io.memory.response.bits.tag := request.tag
    io.memory.response.bits.last := terminal.map(last => (state =/= 5.U(3)) | (last & finalSlice)).getOrElse(true.B)
    address(parameter, aw.bits, request, hartId)
    readAddress(parameter, ar.bits, request, hartId)
    ar.valid := (state === 1.U(3)) & !request.write
    aw.valid := (state === 1.U(3)) & request.write & !awDone
    w.valid := (state === 1.U(3)) & request.write & !wDone
    w.bits.last := true.B
    val laneBits = Integer.numberOfTrailingZeros(parameter.axiDataBits / 8)
    val lane = request.address.asBits.bits(laneBits - 1, 0).asUInt
    val byteShift = (lane.asBits ## 0.B(3)).asUInt
    val update = Wire(UInt(64))
    update := request.data
    if parameter.enableA then
      def operand(value: Referable[UInt]): Referable[UInt] =
        (request.size === 2.U(3)).?((value.asBits.bit(31).?(BigInt("ffffffff", 16).B(32), 0.B(32)) ## value.asBits.bits(31, 0)).asUInt, value)
      val left = operand(data)
      val right = operand(request.data)
      val less = request.atomicOperation.asBits.bit(3).?(left < right, left.asBits.asSInt < right.asBits.asSInt)
      update := (left + right).asBits.bits(63, 0).asUInt
      when(request.atomicOperation === 1.U(5)) { update := right }
      when(request.atomicOperation === 4.U(5)) { update := (left.asBits ^ right.asBits).asUInt }
      when(request.atomicOperation === 8.U(5)) { update := (left.asBits | right.asBits).asUInt }
      when(request.atomicOperation === 12.U(5)) { update := (left.asBits & right.asBits).asUInt }
      when(request.atomicOperation.asBits.bit(4)) { update := (less ^ request.atomicOperation.asBits.bit(2)).?(left, right) }
    val writeData = amo.?((request.size === 2.U(3)).?(update.asBits.bits(31, 0).asUInt, update), request.data)
    w.bits.data := (writeData << byteShift).asBits.bits(parameter.axiDataBits - 1, 0).asUInt
    w.bits.strb := (request.mask << lane).asBits.bits(parameter.axiDataBits / 8 - 1, 0).asUInt
    val readValue = readData(request.size, r.bits.data, byteShift)
    r.ready := (state === 2.U(3)) | (if parameter.enableLineRefill then state === 6.U(3) else false.B)
    b.ready := state === 3.U(3)
    when(io.memory.request.valid & io.memory.request.ready) {
      request :<= io.memory.request.bits
      hartId := io.hartId.asBits.bits(idBits - 1, 0).asUInt
      val inputSc = io.memory.request.bits.atomic & (io.memory.request.bits.atomicOperation === 3.U(5))
      request.write := io.memory.request.bits.write & (!io.memory.request.bits.atomic | inputSc)
      awDone := false.B
      wDone := false.B
      fault := false.B
      data := 0.U(64)
      beat.foreach(_ := 0.U(3))
      state := 1.U(3)
      when(inputSc & !io.memory.request.bits.scEligible) { data := 1.U(64); state := 4.U(3) }
    }
    when(ar.valid & ar.ready) { state := 2.U(3) }
    when(aw.valid & aw.ready) { awDone := true.B }
    when(w.valid & w.ready) { wDone := true.B }
    when((state === 1.U(3)) & request.write & (awDone | (aw.valid & aw.ready)) & (wDone | (w.valid & w.ready))) { state := 3.U(3) }
    when(r.valid & r.ready) {
      data := readValue
      val readFault = fault | (r.bits.resp =/= request.atomic.?(1.U(2), 0.U(2))) | (r.bits.id =/= hartId) | !r.bits.last
      fault := readFault
      when(r.bits.last) {
        when(amo & !readFault) { request.write := true.B; state := 1.U(3) }
          .otherwise { state := 4.U(3) }
      }
      if parameter.enableLineRefill then
        when(line & (state === 2.U(3))) {
          block.foreach(_ := r.bits.data)
          slice.foreach(_ := 0.U(sliceBits))
          terminal.get := r.bits.last
          data := r.bits.data.asBits.bits(63, 0).asUInt
          fault := fault | (r.bits.resp =/= 0.U(2)) | (r.bits.id =/= hartId) |
            (r.bits.last =/= (beat.get === (512 / parameter.axiDataBits - 1).U(3)))
          state := 5.U(3)
        }
        when(state === 6.U(3)) {
          fault := true.B
          data := 0.U(64)
          when(r.bits.last) { state := 4.U(3) }
        }
    }
    when(b.valid & b.ready) {
      when(amo & (b.bits.resp === 0.U(2)) & (b.bits.id === hartId)) {
        request.write := false.B
        awDone := false.B
        wDone := false.B
        state := 1.U(3)
      }.otherwise {
        fault := (b.bits.resp =/= request.atomic.?(1.U(2), 0.U(2))) | (b.bits.id =/= hartId)
        when(sc) {
          data := (b.bits.resp === 0.U(2)).?(1.U(64), 0.U(64))
          fault := b.bits.resp.asBits.bit(1) | (b.bits.id =/= hartId)
        }
        state := 4.U(3)
      }
    }
    when(io.memory.response.valid & io.memory.response.ready) {
      state := 0.U(3)
      if parameter.enableLineRefill then
        when(state === 5.U(3)) {
          slice.foreach(value => value := (value + 1.U(sliceBits)).asBits.bits(sliceBits - 1, 0).asUInt)
          state := 5.U(3)
          when(finalSlice) {
            beat.get := (beat.get + 1.U(3)).asBits.bits(2, 0).asUInt
            state := terminal.get.?(0.U(3), (beat.get === (512 / parameter.axiDataBits - 1).U(3)).?(6.U(3), 2.U(3)))
          }
        }
    }
