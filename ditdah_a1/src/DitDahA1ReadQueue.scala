// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1ReadQueueIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val ports = Flipped(Vec(2 * parameter.hartCount, new MemoryPort))
  val ar = Aligned(new Decoupled(new AxiAddress(parameter)))
  val r = Flipped(new Decoupled(new AxiRead(parameter)))
  val empty = Aligned(Bool())

@generator
object DitDahA1ReadQueue extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1ReadQueueIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1ReadQueue"
  def architecture(parameter: DitDahA1Parameter) =
    require(parameter.hartCount > 1, "Concurrent reads require multiple harts")
    val io = summon[Interface[DitDahA1ReadQueueIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val count = 2 * parameter.hartCount
    val ownerBits = 32 - Integer.numberOfLeadingZeros(count - 1)
    val state = Seq.fill(2)(RegInit(0.U(3)))
    val owner = Seq.fill(2)(Reg(UInt(ownerBits)))
    val request = Seq.fill(2)(Reg(new MemoryRequest))
    val data = Seq.fill(2)(Reg(UInt(64)))
    val fault = Seq.fill(2)(RegInit(false.B))
    val poisoned = RegInit(false.B)
    val line = request.map(DitDahA1Axi.lineRead(parameter, _))
    val beat = Option.when(parameter.enableLineRefill)(Seq.fill(2)(RegInit(0.U(3))))
    val terminal = Option.when(parameter.enableLineRefill)(Seq.fill(2)(Reg(Bool())))
    val slices = parameter.axiDataBits / 64
    val sliceBits = math.max(1, Integer.numberOfTrailingZeros(slices))
    val slice = Option.when(parameter.enableLineRefill && slices > 1)(RegInit(0.U(sliceBits)))
    val block = Option.when(slice.isDefined)(Reg(UInt(parameter.axiDataBits)))
    val finalSlice = slice.map(_ === (slices - 1).U(sliceBits)).getOrElse(true.B)
    val blockBusy = if block.isDefined then state.map(_ === 5.U(3)).reduce(_ | _) else false.B
    val next = RegInit(0.U(ownerBits))
    val free = state.map(_ === 0.U(3))
    val waiting = state.map(s => (s === 3.U(3)) | (if parameter.enableLineRefill then s === 6.U(3) else false.B))
    val inflight = (0 until 2).map(n => waiting(n) |
      terminal.map(t => (state(n) === 5.U(3)) & !t(n)).getOrElse(false.B))
    val hart = owner.map(_.asBits.bits(ownerBits - 1, 1).asUInt)
    val available = (0 until count).map { i =>
      !(0 until 2).map(n => !free(n) & (hart(n) === (i / 2).U(parameter.axiIdBits))).reduce(_ | _)
    }
    val valid = (0 until count).map(i => io.ports(i).request.valid & available(i))
    val selected = DitDahA1MemoryArbiter.select(valid, next)
    val captured = Wire(new MemoryRequest)
    captured :<= io.ports(0).request.bits
    for i <- 1 until count do
      when(selected === i.U(ownerBits)) { captured :<= io.ports(i).request.bits }
    val accept = valid.reduce(_ | _) & free.reduce(_ | _) & !poisoned
    val slot = !free(0)
    io.empty := free.reduce(_ & _) & !poisoned
    for i <- 0 until count do
      val port = io.ports(i)
      port.request.ready := available(i) & free.reduce(_ | _) & (selected === i.U(ownerBits)) & !poisoned
      port.response.valid := false.B
      port.response.bits.data := 0.U(64)
      port.response.bits.fault := false.B
      port.response.bits.tag := 0.U(8)
      port.response.bits.last := true.B
      for n <- 0 until 2 do
        val streaming = if parameter.enableLineRefill then state(n) === 5.U(3) else false.B
        when(((state(n) === 4.U(3)) | streaming) & (owner(n) === i.U(ownerBits))) {
          port.response.valid := true.B
          port.response.bits.data := data(n)
          block.foreach { value =>
            when(streaming) { port.response.bits.data := (value >> (slice.get.asBits ## 0.B(6)).asUInt).asBits.bits(63, 0).asUInt }
          }
          port.response.bits.fault := fault(n)
          port.response.bits.tag := request(n).tag
          terminal.foreach(t => port.response.bits.last := !streaming | (t(n) & finalSlice))
          when(port.response.ready) {
            state(n) := 0.U(3)
            if parameter.enableLineRefill then
              when(streaming) {
                slice.foreach(s => s := (s + 1.U(sliceBits)).asBits.bits(sliceBits - 1, 0).asUInt)
                state(n) := 5.U(3)
                when(finalSlice) {
                  val end = beat.get(n) === (512 / parameter.axiDataBits - 1).U(3)
                  when(!end) { beat.get(n) := (beat.get(n) + 1.U(3)).asBits.bits(2, 0).asUInt }
                  state(n) := terminal.get(n).?(0.U(3), end.?(6.U(3), 3.U(3)))
                }
              }
          }
        }
    val addressActive = state.map(_ === 2.U(3)).reduce(_ | _)
    val addressSlot = state(1) === 2.U(3)
    val addressRequest = Wire(new MemoryRequest)
    addressRequest :<= request(0)
    when(addressSlot) { addressRequest :<= request(1) }
    DitDahA1Axi.readAddress(parameter, io.ar.bits, addressRequest, addressSlot.?(hart(1), hart(0)))
    io.ar.valid := addressActive
    val matches = (0 until 2).map(n => inflight(n) & (io.r.bits.id === hart(n)))
    val known = matches.reduce(_ | _)
    io.r.ready := (!known & inflight.reduce(_ | _)) | (0 until 2).map(n =>
      matches(n) & waiting(n) & (!line(n) | !blockBusy | (state(n) === 6.U(3)))).reduce(_ | _)
    val unexpected = io.r.valid & io.r.ready & !known
    when(unexpected) { poisoned := true.B }
    for n <- 0 until 2 do
      val ordinary = parameter.memoryRegions.filter(!_.device).foldLeft[Referable[Bool]](false.B) { (allowed, region) =>
        allowed | ((request(n).address >= region.base.U(64)) & (request(n).address < (region.base + region.size).U(64)))
      }
      val permitted = !request(n).write & !request(n).atomic &
        ordinary & DitDahA1Memory.permitted(parameter, request(n))
      when((state(n) === 1.U(3)) & !permitted) {
        data(n) := 0.U(64)
        fault(n) := true.B
        state(n) := 4.U(3)
      }
      when(!poisoned & !unexpected & !addressActive & (state(n) === 1.U(3)) & permitted &
        (if n == 0 then true.B else state(0) =/= 1.U(3))) { state(n) := 2.U(3) }
      when(io.ar.valid & io.ar.ready & (addressSlot === (n == 1).B)) { state(n) := 3.U(3) }
      val laneBits = Integer.numberOfTrailingZeros(parameter.axiDataBits / 8)
      val shift = (request(n).address.asBits.bits(laneBits - 1, 0) ## 0.B(3)).asUInt
      when(io.r.valid & io.r.ready & matches(n)) {
        data(n) := DitDahA1Axi.readData(request(n).size, io.r.bits.data, shift)
        fault(n) := fault(n) | poisoned | (io.r.bits.resp =/= 0.U(2)) | !io.r.bits.last
        when(io.r.bits.last) { state(n) := 4.U(3) }
        if parameter.enableLineRefill then
          when(line(n) & (state(n) === 3.U(3))) {
            block.foreach(_ := io.r.bits.data)
            slice.foreach(_ := 0.U(sliceBits))
            terminal.get(n) := io.r.bits.last
            data(n) := io.r.bits.data.asBits.bits(63, 0).asUInt
            fault(n) := fault(n) | poisoned | (io.r.bits.resp =/= 0.U(2)) |
              (io.r.bits.last =/= (beat.get(n) === (512 / parameter.axiDataBits - 1).U(3)))
            state(n) := 5.U(3)
          }
          when(state(n) === 6.U(3)) {
            fault(n) := true.B
            data(n) := 0.U(64)
          }
      }
      when(accept & (slot === (n == 1).B)) {
        request(n) :<= captured
        owner(n) := selected
        fault(n) := false.B
        beat.foreach(_(n) := 0.U(3))
        state(n) := 1.U(3)
      }
    when(accept) {
      next := (selected === (count - 1).U(ownerBits)).?(0.U(ownerBits),
        (selected + 1.U(ownerBits)).asBits.bits(ownerBits - 1, 0).asUInt)
    }
