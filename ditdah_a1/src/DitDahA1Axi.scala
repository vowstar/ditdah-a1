// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1AxiIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val hartId = Flipped(UInt(4))
  val memory = Flipped(new MemoryPort)
  val axi = Aligned(new AxiBundle(parameter))

@generator
object DitDahA1Axi extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1AxiIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Axi"
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
    val aw = io.axi.aw
    val w = io.axi.w
    val b = io.axi.b
    val ar = io.axi.ar
    val r = io.axi.r
    io.memory.request.ready := state === 0.U(3)
    io.memory.response.valid := state === 4.U(3)
    io.memory.response.bits.data := data
    io.memory.response.bits.fault := fault
    io.memory.response.bits.tag := request.tag
    for channel <- Seq(aw, ar) do
      channel.bits.addr := request.address.asBits.bits(parameter.physicalAddressBits - 1, 0).asUInt
      channel.bits.id := hartId
      channel.bits.len := 0.U(8)
      channel.bits.size := request.size
      channel.bits.burst := 1.U(2)
      channel.bits.lock := request.atomic
      channel.bits.cache := 0.U(4)
      val privileged = if parameter.enableUserMode then request.privileged else true.B
      channel.bits.prot := (request.fetch.asBits ## 0.B(1) ## privileged.asBits).asUInt
      channel.bits.qos := 0.U(4)
    ar.valid := (state === 1.U(3)) & !request.write
    aw.valid := (state === 1.U(3)) & request.write & !awDone
    w.valid := (state === 1.U(3)) & request.write & !wDone
    w.bits.last := true.B
    val laneBits = Integer.numberOfTrailingZeros(parameter.axiDataBits / 8)
    val lane = request.address.asBits.bits(laneBits - 1, 0).asUInt
    val byteShift = (lane.asBits ## 0.B(3)).asUInt
    val update = (request.atomicOperation === 1.U(5)).?(request.data,
      (request.atomicOperation === 8.U(5)).?((data.asBits | request.data.asBits).asUInt,
        (data + request.data).asBits.bits(63, 0).asUInt))
    val writeData = amo.?(update, request.data)
    w.bits.data := (writeData << byteShift).asBits.bits(parameter.axiDataBits - 1, 0).asUInt
    w.bits.strb := (request.mask << lane).asBits.bits(parameter.axiDataBits / 8 - 1, 0).asUInt
    val shiftedReadData = (r.bits.data >> byteShift).asBits.bits(63, 0).asUInt
    val readData = Wire(UInt(64))
    readData := 0.U(64)
    for size <- 0 to 3 do
      when(request.size === size.U(3)) { readData := shiftedReadData.asBits.bits((8 << size) - 1, 0).asUInt }
    r.ready := state === 2.U(3)
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
      state := 1.U(3)
      when(inputSc & !io.memory.request.bits.scEligible) { data := 1.U(64); state := 4.U(3) }
    }
    when(ar.valid & ar.ready) { state := 2.U(3) }
    when(aw.valid & aw.ready) { awDone := true.B }
    when(w.valid & w.ready) { wDone := true.B }
    when((state === 1.U(3)) & request.write & (awDone | (aw.valid & aw.ready)) & (wDone | (w.valid & w.ready))) { state := 3.U(3) }
    when(r.valid & r.ready) {
      data := readData
      val readFault = fault | (r.bits.resp =/= request.atomic.?(1.U(2), 0.U(2))) | (r.bits.id =/= hartId) | !r.bits.last
      fault := readFault
      when(r.bits.last) {
        when(amo & !readFault) { request.write := true.B; state := 1.U(3) }
          .otherwise { state := 4.U(3) }
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
    when(io.memory.response.valid & io.memory.response.ready) { state := 0.U(3) }
