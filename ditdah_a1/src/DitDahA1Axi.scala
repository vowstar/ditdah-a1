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
      channel.bits.id := 0.U(1)
      channel.bits.len := 0.U(8)
      channel.bits.size := request.size
      channel.bits.burst := 1.U(2)
      channel.bits.lock := false.B
      channel.bits.cache := 0.U(4)
      channel.bits.prot := request.fetch.?(5.U(3), 1.U(3))
      channel.bits.qos := 0.U(4)
    ar.valid := (state === 1.U(3)) & !request.write
    aw.valid := (state === 1.U(3)) & request.write & !awDone
    w.valid := (state === 1.U(3)) & request.write & !wDone
    w.bits.last := true.B
    val laneBits = Integer.numberOfTrailingZeros(parameter.axiDataBits / 8)
    val lane = request.address.asBits.bits(laneBits - 1, 0).asUInt
    val byteShift = (lane.asBits ## 0.B(3)).asUInt
    w.bits.data := (request.data << byteShift).asBits.bits(parameter.axiDataBits - 1, 0).asUInt
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
      awDone := false.B
      wDone := false.B
      fault := false.B
      data := 0.U(64)
      state := 1.U(3)
    }
    when(ar.valid & ar.ready) { state := 2.U(3) }
    when(aw.valid & aw.ready) { awDone := true.B }
    when(w.valid & w.ready) { wDone := true.B }
    when((state === 1.U(3)) & request.write & (awDone | (aw.valid & aw.ready)) & (wDone | (w.valid & w.ready))) { state := 3.U(3) }
    when(r.valid & r.ready) {
      data := readData
      fault := fault | (r.bits.resp =/= 0.U(2)) | (r.bits.id =/= 0.U(1)) | !r.bits.last
      when(r.bits.last) { state := 4.U(3) }
    }
    when(b.valid & b.ready) {
      fault := (b.bits.resp =/= 0.U(2)) | (b.bits.id =/= 0.U(1))
      state := 4.U(3)
    }
    when(io.memory.response.valid & io.memory.response.ready) { state := 0.U(3) }
