// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1FetchIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val pmp = Option.when(parameter.pmpEntries != 0)(Flipped(new PmpState(parameter)))
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val request = Flipped(new Decoupled(new FetchRequest))
  val output = Aligned(new Decoupled(new FetchPacket))
  val cancel = Flipped(Bool())
  val memory = Aligned(new MemoryPort)

@generator
object DitDahA1Fetch extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1FetchIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Fetch"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1FetchIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val state = RegInit(0.U(2))
    val packet = Reg(new FetchPacket)
    val killed = RegInit(false.B)
    val request = io.memory.request
    val response = io.memory.response
    val permitted = if parameter.pmpEntries == 0 then true.B else
      val pmp = DitDahA1Pmp.instantiate(parameter)
      pmp.io.state :<= io.pmp.get
      pmp.io.address := io.request.bits.pc
      pmp.io.size := 2.U(3)
      pmp.io.write := false.B
      pmp.io.fetch := true.B
      pmp.io.allowed
    io.request.ready := (state === 0.U(2)) & !io.cancel
    io.output.valid := (state === 3.U(2)) & !killed & !io.cancel
    io.output.bits :<= packet
    request.valid := state === 1.U(2)
    request.bits.address := packet.pc
    request.bits.data := 0.U(64)
    request.bits.size := 2.U(3)
    request.bits.mask := 0.U(8)
    request.bits.tag := packet.tag
    request.bits.fetch := true.B
    request.bits.write := false.B
    response.ready := state === 2.U(2)
    when(io.request.valid & io.request.ready) {
      packet.pc := io.request.bits.pc
      packet.tag := io.request.bits.tag
      packet.instruction := 0.U(32)
      packet.length := 4.U(3)
      packet.fault := false.B
      packet.cause := 0.U(64)
      packet.tval := 0.U(64)
      killed := false.B
      state := 1.U(2)
      if parameter.pmpEntries != 0 then
        when(!permitted) {
          packet.fault := true.B
          packet.cause := 1.U(64)
          packet.tval := io.request.bits.pc
          state := 3.U(2)
        }
      when(io.request.bits.pc.asBits.bits(1, 0) =/= 0.B(2)) {
        packet.fault := true.B
        if parameter.pmpEntries != 0 then packet.cause := 0.U(64)
        packet.tval := io.request.bits.pc
        state := 3.U(2)
      }
    }
    when(request.valid & request.ready) { state := 2.U(2) }
    when(response.valid & response.ready) {
      val fault = response.bits.fault | (response.bits.tag =/= packet.tag)
      packet.instruction := fault.?(0.U(32), response.bits.data.asBits.bits(31, 0).asUInt)
      packet.fault := fault
      packet.cause := fault.?(1.U(64), 0.U(64))
      packet.tval := fault.?(packet.pc, 0.U(64))
      state := 3.U(2)
    }
    when(io.cancel & (state =/= 0.U(2))) { killed := true.B }
    when((state === 3.U(2)) & (killed | io.cancel | io.output.ready)) { state := 0.U(2) }
