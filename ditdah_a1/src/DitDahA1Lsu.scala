// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1LsuIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val input = Flipped(new Decoupled(new ResultPacket))
  val output = Aligned(new Decoupled(new ResultPacket))
  val storeAllowed = Flipped(Bool())
  val memory = Aligned(new MemoryPort)

@generator
object DitDahA1Lsu extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1LsuIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Lsu"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1LsuIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val state = RegInit(0.U(2))
    val packet = Reg(new ResultPacket)
    val request = io.memory.request
    val response = io.memory.response
    io.input.ready := (state === 0.U(2)) & (io.input.bits.instruction.fault | !io.input.bits.store | io.storeAllowed)
    io.output.valid := state === 3.U(2)
    io.output.bits :<= packet
    request.valid := state === 1.U(2)
    request.bits.address := packet.address
    request.bits.data := packet.storeData
    request.bits.size := 3.U(3)
    request.bits.mask := packet.store.?(255.U(8), 0.U(8))
    request.bits.tag := packet.instruction.tag
    request.bits.write := packet.store
    request.bits.fetch := false.B
    response.ready := state === 2.U(2)
    when(io.input.valid & io.input.ready) {
      packet :<= io.input.bits
      state := 1.U(2)
      when(!io.input.bits.instruction.fault & (io.input.bits.address.asBits.bits(2, 0) =/= 0.B(3))) {
        packet.instruction.fault := true.B
        packet.instruction.cause := io.input.bits.store.?(6.U(64), 4.U(64))
        packet.instruction.tval := io.input.bits.address
        state := 3.U(2)
      }
      when(io.input.bits.instruction.fault) { state := 3.U(2) }
    }
    when(request.valid & request.ready) { state := 2.U(2) }
    when(response.valid & response.ready) {
      when(packet.load) { packet.value := response.bits.data }
      when(response.bits.fault | (response.bits.tag =/= packet.instruction.tag)) {
        packet.instruction.fault := true.B
        packet.instruction.cause := packet.store.?(7.U(64), 5.U(64))
        packet.instruction.tval := packet.address
      }
      state := 3.U(2)
    }
    when(io.output.valid & io.output.ready) { state := 0.U(2) }
