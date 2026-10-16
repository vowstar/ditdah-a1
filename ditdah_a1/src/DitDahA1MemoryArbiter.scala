// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1MemoryArbiterIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val instruction = Flipped(new MemoryPort)
  val data = Flipped(new MemoryPort)
  val downstream = Aligned(new MemoryPort)

@generator
object DitDahA1MemoryArbiter extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1MemoryArbiterIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1MemoryArbiter"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1MemoryArbiterIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val state = RegInit(0.U(2))
    val dataOwner = Reg(Bool())
    val request = Reg(new MemoryRequest)
    val instruction = io.instruction
    val data = io.data
    val down = io.downstream
    val idle = state === 0.U(2)
    data.request.ready := idle
    instruction.request.ready := idle & !data.request.valid
    down.request.valid := state === 1.U(2)
    down.request.bits :<= request
    instruction.response.valid := (state === 2.U(2)) & !dataOwner & down.response.valid
    data.response.valid := (state === 2.U(2)) & dataOwner & down.response.valid
    instruction.response.bits :<= down.response.bits
    data.response.bits :<= down.response.bits
    down.response.ready := (state === 2.U(2)) & dataOwner.?(data.response.ready, instruction.response.ready)
    when(data.request.valid & data.request.ready) {
      request :<= data.request.bits
      dataOwner := true.B
      state := 1.U(2)
    }
    when(instruction.request.valid & instruction.request.ready) {
      request :<= instruction.request.bits
      dataOwner := false.B
      state := 1.U(2)
    }
    when(down.request.valid & down.request.ready) { state := 2.U(2) }
    when(down.response.valid & down.response.ready) { state := 0.U(2) }
