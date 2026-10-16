// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1GprIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val raddr1 = Flipped(UInt(5))
  val raddr2 = Flipped(UInt(5))
  val rdata1 = Aligned(UInt(64))
  val rdata2 = Aligned(UInt(64))
  val we = Flipped(Bool())
  val waddr = Flipped(UInt(5))
  val wdata = Flipped(UInt(64))

@generator
object DitDahA1Gpr extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1GprIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Gpr"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1GprIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val registers = Seq.fill(31)(RegInit(0.U(64)))
    io.rdata1 := 0.U(64)
    io.rdata2 := 0.U(64)
    for i <- 1 to 31 do
      when(io.raddr1 === i.U(5)) { io.rdata1 := registers(i - 1) }
      when(io.raddr2 === i.U(5)) { io.rdata2 := registers(i - 1) }
      when(io.we & (io.waddr === i.U(5))) { registers(i - 1) := io.wdata }
