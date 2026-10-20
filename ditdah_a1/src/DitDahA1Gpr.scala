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
  val raddr1 = Flipped(Vec(parameter.issueWidth, UInt(5)))
  val raddr2 = Flipped(Vec(parameter.issueWidth, UInt(5)))
  val rdata1 = Aligned(Vec(parameter.issueWidth, UInt(64)))
  val rdata2 = Aligned(Vec(parameter.issueWidth, UInt(64)))
  val we = Flipped(Vec(parameter.issueWidth, Bool()))
  val waddr = Flipped(Vec(parameter.issueWidth, UInt(5)))
  val wdata = Flipped(Vec(parameter.issueWidth, UInt(64)))

@generator
object DitDahA1Gpr extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1GprIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Gpr"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1GprIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val registers = Seq.fill(31)(RegInit(0.U(64)))
    for lane <- 0 until parameter.issueWidth do
      io.rdata1(lane) := 0.U(64)
      io.rdata2(lane) := 0.U(64)
      for i <- 1 to 31 do
        when(io.raddr1(lane) === i.U(5)) { io.rdata1(lane) := registers(i - 1) }
        when(io.raddr2(lane) === i.U(5)) { io.rdata2(lane) := registers(i - 1) }
        when(io.we(lane) & (io.waddr(lane) === i.U(5))) { registers(i - 1) := io.wdata(lane) }
