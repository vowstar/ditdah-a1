// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

object DitDahA1RegisterFile:
  def apply(width: Int, zero: Boolean, addresses: Seq[Referable[UInt]],
      writes: Seq[(Referable[Bool], Referable[UInt], Referable[UInt])])(
      using Arena, Context, Block, InstanceContext, ClockScope, ResetScope): Seq[Referable[UInt]] =
    val registers = Seq.fill(if zero then 31 else 32)(if zero then RegInit(0.U(width)) else Reg(UInt(width)))
    val outputs = addresses.map { address =>
      val value = Wire(UInt(width))
      value := 0.U(width)
      for i <- registers.indices do when(address === (i + (if zero then 1 else 0)).U(5)) { value := registers(i) }
      value
    }
    for (enable, address, data) <- writes; i <- registers.indices do
      when(enable & (address === (i + (if zero then 1 else 0)).U(5))) { registers(i) := data.asBits.bits(width - 1, 0).asUInt }
    outputs

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
    val values = DitDahA1RegisterFile(64, true,
      (0 until parameter.issueWidth).flatMap(n => Seq(io.raddr1(n), io.raddr2(n))),
      (0 until parameter.issueWidth).map(n => (io.we(n), io.waddr(n), io.wdata(n))))
    for lane <- 0 until parameter.issueWidth do
      io.rdata1(lane) := values(2 * lane)
      io.rdata2(lane) := values(2 * lane + 1)
