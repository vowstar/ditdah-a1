// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1IssueIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val input = Flipped(new Decoupled(new DecodedPacket(parameter)))
  val output = Aligned(new Decoupled(new IssuedPacket(parameter)))
  val raddr1 = Aligned(UInt(5))
  val raddr2 = Aligned(UInt(5))
  val rdata1 = Flipped(UInt(64))
  val rdata2 = Flipped(UInt(64))

@generator
object DitDahA1Issue extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1IssueIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Issue"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1IssueIO]]
    io.input.ready := io.output.ready
    io.output.valid := io.input.valid
    io.raddr1 := io.input.bits.usesRs1.?(io.input.bits.rs1, 0.U(5))
    io.raddr2 := io.input.bits.usesRs2.?(io.input.bits.rs2, 0.U(5))
    io.output.bits.decoded :<= io.input.bits
    io.output.bits.operand1 := io.rdata1
    io.output.bits.operand2 := io.rdata2
