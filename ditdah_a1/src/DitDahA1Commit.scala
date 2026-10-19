// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1CommitIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val input = Flipped(new Decoupled(new ResultPacket))
  val output = Aligned(new Decoupled(new ResultPacket))
  val trapVector = Flipped(UInt(64))
  val returnPc = Flipped(UInt(64))

@generator
object DitDahA1Commit extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1CommitIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Commit"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1CommitIO]]
    io.input.ready := io.output.ready
    io.output.valid := io.input.valid
    io.output.bits :<= io.input.bits
    val out = io.output.bits
    when(io.input.bits.mret | io.input.bits.sret) { out.nextPc := io.returnPc }
    when(io.input.bits.instruction.fault) {
      out.nextPc := io.trapVector
      out.rdWrite := false.B
      out.csrWrite := false.B
      out.mret := false.B
      out.sret := false.B
      out.fenceI := false.B
      out.sfenceVma := false.B
      out.wfi := false.B
    }
    when(io.input.bits.rd === 0.U(5)) { out.rdWrite := false.B }
