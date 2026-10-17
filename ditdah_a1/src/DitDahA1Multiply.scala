// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1MultiplyIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val input = Flipped(new Decoupled(new IssuedPacket))
  val output = Aligned(new Decoupled(UInt(64)))

@generator
object DitDahA1Multiply extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1MultiplyIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Multiply"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1MultiplyIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val busy = RegInit(false.B)
    val valid = RegInit(false.B)
    val multiplicand = Reg(UInt(64))
    val multiplier = Reg(UInt(64))
    val product = Reg(UInt(64))
    io.input.ready := !busy & !valid
    io.output.valid := valid
    io.output.bits := product
    when(io.output.valid & io.output.ready) { valid := false.B }
    when(busy) {
      product := (product + multiplier.asBits.bit(0).?(multiplicand, 0.U(64))).asBits.bits(63, 0).asUInt
      multiplicand := (multiplicand << 1).asBits.bits(63, 0).asUInt
      multiplier := multiplier >> 1
      when(multiplier <= 1.U(64)) { busy := false.B; valid := true.B }
    }
    when(io.input.valid & io.input.ready) {
      multiplicand := io.input.bits.operand1
      multiplier := io.input.bits.operand2
      product := 0.U(64)
      busy := true.B
    }
