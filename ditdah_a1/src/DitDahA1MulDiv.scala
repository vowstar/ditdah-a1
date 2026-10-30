// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1MulDivIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val input = Flipped(new Decoupled(new IssuedPacket(parameter)))
  val output = Aligned(new Decoupled(UInt(64)))

@generator
object DitDahA1MulDiv extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1MulDivIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1MulDiv"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1MulDivIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val busy = RegInit(false.B)
    val valid = RegInit(false.B)
    val factor = Reg(UInt(128))
    val remaining = Reg(UInt(64))
    val work = Reg(UInt(128))
    val functionCode = Reg(UInt(3))
    val wordOperation = Reg(Bool())
    val negateResult = Reg(Bool())
    io.input.ready := !busy & !valid
    io.output.valid := valid
    val quotient = work.asBits.bits(63, 0).asUInt
    val remainder = work.asBits.bits(127, 64).asUInt
    val divided = functionCode.asBits.bit(1).?(remainder, quotient)
    val corrected = negateResult.?((0.U(64) - divided).asBits.bits(63, 0).asUInt, divided)
    val value = functionCode.asBits.bit(2).?(corrected, (functionCode === 0.U(3)).?(quotient, remainder))
    io.output.bits := wordOperation.?((value.asBits.bit(31).?(BigInt("ffffffff", 16).B(32), 0.B(32)) ## value.asBits.bits(31, 0)).asUInt, value)
    when(io.output.valid & io.output.ready) { valid := false.B }
    when(busy) {
      when(functionCode.asBits.bit(2)) {
        val trial = work.asBits.bits(127, 63).asUInt
        val divisor = (0.B(1) ## factor.asBits.bits(63, 0)).asUInt
        val subtract = trial >= divisor
        val nextRemainder = subtract.?((trial - divisor).asBits.bits(63, 0), trial.asBits.bits(63, 0))
        work := (nextRemainder ## work.asBits.bits(62, 0) ## subtract.asBits).asUInt
      }.otherwise {
        work := (work + remaining.asBits.bit(0).?(factor, 0.U(128))).asBits.bits(127, 0).asUInt
        factor := (factor << 1).asBits.bits(127, 0).asUInt
      }
      remaining := remaining >> 1
      when(remaining <= 1.U(64)) { busy := false.B; valid := true.B }
    }
    when(io.input.valid & io.input.ready) {
      val encoding = io.input.bits.decoded.instruction.instruction.asBits
      val function = encoding.bits(14, 12).asUInt
      val division = function.asBits.bit(2)
      val signed = division & !function.asBits.bit(0)
      val word = encoding.bits(6, 0) === 0x3b.B(7)
      val operands = Seq(io.input.bits.operand1, io.input.bits.operand2).map { value =>
        val extended = ((signed & value.asBits.bit(31)).?(BigInt("ffffffff", 16).B(32), 0.B(32)) ## value.asBits.bits(31, 0)).asUInt
        word.?(extended, value)
      }
      val a = operands(0)
      val b = operands(1)
      val negativeA = signed & a.asBits.bit(63)
      val negativeB = signed & b.asBits.bit(63)
      val absoluteA = negativeA.?((0.U(64) - a).asBits.bits(63, 0).asUInt, a)
      val absoluteB = negativeB.?((0.U(64) - b).asBits.bits(63, 0).asUInt, b)
      val signedA = ((function === 1.U(3)) | (function === 2.U(3))) & a.asBits.bit(63)
      val signedB = (function === 1.U(3)) & b.asBits.bit(63)
      val high = (0.U(64) - signedA.?(b, 0.U(64)) - signedB.?(a, 0.U(64))).asBits.bits(63, 0)
      factor := (0.B(64) ## division.?(absoluteB, a).asBits).asUInt
      remaining := division.?(word.?((BigInt(1) << 31).U(64), (BigInt(1) << 63).U(64)), b)
      work := division.?((0.B(64) ## word.?((absoluteA.asBits.bits(31, 0) ## 0.B(32)).asUInt, absoluteA).asBits).asUInt,
        (high ## 0.B(64)).asUInt)
      functionCode := function
      wordOperation := word
      negateResult := function.asBits.bit(1).?(negativeA, (negativeA ^ negativeB) & (b =/= 0.U(64)))
      busy := true.B
    }
