// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class FloatingRequest extends Bundle:
  val instruction = Aligned(UInt(32))
  val a = Aligned(UInt(64))
  val b = Aligned(UInt(64))
  val c = Aligned(UInt(64))
  val roundingMode = Aligned(UInt(3))
class FloatingResult extends Bundle:
  val value = Aligned(UInt(64))
  val flags = Aligned(UInt(5))
class DitDahA1FpuIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val input = Flipped(new Decoupled(new FloatingRequest))
  val output = Aligned(new Decoupled(new FloatingResult))
case class DitDahA1FpuParameters(FLEN: Int) extends VerilogParameter

@generator
object DitDahA1Fpu extends VerilogWrapper[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1FpuIO, DitDahA1UnitProbe, DitDahA1FpuParameters]:
  def verilogModuleName(parameter: DitDahA1Parameter) = "DitDahA1Fpu"
  def verilogParameter(parameter: DitDahA1Parameter) = DitDahA1FpuParameters(parameter.floatingPointBits)
