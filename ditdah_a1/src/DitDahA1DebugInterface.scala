// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

class DmiRequest extends Bundle:
  val address = Aligned(UInt(7))
  val data = Aligned(UInt(32))
  val op = Aligned(UInt(2))
class DmiResponse extends Bundle:
  val data = Aligned(UInt(32))
  val status = Aligned(UInt(2))
class DmiPort extends Bundle:
  val request = Aligned(new Decoupled(new DmiRequest))
  val response = Flipped(new Decoupled(new DmiResponse))
class JtagPort extends Bundle:
  val tck = Flipped(Clock())
  val trstN = Flipped(Bool())
  val tms = Flipped(Bool())
  val tdi = Flipped(Bool())
  val tdo = Aligned(Bool())
  val tdoEnable = Aligned(Bool())

private[a1] object DebugReset:
  class Signal extends Bundle:
    val value = Aligned(Reset())
  def release(clock: Ref[Clock], reset: Ref[Reset])(using Arena, Context, Block, InstanceContext) =
    given ClockScope = ClockScope.posedge(clock)
    given ResetScope = ResetScope.asyncActiveHigh(reset)
    val meta = RegInit(true.B)
    val held = RegInit(true.B)
    meta := false.B
    held := meta
    val released = Wire(new Signal)
    released.value := held.asReset
    released.value
