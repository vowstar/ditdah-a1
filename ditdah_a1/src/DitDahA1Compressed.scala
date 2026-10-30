// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

object DitDahA1Compressed:
  def apply(raw: Referable[UInt])(using Arena, Context, Block, InstanceContext): Referable[Bits] =
    val c = raw.asBits
    val rd = c.bits(11, 7)
    val rs2 = c.bits(6, 2)
    val compact = 1.B(2) ## c.bits(9, 7)
    val target = 1.B(2) ## c.bits(4, 2)
    val immediate = c.bit(12).?(63.B(6), 0.B(6)) ## c.bits(12, 12) ## c.bits(6, 2)
    val shift = 0.B(6) ## c.bits(12, 12) ## c.bits(6, 2)
    def i(d: Referable[Bits], a: Referable[Bits], imm: Referable[Bits], f: Int = 0, word: Boolean = false)(using Block) =
      imm ## a ## f.B(3) ## d ## (if word then 0x1b else 0x13).B(7)
    def r(d: Referable[Bits], a: Referable[Bits], b: Referable[Bits], f: Referable[Bits], upper: Int = 0, word: Boolean = false)(using Block) =
      upper.B(7) ## b ## a ## f ## d ## (if word then 0x3b else 0x33).B(7)
    def load(d: Referable[Bits], a: Referable[Bits], imm: Referable[Bits], f: Int)(using Block) =
      imm ## a ## f.B(3) ## d ## 0x03.B(7)
    def store(a: Referable[Bits], b: Referable[Bits], imm: Referable[Bits], f: Int)(using Block) =
      imm.bits(11, 5) ## b ## a ## f.B(3) ## imm.bits(4, 0) ## 0x23.B(7)
    val out = Wire(Bits(32))
    out := 0.B(32)
    when(c.bits(1, 0) === 0.B(2)) {
      val spOffset = 0.B(2) ## c.bits(10, 7) ## c.bits(12, 11) ## c.bits(5, 5) ## c.bits(6, 6) ## 0.B(2)
      when((c.bits(15, 13) === 0.B(3)) & (spOffset =/= 0.B(12))) { out := i(target, 2.B(5), spOffset) }
      for (f, size) <- Seq(2 -> 2, 3 -> 3) do
        val offset = if size == 2 then 0.B(5) ## c.bits(5, 5) ## c.bits(12, 10) ## c.bits(6, 6) ## 0.B(2)
          else 0.B(4) ## c.bits(6, 5) ## c.bits(12, 10) ## 0.B(3)
        when(c.bits(15, 13) === f.B(3)) { out := load(target, compact, offset, size) }
        when(c.bits(15, 13) === (f + 4).B(3)) { out := store(compact, target, offset, size) }
    }
    when(c.bits(1, 0) === 1.B(2)) {
      when(c.bits(15, 13) === 0.B(3)) { out := i(rd, rd, immediate) }
      when((c.bits(15, 13) === 1.B(3)) & (rd =/= 0.B(5))) { out := i(rd, rd, immediate, word = true) }
      when(c.bits(15, 13) === 2.B(3)) { out := i(rd, 0.B(5), immediate) }
      when((c.bits(15, 13) === 3.B(3)) & (immediate =/= 0.B(12))) {
        out := (c.bit(12).?(((BigInt(1) << 15) - 1).B(15), 0.B(15)) ## c.bits(6, 2) ## rd ## 0x37.B(7))
        when(rd === 2.B(5)) {
          val offset = c.bit(12).?(7.B(3), 0.B(3)) ## c.bits(4, 3) ## c.bits(5, 5) ## c.bits(2, 2) ## c.bits(6, 6) ## 0.B(4)
          out := i(rd, rd, offset)
        }
      }
      when(c.bits(15, 13) === 4.B(3)) {
        when(c.bits(11, 10) === 0.B(2)) { out := i(compact, compact, shift, 5) }
        when(c.bits(11, 10) === 1.B(2)) { out := i(compact, compact, 0x10.B(6) ## shift.bits(5, 0), 5) }
        when(c.bits(11, 10) === 2.B(2)) { out := i(compact, compact, immediate, 7) }
        when(c.bits(11, 10) === 3.B(2)) {
          val function = Wire(Bits(3))
          function := 0.B(3)
          when(c.bits(6, 5) === 1.B(2)) { function := 4.B(3) }
          when(c.bits(6, 5) === 2.B(2)) { function := 6.B(3) }
          when(c.bits(6, 5) === 3.B(2)) { function := 7.B(3) }
          when(!c.bit(12)) {
            out := r(compact, compact, target, function)
            when(c.bits(6, 5) === 0.B(2)) { out := r(compact, compact, target, function, 32) }
          }
          when(c.bit(12) & !c.bit(6)) {
            out := r(compact, compact, target, 0.B(3), word = true)
            when(!c.bit(5)) { out := r(compact, compact, target, 0.B(3), 32, word = true) }
          }
        }
      }
      when(c.bits(15, 13) === 5.B(3)) {
        val offset = c.bits(12, 12) ## c.bits(8, 8) ## c.bits(10, 9) ## c.bits(6, 6) ## c.bits(7, 7) ## c.bits(2, 2) ## c.bits(11, 11) ## c.bits(5, 3) ## 0.B(1)
        val full = c.bit(12).?(511.B(9), 0.B(9)) ## offset
        out := full.bits(20, 20) ## full.bits(10, 1) ## full.bits(11, 11) ## full.bits(19, 12) ## 0.B(5) ## 0x6f.B(7)
      }
      when((c.bits(15, 13) === 6.B(3)) | (c.bits(15, 13) === 7.B(3))) {
        val offset = c.bit(12).?(31.B(5), 0.B(5)) ## c.bits(6, 5) ## c.bits(2, 2) ## c.bits(11, 10) ## c.bits(4, 3) ## 0.B(1)
        out := offset.bits(12, 12) ## offset.bits(10, 5) ## 0.B(5) ## compact ## (0.B(2) ## c.bits(13, 13)) ## offset.bits(4, 1) ## offset.bits(11, 11) ## 0x63.B(7)
      }
    }
    when(c.bits(1, 0) === 2.B(2)) {
      when(c.bits(15, 13) === 0.B(3)) { out := i(rd, rd, shift, 1) }
      for (f, size) <- Seq(2 -> 2, 3 -> 3) do
        val offset = if size == 2 then 0.B(4) ## c.bits(3, 2) ## c.bits(12, 12) ## c.bits(6, 4) ## 0.B(2)
          else 0.B(3) ## c.bits(4, 2) ## c.bits(12, 12) ## c.bits(6, 5) ## 0.B(3)
        when((c.bits(15, 13) === f.B(3)) & (rd =/= 0.B(5))) { out := load(rd, 2.B(5), offset, size) }
        val storeOffset = if size == 2 then 0.B(4) ## c.bits(8, 7) ## c.bits(12, 9) ## 0.B(2)
          else 0.B(3) ## c.bits(9, 7) ## c.bits(12, 10) ## 0.B(3)
        when(c.bits(15, 13) === (f + 4).B(3)) { out := store(2.B(5), rs2, storeOffset, size) }
      when(c.bits(15, 13) === 4.B(3)) {
        when(rs2 =/= 0.B(5)) { out := r(rd, c.bit(12).?(rd, 0.B(5)), rs2, 0.B(3)) }
        when((rs2 === 0.B(5)) & (rd =/= 0.B(5))) { out := 0.B(12) ## rd ## 0.B(3) ## (0.B(4) ## c.bits(12, 12)) ## 0x67.B(7) }
        when(c.bit(12) & (rs2 === 0.B(5)) & (rd === 0.B(5))) { out := 0x00100073.B(32) }
      }
    }
    out
