// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

object DitDahA1BitManip:
  private def register(name: String, opcode: Int, function: Int, upper: Int) =
    (name, 0xfe00707fL, (upper.toLong << 25) | (function << 12) | opcode)
  private def unary(name: String, opcode: Int, function: Int, immediate: Int) =
    (name, 0xfff0707fL, (immediate.toLong << 20) | (function << 12) | opcode)
  private def shift(name: String, opcode: Int, function: Int, upper: Int) =
    (name, 0xfc00707fL, (upper.toLong << 26) | (function << 12) | opcode)
  val zba = (for uw <- Seq(false, true); amount <- 1 to 3 yield
    register(s"sh${amount}add${if uw then ".uw" else ""}", if uw then 0x3b else 0x33, amount * 2, 0x10)) ++
    Seq(register("add.uw", 0x3b, 0, 4), shift("slli.uw", 0x1b, 1, 2))
  val zbb = Seq(register("andn", 0x33, 7, 0x20), register("orn", 0x33, 6, 0x20), register("xnor", 0x33, 4, 0x20)) ++
    (for w <- Seq(false, true); (name, offset) <- Seq("clz" -> 0, "ctz" -> 1, "cpop" -> 2) yield unary(name + (if w then "w" else ""), if w then 0x1b else 0x13, 1, 0x600 + offset)) ++
    Seq("min", "minu", "max", "maxu").zipWithIndex.map((name, i) => register(name, 0x33, 4 + i, 5)) ++
    Seq(unary("sext.b", 0x13, 1, 0x604), unary("sext.h", 0x13, 1, 0x605), unary("zext.h", 0x3b, 4, 0x080)) ++
    (for w <- Seq(false, true); (name, function) <- Seq("rol" -> 1, "ror" -> 5) yield register(name + (if w then "w" else ""), if w then 0x3b else 0x33, function, 0x30)) ++
    Seq(shift("rori", 0x13, 5, 0x18), register("roriw", 0x1b, 5, 0x30), unary("orc.b", 0x13, 5, 0x287), unary("rev8", 0x13, 5, 0x6b8))
  val zbs = for immediate <- Seq(false, true); (name, upper, function) <- Seq(("bclr", 0x24, 1), ("bext", 0x24, 5), ("binv", 0x34, 1), ("bset", 0x14, 1)) yield
    if immediate then shift(name + "i", 0x13, function, upper / 2) else register(name, 0x33, function, upper)
  def encodings(p: DitDahA1Parameter) =
    (if p.enableZba then zba else Seq.empty) ++ (if p.enableZbb then zbb else Seq.empty) ++ (if p.enableZbs then zbs else Seq.empty) ++
    (if p.enableZicond then Seq(register("czero.eqz", 0x33, 5, 7), register("czero.nez", 0x33, 7, 7)) else Seq.empty)

  def result(p: DitDahA1Parameter, in: Referable[IssuedPacket], default: Referable[UInt])(using Arena, Context, Block, InstanceContext): Referable[UInt] =
    val value = Wire(UInt(64))
    value := default
    val raw = in.decoded.instruction.instruction
    val instruction = if p.enableC then (in.decoded.instruction.length === 2.U(3)).?(DitDahA1Compressed(raw, p), raw.asBits) else raw.asBits
    val a = in.operand1.asBits
    val b = in.operand2.asBits
    def extend(x: Referable[Bits], sign: Boolean = false)(using Block) =
      ((if sign then x.bit(x.width - 1).?(((BigInt(1) << (64 - x.width)) - 1).B(64 - x.width), 0.B(64 - x.width)) else 0.B(64 - x.width)) ## x).asUInt
    val immediate = (instruction.bits(6, 0) === 0x13.B(7)) | (instruction.bits(6, 0) === 0x1b.B(7))
    val amount = immediate.?(instruction.bits(25, 20), b.bits(5, 0)).asUInt
    val narrow = extend(a.bits(31, 0))
    val counts = if p.enableZbb then (for width <- Seq(32, 64) yield
      val leading = Wire(UInt(7)); leading := width.U(7)
      val trailing = Wire(UInt(7)); trailing := width.U(7)
      for i <- 0 until width do when(a.bit(i)) { leading := (width - i - 1).U(7) }
      for i <- (0 until width).reverse do when(a.bit(i)) { trailing := i.U(7) }
      def sum(xs: Seq[Referable[UInt]]): Referable[UInt] =
        if xs.size == 1 then xs.head else sum(xs.take(xs.size / 2)) + sum(xs.drop(xs.size / 2))
      val population = sum((0 until width).map(i => a.bit(i).?(1.U(7), 0.U(7))))
      width -> Seq(leading, trailing, population)).toMap else Map.empty[Int, Seq[Referable[UInt]]]
    for (name, mask, encoding) <- encodings(p) do
      when(((in.decoded.operation === DitDahA1Isa.AluImmediate.U(5)) | (in.decoded.operation === DitDahA1Isa.AluRegister.U(5))) &
        ((instruction & BigInt(mask).B(32)) === BigInt(encoding).B(32))) {
        val result: Referable[UInt] = name match
          case "czero.eqz" => (b =/= 0.B(64)).?(a, 0.B(64)).asUInt
          case "czero.nez" => (b === 0.B(64)).?(a, 0.B(64)).asUInt
          case "add.uw" => (narrow + b.asUInt).asBits.bits(63, 0).asUInt
          case "slli.uw" => (narrow << amount).asBits.bits(63, 0).asUInt
          case n if n.startsWith("sh") =>
            val left = if n.endsWith(".uw") then narrow else a.asUInt
            ((left << n.charAt(2).asDigit) + b.asUInt).asBits.bits(63, 0).asUInt
          case "andn" => (a & ~b).asUInt
          case "orn" => (a | ~b).asUInt
          case "xnor" => (~(a ^ b)).asUInt
          case n if n.startsWith("clz") || n.startsWith("ctz") || n.startsWith("cpop") => counts(if n.endsWith("w") then 32 else 64)(if n.startsWith("clz") then 0 else if n.startsWith("ctz") then 1 else 2)
          case "min" | "minu" | "max" | "maxu" =>
            val less = if name.endsWith("u") then a.asUInt < b.asUInt else a.asSInt < b.asSInt
            (if name.startsWith("min") then less else !less).?(a, b).asUInt
          case "sext.b" => extend(a.bits(7, 0), true)
          case "sext.h" => extend(a.bits(15, 0), true)
          case "zext.h" => extend(a.bits(15, 0))
          case "orc.b" => (0 until 8).reverse.map(i => (a.bits(i * 8 + 7, i * 8) =/= 0.B(8)).?(255.B(8), 0.B(8))).reduce(_ ## _).asUInt
          case "rev8" => (0 until 8).map(i => a.bits(i * 8 + 7, i * 8)).reduce(_ ## _).asUInt
          case n if n.startsWith("ro") =>
            val width = if n.endsWith("w") then 32 else 64
            val source = a.bits(width - 1, 0).asUInt
            val shift = if width == 32 then amount.asBits.bits(4, 0).asUInt else amount
            val complement = (0.U(shift.width) - shift).asBits.bits(shift.width - 1, 0).asUInt
            val rotate = if n.startsWith("rol") then ((source << shift).asBits.bits(width - 1, 0) | (source >> complement).asBits) else ((source >> shift).asBits | (source << complement).asBits.bits(width - 1, 0))
            if width == 32 then extend(rotate, true) else rotate.asUInt
          case n =>
            val bit = (1.U(64) << amount).asBits.bits(63, 0)
            if n.startsWith("bclr") then (a & ~bit).asUInt else if n.startsWith("binv") then (a ^ bit).asUInt else if n.startsWith("bset") then (a | bit).asUInt else ((a.asUInt >> amount).asBits & 1.B(64)).asUInt
        value := result
      }
    value
