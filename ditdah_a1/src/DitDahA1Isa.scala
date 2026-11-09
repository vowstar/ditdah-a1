// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

object DitDahA1Isa:
  val mulDivInstructions = Seq("mul", "mulh", "mulhsu", "mulhu", "div", "divu", "rem", "remu",
    "mulw", "divw", "divuw", "remw", "remuw")
  val compressedInstructions = Seq("c.addi4spn", "c.lw", "c.ld", "c.sw", "c.sd", "c.nop", "c.addi", "c.addiw", "c.li", "c.lui", "c.addi16sp",
    "c.srli", "c.srai", "c.andi", "c.sub", "c.xor", "c.or", "c.and", "c.subw", "c.addw", "c.j", "c.beqz", "c.bnez", "c.slli", "c.lwsp", "c.ldsp", "c.jr", "c.mv", "c.ebreak", "c.jalr", "c.add", "c.swsp", "c.sdsp")
  def floatingInstructions(bits: Int) = (if bits == 0 then Seq.empty else (if bits == 64 then Seq("s", "d") else Seq("s")).flatMap { format =>
    Seq("fmadd", "fmsub", "fnmsub", "fnmadd", "fadd", "fsub", "fmul", "fdiv", "fsqrt", "fsgnj", "fsgnjn", "fsgnjx", "fmin", "fmax", "feq", "flt", "fle", "fclass").map(_ + "." + format) ++
      Seq("w", "wu", "l", "lu").flatMap(integer => Seq(s"fcvt.$integer.$format", s"fcvt.$format.$integer")) ++
      (if format == "s" then Seq("flw", "fsw", "fmv.x.w", "fmv.w.x") else Seq("fld", "fsd", "fmv.x.d", "fmv.d.x", "fcvt.s.d", "fcvt.d.s"))
  })
  def additionalInstructions(p: DitDahA1Parameter) = Seq("pause", "ntl.p1", "ntl.pall", "ntl.s1", "ntl.all", "prefetch.i", "prefetch.r", "prefetch.w") ++
    (if p.enableZicboz then Seq("cbo.zero") else Seq.empty) ++
    (if p.enableZicbom then Seq("cbo.clean", "cbo.inval", "cbo.flush") else Seq.empty) ++
    (if p.enableZawrs then Seq("wrs.nto", "wrs.sto") else Seq.empty) ++
    (if p.enableC then Seq("c.ntl.p1", "c.ntl.pall", "c.ntl.s1", "c.ntl.all") else Seq.empty) ++
    (if p.enableZimop then (0 until 32).map(n => s"mop.r.$n") ++ (0 until 8).map(n => s"mop.rr.$n") else Seq.empty) ++
    (if p.enableZcmop then (1 to 15 by 2).map(n => s"c.mop.$n") else Seq.empty) ++
    (if p.enableZcb then Seq("c.lbu", "c.lh", "c.lhu", "c.sb", "c.sh", "c.zext.b", "c.not") ++
      (if p.enableM then Seq("c.mul") else Seq.empty) ++ (if p.enableZbb then Seq("c.sext.b", "c.sext.h", "c.zext.h") else Seq.empty) ++
      (if p.enableZba then Seq("c.zext.w") else Seq.empty) else Seq.empty) ++
    (if p.enableZfa then (if p.floatingPointBits == 64 then Seq("s", "d") else Seq("s")).flatMap(f =>
      Seq("fli", "fminm", "fmaxm", "fround", "froundnx", "fleq", "fltq").map(_ + "." + f)) ++
      (if p.floatingPointBits == 64 then Seq("fcvtmod.w.d") else Seq.empty) else Seq.empty) ++
    (if p.enableZfhmin then Seq("flh", "fsh", "fmv.x.h", "fmv.h.x", "fcvt.s.h", "fcvt.h.s") ++
      (if p.floatingPointBits == 64 then Seq("fcvt.d.h", "fcvt.h.d") else Seq.empty) else Seq.empty)
  val atomicOperations = Seq(0, 1, 4, 8, 12, 16, 20, 24, 28)
  val atomicInstructions = for size <- Seq("w", "d"); name <- Seq("lr", "sc", "amoadd", "amoswap", "amoxor", "amoor", "amoand", "amomin", "amomax", "amominu", "amomaxu") yield s"$name.$size"
  def instructions(parameter: DitDahA1Parameter) = Seq("lui", "auipc", "addi", "add", "beq", "jal", "jalr",
    "ld", "sd", "csrrw", "csrrs", "ecall", "ebreak", "mret", "fence", "fence.i", "lw", "lwu", "sw",
    "slli", "slti", "sltiu", "xori", "srli", "srai", "ori", "andi", "sub", "sll", "slt", "sltu", "xor", "srl", "sra", "or", "and",
    "addiw", "slliw", "srliw", "sraiw", "addw", "subw", "sllw", "srlw", "sraw", "bne", "blt", "bge", "bltu", "bgeu",
    "lb", "lh", "lbu", "lhu", "sb", "sh", "csrrc", "csrrwi", "csrrsi", "csrrci", "wfi") ++ (if parameter.enableA then atomicInstructions else Seq.empty) ++ (if parameter.enableM then mulDivInstructions else Seq.empty) ++ (if parameter.enableC then compressedInstructions else Seq.empty) ++ DitDahA1BitManip.encodings(parameter).map(_._1) ++ floatingInstructions(parameter.floatingPointBits) ++ additionalInstructions(parameter) ++ (if parameter.enableC && parameter.floatingPointBits == 64 then Seq("c.fld", "c.fsd", "c.fldsp", "c.fsdsp") else Seq.empty)
  val supervisorInstructions = Seq("sret")
  val debugInstructions = Seq("dret")
  val Illegal = 0
  val Lui = 1
  val Auipc = 2
  val Addi = 3
  val Add = 4
  val Beq = 5
  val Jal = 6
  val Jalr = 7
  val Ld = 8
  val Sd = 9
  val Csrrw = 10
  val Csrrs = 11
  val Ecall = 12
  val Mret = 13
  val Arithmetic = 14
  val AmoaddD = 15
  val Fence = 16
  val FenceI = 17
  val Lw = 18
  val Lwu = 19
  val Sw = 20
  val AluImmediate = 21
  val AluRegister = 22
  val AluWordImmediate = 23
  val AluWordRegister = 24
  val Branch = 25
  val Load = 26
  val Store = 27
  val Csr = 28
  val Wfi = 29
  val Atomic = 30
  val Sret = 31
  val operationBits = 5
