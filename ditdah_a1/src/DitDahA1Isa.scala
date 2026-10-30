// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

object DitDahA1Isa:
  val mulDivInstructions = Seq("mul", "mulh", "mulhsu", "mulhu", "div", "divu", "rem", "remu",
    "mulw", "divw", "divuw", "remw", "remuw")
  val compressedInstructions = Seq("c.addi4spn", "c.lw", "c.ld", "c.sw", "c.sd", "c.nop", "c.addi", "c.addiw", "c.li", "c.lui", "c.addi16sp",
    "c.srli", "c.srai", "c.andi", "c.sub", "c.xor", "c.or", "c.and", "c.subw", "c.addw", "c.j", "c.beqz", "c.bnez", "c.slli", "c.lwsp", "c.ldsp", "c.jr", "c.mv", "c.ebreak", "c.jalr", "c.add", "c.swsp", "c.sdsp")
  val atomicOperations = Seq(0, 1, 4, 8, 12, 16, 20, 24, 28)
  val atomicInstructions = for size <- Seq("w", "d"); name <- Seq("lr", "sc", "amoadd", "amoswap", "amoxor", "amoor", "amoand", "amomin", "amomax", "amominu", "amomaxu") yield s"$name.$size"
  def instructions(parameter: DitDahA1Parameter) = Seq("lui", "auipc", "addi", "add", "beq", "jal", "jalr",
    "ld", "sd", "csrrw", "csrrs", "ecall", "ebreak", "mret", "fence", "fence.i", "lw", "lwu", "sw",
    "slli", "slti", "sltiu", "xori", "srli", "srai", "ori", "andi", "sub", "sll", "slt", "sltu", "xor", "srl", "sra", "or", "and",
    "addiw", "slliw", "srliw", "sraiw", "addw", "subw", "sllw", "srlw", "sraw", "bne", "blt", "bge", "bltu", "bgeu",
    "lb", "lh", "lbu", "lhu", "sb", "sh", "csrrc", "csrrwi", "csrrsi", "csrrci", "wfi") ++ (if parameter.enableA then atomicInstructions else Seq.empty) ++ (if parameter.enableM then mulDivInstructions else Seq.empty) ++ (if parameter.enableC then compressedInstructions else Seq.empty)
  val supervisorInstructions = Seq("sret")
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
  val MulDiv = 14
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
