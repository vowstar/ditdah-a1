// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

object DitDahA1Isa:
  val instructions = Seq("lui", "auipc", "addi", "add", "beq", "jal", "jalr",
    "ld", "sd", "csrrw", "csrrs", "ecall", "mret", "mul", "amoadd.d", "fence", "fence.i", "lw", "lwu", "sw",
    "slli", "slti", "sltiu", "xori", "srli", "srai", "ori", "andi", "sub", "sll", "slt", "sltu", "xor", "srl", "sra", "or", "and",
    "addiw", "slliw", "srliw", "sraiw", "addw", "subw", "sllw", "srlw", "sraw", "bne", "blt", "bge", "bltu", "bgeu",
    "lb", "lh", "lbu", "lhu", "sb", "sh", "csrrc", "csrrwi", "csrrsi", "csrrci", "wfi",
    "amoor.d", "amoswap.d", "lr.d", "sc.d")
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
  val Mul = 14
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
