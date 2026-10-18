// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

object DitDahA1Isa:
  val instructions = Seq("lui", "auipc", "addi", "add", "beq", "jal", "jalr",
    "ld", "sd", "csrrw", "csrrs", "ecall", "mret", "mul", "amoadd.d", "fence", "fence.i")
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
  val operationBits = 5
