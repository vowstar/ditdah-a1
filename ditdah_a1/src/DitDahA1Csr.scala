// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1CsrIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val readAddress = Flipped(UInt(12))
  val readData = Aligned(UInt(64))
  val legal = Aligned(Bool())
  val write = Flipped(Bool())
  val writeAddress = Flipped(UInt(12))
  val writeData = Flipped(UInt(64))
  val trap = Flipped(Bool())
  val trapPc = Flipped(UInt(64))
  val trapCause = Flipped(UInt(64))
  val trapValue = Flipped(UInt(64))
  val mret = Flipped(Bool())
  val trapVector = Aligned(UInt(64))
  val returnPc = Aligned(UInt(64))

@generator
object DitDahA1Csr extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1CsrIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Csr"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1CsrIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val status = RegInit(0.U(64))
    val mtvec = RegInit(0.U(64))
    val mscratch = RegInit(0.U(64))
    val mepc = RegInit(0.U(64))
    val mcause = RegInit(0.U(64))
    val mtval = RegInit(0.U(64))
    io.trapVector := mtvec
    io.returnPc := mepc
    io.readData := 0.U(64)
    io.legal := false.B
    Seq(0x301, 0x304, 0x344, 0xf11, 0xf12, 0xf13, 0xf14).foreach { address =>
      when(io.readAddress === address.U(12)) { io.legal := true.B }
    }
    Seq((0x305, mtvec), (0x340, mscratch), (0x341, mepc), (0x342, mcause), (0x343, mtval)).foreach { case (address, register) =>
      when(io.readAddress === address.U(12)) { io.readData := register; io.legal := true.B }
      when(io.write & (io.writeAddress === address.U(12))) {
        if address == 0x305 || address == 0x341 then
          register := (io.writeData.asBits.bits(63, 2) ## 0.B(2)).asUInt
        else register := io.writeData
      }
    }
    when(io.readAddress === 0x300.U(12)) { io.readData := (status.asBits | 0x1800.B(64)).asUInt; io.legal := true.B }
    when(io.write & (io.writeAddress === 0x300.U(12))) { status := (io.writeData.asBits & 0x88.B(64)).asUInt }
    when(io.mret) { status := status.asBits.bit(7).?(0x88.U(64), 0x80.U(64)) }
    when(io.trap) {
      mepc := (io.trapPc.asBits.bits(63, 2) ## 0.B(2)).asUInt
      mcause := io.trapCause
      mtval := io.trapValue
      status := status.asBits.bit(3).?(0x80.U(64), 0.U(64))
    }
