// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1CsrIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val interrupts = Option.when(parameter.enableInterrupts)(Flipped(new InterruptBundle))
  val interruptPending = Option.when(parameter.enableInterrupts)(Aligned(Bool()))
  val interruptCause = Option.when(parameter.enableInterrupts)(Aligned(UInt(64)))
  val pmp = Option.when(parameter.pmpEntries != 0)(Aligned(new PmpState(parameter)))
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
    parameter.validateProtection()
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
    if parameter.enableInterrupts then
      val enables = RegInit(0.U(3))
      val inputs = io.interrupts.get
      val levels = inputs.external.asBits ## inputs.timer.asBits ## inputs.software.asBits
      val pending = enables.asBits & levels
      io.interruptPending.get := status.asBits.bit(3) & (pending =/= 0.B(3))
      io.interruptCause.get := pending.bit(2).?(BigInt("800000000000000b", 16).U(64),
        pending.bit(0).?(BigInt("8000000000000003", 16).U(64), BigInt("8000000000000007", 16).U(64)))
      Seq((0x304, enables.asBits), (0x344, levels)).foreach { case (address, bits) =>
        when(io.readAddress === address.U(12)) {
          io.readData := (0.B(52) ## bits.bits(2, 2) ## 0.B(3) ## bits.bits(1, 1) ##
            0.B(3) ## bits.bits(0, 0) ## 0.B(3)).asUInt
        }
      }
      when(io.write & (io.writeAddress === 0x304.U(12))) {
        val bits = io.writeData.asBits
        enables := (bits.bits(11, 11) ## bits.bits(7, 7) ## bits.bits(3, 3)).asUInt
      }
    if parameter.pmpEntries != 0 then
      val width = parameter.physicalAddressBits - 2
      val config = Seq.fill(parameter.pmpEntries)(RegInit(0.U(6)))
      val address = Seq.fill(parameter.pmpEntries)(RegInit(0.U(width)))
      val encoded = config.map(value => (value.asBits.bits(5, 5) ## 0.B(2) ## value.asBits.bits(4, 0)).asUInt)
      io.pmp.get.config := encoded.reverse.map(_.asBits).reduce(_ ## _).asUInt
      io.pmp.get.address := address.reverse.map(_.asBits).reduce(_ ## _).asUInt
      for csr <- (0 until 16 by 2).map(0x3a0 + _) ++ (0 until 64).map(0x3b0 + _) do
        when(io.readAddress === csr.U(12)) { io.legal := true.B }
      for index <- config.indices do
        val slot = index % 8
        val csr = 0x3a0 + (index / 8) * 2
        val locked = config(index).asBits.bit(5)
        val predecessorLocked = if index + 1 == config.size then false.B else
          config(index + 1).asBits.bit(5) & (config(index + 1).asBits.bits(4, 3) === 1.B(2))
        if slot == 0 then
          when(io.readAddress === csr.U(12)) {
            io.readData := encoded.slice(index, index + 8).reverse.map(_.asBits).reduce(_ ## _).asUInt
          }
        when(io.readAddress === (0x3b0 + index).U(12)) { io.readData := address(index) }
        when(io.write & (io.writeAddress === csr.U(12)) & !locked) {
          val value = io.writeData.asBits.bits(slot * 8 + 7, slot * 8)
          config(index) := (value.bits(7, 7) ## (value.bits(4, 0) & value.bit(0).?(31.B(5), 29.B(5)))).asUInt
        }
        when(io.write & (io.writeAddress === (0x3b0 + index).U(12)) & !locked & !predecessorLocked) {
          address(index) := io.writeData.asBits.bits(width - 1, 0).asUInt
        }
