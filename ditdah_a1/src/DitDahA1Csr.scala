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
  val wakeup = Option.when(parameter.enableInterrupts)(Aligned(Bool()))
  val interruptCause = Option.when(parameter.enableInterrupts)(Aligned(UInt(64)))
  val pmp = Option.when(parameter.pmpEntries != 0)(Aligned(new PmpState(parameter)))
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val hartId = Flipped(UInt(4))
  val readAddress = Flipped(UInt(12))
  val readData = Aligned(UInt(64))
  val legal = Aligned(Bool())
  val privilege = Aligned(UInt(2))
  val dataPrivilege = Aligned(UInt(2))
  val translationState = Option.when(parameter.enableTranslation)(Aligned(new TranslationState))
  val sfenceLegal = Aligned(Bool())
  val wfiLegal = Aligned(Bool())
  val write = Flipped(Bool())
  val writeAddress = Flipped(UInt(12))
  val writeData = Flipped(UInt(64))
  val trap = Flipped(Bool())
  val trapPc = Flipped(UInt(64))
  val trapCause = Flipped(UInt(64))
  val trapValue = Flipped(UInt(64))
  val mret = Flipped(Bool())
  val sret = Flipped(Bool())
  val sretLegal = Aligned(Bool())
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
    val satp = Option.when(parameter.enableTranslation)(RegInit(0.U(64)))
    if parameter.enableTranslation then
      io.translationState.get.satp := satp.get
      io.translationState.get.sum := status.asBits.bit(18)
      io.translationState.get.mxr := status.asBits.bit(19)
    val mode = Option.when(parameter.enableSupervisorMode)(RegInit(3.U(2)))
    val user = Option.when(parameter.enableUserMode && !parameter.enableSupervisorMode)(RegInit(false.B))
    val privilege = mode.getOrElse(user.map(_.?(0.U(2), 3.U(2))).getOrElse(3.U(2)))
    io.privilege := privilege
    io.dataPrivilege := (if parameter.enableUserMode then
      ((privilege === 3.U(2)) & status.asBits.bit(17)).?(status.asBits.bits(12, 11).asUInt, privilege)
    else 3.U(2))
    io.wfiLegal := (if parameter.enableSupervisorMode then
      (privilege === 3.U(2)) | ((privilege === 1.U(2)) & !status.asBits.bit(21))
    else if parameter.enableUserMode then (privilege === 3.U(2)) | !status.asBits.bit(21) else true.B)
    io.sretLegal := (if parameter.enableSupervisorMode then
      (privilege === 3.U(2)) | ((privilege === 1.U(2)) & !status.asBits.bit(22)) else false.B)
    io.sfenceLegal := (if parameter.enableTranslation then
      (privilege === 3.U(2)) | ((privilege === 1.U(2)) & !status.asBits.bit(20)) else false.B)
    val mtvec = RegInit(0.U(64))
    val mscratch = RegInit(0.U(64))
    val mepc = RegInit(0.U(64))
    val mcause = RegInit(0.U(64))
    val mtval = RegInit(0.U(64))
    val medeleg = Option.when(parameter.enableSupervisorMode)(RegInit(0.U(64)))
    val mideleg = Option.when(parameter.enableSupervisorMode)(RegInit(0.U(64)))
    val stvec = Option.when(parameter.enableSupervisorMode)(RegInit(0.U(64)))
    val sscratch = Option.when(parameter.enableSupervisorMode)(RegInit(0.U(64)))
    val sepc = Option.when(parameter.enableSupervisorMode)(RegInit(0.U(64)))
    val scause = Option.when(parameter.enableSupervisorMode)(RegInit(0.U(64)))
    val stval = Option.when(parameter.enableSupervisorMode)(RegInit(0.U(64)))
    val supervisorTrap = if parameter.enableSupervisorMode then
      val delegation = io.trapCause.asBits.bit(63).?(mideleg.get, medeleg.get)
      (privilege =/= 3.U(2)) & (io.trapCause.asBits.bits(62, 6) === 0.B(57)) &
        (delegation >> io.trapCause.asBits.bits(5, 0).asUInt).asBits.bit(0)
    else false.B
    io.trapVector := (if parameter.enableSupervisorMode then supervisorTrap.?(stvec.get, mtvec) else mtvec)
    io.returnPc := (if parameter.enableSupervisorMode then io.sret.?(sepc.get, mepc) else mepc)
    io.readData := 0.U(64)
    io.legal := false.B
    Seq(0x301, 0x304, 0x344, 0xf11, 0xf12, 0xf13, 0xf14, 0xf15).foreach { address =>
      when(io.readAddress === address.U(12)) { io.legal := true.B }
    }
    when(io.readAddress === 0xf14.U(12)) { io.readData := io.hartId }
    val machineRegisters = Seq((0x305, mtvec), (0x340, mscratch), (0x341, mepc), (0x342, mcause), (0x343, mtval))
    val supervisorRegisters = if parameter.enableSupervisorMode then
      Seq((0x105, stvec.get), (0x140, sscratch.get), (0x141, sepc.get), (0x142, scause.get), (0x143, stval.get))
    else Seq.empty
    (machineRegisters ++ supervisorRegisters).foreach { case (address, register) =>
      when(io.readAddress === address.U(12)) { io.readData := register; io.legal := true.B }
      when(io.write & (io.writeAddress === address.U(12))) {
        if Set(0x105, 0x141, 0x305, 0x341).contains(address) then
          register := (io.writeData.asBits.bits(63, 2) ## 0.B(2)).asUInt
        else register := io.writeData
      }
    }
    val fixedStatus = if parameter.enableSupervisorMode then BigInt("a00000000", 16)
      else if parameter.enableUserMode then BigInt("200000000", 16) else BigInt(0x1800)
    when(io.readAddress === 0x300.U(12)) { io.readData := (status.asBits | fixedStatus.B(64)).asUInt; io.legal := true.B }
    when(io.write & (io.writeAddress === 0x300.U(12))) {
      if parameter.enableUserMode then
        val mpp = io.writeData.asBits.bits(12, 11)
        val savedPrivilege = (mpp === 3.B(2)).?(0x1800.B(64),
          (parameter.enableSupervisorMode.B & (mpp === 1.B(2))).?(0x800.B(64), 0.B(64)))
        val mask = if parameter.enableTranslation then 0x7e01aa else if parameter.enableSupervisorMode then 0x7201aa else 0x220088
        status := ((io.writeData.asBits & mask.B(64)) | savedPrivilege).asUInt
      else status := (io.writeData.asBits & 0x88.B(64)).asUInt
    }
    if parameter.enableSupervisorMode then
      val supervisorMask = if parameter.enableTranslation then 0xc0122 else 0x122
      when(io.readAddress === 0x100.U(12)) {
        io.readData := ((status.asBits & supervisorMask.B(64)) | BigInt("200000000", 16).B(64)).asUInt
        io.legal := true.B
      }
      when(io.write & (io.writeAddress === 0x100.U(12))) {
        status := ((status.asBits & (BigInt("ffffffffffffffff", 16) ^ supervisorMask).B(64)) | (io.writeData.asBits & supervisorMask.B(64))).asUInt
      }
      Seq((0x302, medeleg.get, if parameter.enableTranslation then 0xb3ff else 0x3ff), (0x303, mideleg.get, 0x222)).foreach { case (address, register, mask) =>
        when(io.readAddress === address.U(12)) { io.readData := register; io.legal := true.B }
        when(io.write & (io.writeAddress === address.U(12))) { register := (io.writeData.asBits & mask.B(64)).asUInt }
      }
      Seq(0x106, 0x10a, 0x180).foreach { address =>
        when(io.readAddress === address.U(12)) { io.legal := true.B }
      }
      if parameter.enableTranslation then
        when(io.readAddress === 0x180.U(12)) { io.readData := satp.get }
        when(io.write & (io.writeAddress === 0x180.U(12))) {
          val mode = io.writeData.asBits.bits(63, 60)
          val rootFits = if parameter.physicalAddressBits == 56 then true.B else
            io.writeData.asBits.bits(43, parameter.physicalAddressBits - 12) === 0.B(56 - parameter.physicalAddressBits)
          when(mode === 0.B(4)) { satp.get := 0.U(64) }
          when((mode === 8.B(4)) & rootFits) {
            satp.get := (8.B(4) ## 0.B(16) ## io.writeData.asBits.bits(43, 0)).asUInt
          }
        }
      when(io.sret) {
        mode.get := status.asBits.bit(8).?(1.U(2), 0.U(2))
        status := ((status.asBits & BigInt("fffffffffffdfedd", 16).B(64)) |
          status.asBits.bit(5).?(0x22.B(64), 0x20.B(64))).asUInt
      }
    when(io.mret) {
      if parameter.enableSupervisorMode then mode.get := status.asBits.bits(12, 11).asUInt
      else if parameter.enableUserMode then user.get := status.asBits.bits(12, 11) === 0.B(2)
      val toMachine = status.asBits.bits(12, 11) === 3.B(2)
      val mask = if parameter.enableUserMode then BigInt("ffffffffffffe777", 16) else BigInt(0)
      status := ((status.asBits & mask.B(64) & toMachine.?(BigInt("ffffffffffffffff", 16).B(64), BigInt("fffffffffffdffff", 16).B(64))) |
        status.asBits.bit(7).?(0x88.B(64), 0x80.B(64))).asUInt
    }
    when(io.trap) {
      when(supervisorTrap) {
        if parameter.enableSupervisorMode then
          sepc.get := (io.trapPc.asBits.bits(63, 2) ## 0.B(2)).asUInt
          scause.get := io.trapCause
          stval.get := io.trapValue
          mode.get := 1.U(2)
          status := ((status.asBits & BigInt("fffffffffffffedd", 16).B(64)) |
            (privilege === 1.U(2)).?(0x100.B(64), 0.B(64)) | status.asBits.bit(1).?(0x20.B(64), 0.B(64))).asUInt
      }.otherwise {
        mepc := (io.trapPc.asBits.bits(63, 2) ## 0.B(2)).asUInt
        mcause := io.trapCause
        mtval := io.trapValue
        mode.foreach(_ := 3.U(2))
        user.foreach(_ := false.B)
        val savedPrivilege = if parameter.enableUserMode then (privilege.asBits ## 0.B(11)).asUInt else 0.U(64)
        status := ((status.asBits & BigInt("ffffffffffffe777", 16).B(64)) | savedPrivilege.asBits |
          status.asBits.bit(3).?(0x80.B(64), 0.B(64))).asUInt
      }
    }
    if parameter.enableSupervisorMode then
      val enables = RegInit(0.U(12))
      val softwarePending = RegInit(0.U(3))
      val inputs = io.interrupts.get
      val levels = (0.B(52) ## inputs.external.asBits ## 0.B(3) ## inputs.timer.asBits ## 0.B(3) ## inputs.software.asBits ## 0.B(3)).asUInt
      val supervisorLevels = (0.B(54) ## softwarePending.asBits.bits(2, 2) ## 0.B(3) ## softwarePending.asBits.bits(1, 1) ##
        0.B(3) ## softwarePending.asBits.bits(0, 0) ## 0.B(1)).asUInt
      val pending = (levels.asBits | supervisorLevels.asBits).asUInt
      val mask = mideleg.get.asBits.bits(11, 0)
      val active = enables.asBits & pending.asBits.bits(11, 0)
      val machinePending = active & (mask ^ 0xfff.B(12))
      val supervisorPending = active & mask
      val machineEnabled = ((privilege =/= 3.U(2)) | status.asBits.bit(3)) & (machinePending =/= 0.B(12))
      val supervisorEnabled = ((privilege === 0.U(2)) | ((privilege === 1.U(2)) & status.asBits.bit(1))) & (supervisorPending =/= 0.B(12))
      def interruptCause(bits: Referable[Bits]): Referable[UInt] =
        Seq(5, 1, 9, 7, 3, 11).foldLeft[Referable[UInt]](BigInt("8000000000000007", 16).U(64)) { (cause, bit) =>
          bits.bit(bit).?((BigInt("8000000000000000", 16) | bit).U(64), cause)
        }
      io.wakeup.get := active =/= 0.B(12)
      io.interruptPending.get := machineEnabled | supervisorEnabled
      io.interruptCause.get := machineEnabled.?(interruptCause(machinePending), interruptCause(supervisorPending))
      Seq((0x304, enables.asBits), (0x344, pending.asBits), (0x104, enables.asBits & mask),
        (0x144, pending.asBits.bits(11, 0) & mask)).foreach { case (address, bits) =>
        when(io.readAddress === address.U(12)) { io.readData := bits.asUInt; io.legal := true.B }
      }
      when(io.write & (io.writeAddress === 0x304.U(12))) { enables := (io.writeData.asBits.bits(11, 0) & 0xaaa.B(12)).asUInt }
      when(io.write & (io.writeAddress === 0x104.U(12))) {
        enables := ((enables.asBits & (mask ^ 0xfff.B(12))) | (io.writeData.asBits.bits(11, 0) & mask)).asUInt
      }
      when(io.write & (io.writeAddress === 0x344.U(12))) {
        val bits = io.writeData.asBits
        softwarePending := (bits.bits(9, 9) ## bits.bits(5, 5) ## bits.bits(1, 1)).asUInt
      }
      when(io.write & (io.writeAddress === 0x144.U(12)) & mask.bit(1)) {
        softwarePending := (softwarePending.asBits.bits(2, 1) ## io.writeData.asBits.bits(1, 1)).asUInt
      }
    else if parameter.enableInterrupts then
      val enables = RegInit(0.U(3))
      val inputs = io.interrupts.get
      val levels = inputs.external.asBits ## inputs.timer.asBits ## inputs.software.asBits
      val pending = enables.asBits & levels
      io.wakeup.get := pending =/= 0.B(3)
      io.interruptPending.get := (status.asBits.bit(3) | (privilege =/= 3.U(2))) & (pending =/= 0.B(3))
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
    if parameter.enableUserMode then
      Seq(0x306, 0x30a).foreach { address =>
        when(io.readAddress === address.U(12)) { io.legal := true.B }
      }
      if parameter.enableSupervisorMode then
        when((io.readAddress === 0x180.U(12)) & (privilege === 1.U(2)) & status.asBits.bit(20)) { io.legal := false.B }
      when(io.readAddress.asBits.bits(9, 8).asUInt > privilege) { io.legal := false.B }
