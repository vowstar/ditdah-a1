// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DebugCsrPort extends Bundle:
  val enter = Flipped(Bool())
  val pc = Flipped(UInt(64))
  val cause = Flipped(UInt(3))
  val dret = Flipped(Bool())
  val mode = Aligned(Bool())
  val step = Aligned(Bool())
  val ebreak = Aligned(Bool())

class DitDahA1CsrIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val timeValue = Option.when(parameter.enableCounters)(Flipped(UInt(64)))
  val retiredCount = Option.when(parameter.enableCounters)(Flipped(UInt(parameter.issueCountBits)))
  val debug = Option.when(parameter.enableJtag)(Aligned(new DebugCsrPort))
  val fpEnabled = Option.when(parameter.floatingPointBits != 0)(Aligned(Bool()))
  val roundingMode = Option.when(parameter.floatingPointBits != 0)(Aligned(UInt(3)))
  val fpDirty = Option.when(parameter.floatingPointBits != 0)(Flipped(Bool()))
  val fpFlags = Option.when(parameter.floatingPointBits != 0)(Flipped(UInt(5)))
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
  val waitTimeout = Option.when(parameter.enableZawrs)(Aligned(Bool()))
  val zeroLegal = Option.when(parameter.enableZicboz)(Aligned(Bool()))
  val cleanLegal = Option.when(parameter.enableZicbom)(Aligned(Bool()))
  val invalidateLegal = Option.when(parameter.enableZicbom)(Aligned(Bool()))
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
    parameter.validateCounters()
    val io = summon[Interface[DitDahA1CsrIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val status = RegInit(0.U(64))
    val debugMode = Option.when(parameter.enableJtag)(RegInit(false.B))
    val debugging = debugMode.getOrElse(false.B)
    io.readData := 0.U(64)
    io.legal := false.B
    val fpStatus = Wire(UInt(64))
    fpStatus := 0.U(64)
    if parameter.floatingPointBits != 0 then
      val fs = RegInit(0.U(2))
      val fcsr = RegInit(0.U(8))
      fpStatus := ((fs === 3.U(2)).asBits ## 0.B(48) ## fs.asBits ## 0.B(13)).asUInt
      io.fpEnabled.get := fs =/= 0.U(2)
      io.roundingMode.get := fcsr.asBits.bits(7, 5).asUInt
      when(io.write & ((io.writeAddress === 0x300.U(12)) | (parameter.enableSupervisorMode.B & (io.writeAddress === 0x100.U(12))))) { fs := io.writeData.asBits.bits(14, 13).asUInt }
      when(io.fpDirty.get) { fcsr := (fcsr.asBits | io.fpFlags.get.asBits).asUInt; fs := 3.U(2) }
      for address <- 1 to 3 do
        when(io.readAddress === address.U(12)) {
          io.readData := (if address == 1 then fcsr.asBits.bits(4, 0) else if address == 2 then fcsr.asBits.bits(7, 5) else fcsr.asBits).asUInt
          io.legal := io.fpEnabled.get
        }
        when(io.write & io.fpEnabled.get & (io.writeAddress === address.U(12))) {
          fcsr := (if address == 1 then fcsr.asBits.bits(7, 5) ## io.writeData.asBits.bits(4, 0) else if address == 2 then io.writeData.asBits.bits(2, 0) ## fcsr.asBits.bits(4, 0) else io.writeData.asBits.bits(7, 0)).asUInt
          fs := 3.U(2)
        }
    val satp = Option.when(parameter.enableTranslation)(RegInit(0.U(64)))
    if parameter.enableTranslation then
      io.translationState.get.satp := satp.get
      io.translationState.get.sum := status.asBits.bit(18)
      io.translationState.get.mxr := status.asBits.bit(19)
    val mode = Option.when(parameter.enableSupervisorMode)(RegInit(3.U(2)))
    val user = Option.when(parameter.enableUserMode && !parameter.enableSupervisorMode)(RegInit(false.B))
    val savedPrivilege = mode.getOrElse(user.map(_.?(0.U(2), 3.U(2))).getOrElse(3.U(2)))
    val privilege = if parameter.enableJtag then debugging.?(3.U(2), savedPrivilege) else savedPrivilege
    io.privilege := privilege
    io.waitTimeout.foreach(_ := (privilege =/= 3.U(2)) & status.asBits.bit(21))
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
    val overflowRequest = Option.when(parameter.hpmCounters > 0)(RegInit(false.B))
    val overflowPending = Option.when(parameter.hpmCounters > 0)(RegInit(false.B))
    val stimecmp = Option.when(parameter.enableSstc)(RegInit(((BigInt(1) << 64) - 1).U(64)))
    val stce = Option.when(parameter.enableSstc)(RegInit(false.B))
    if parameter.enableCounters then
      val countMask = ((BigInt(1) << (parameter.hpmCounters + 3)) - 1)
      val inhibitMask = countMask & ~BigInt(2)
      val mcounteren = Option.when(parameter.enableUserMode)(RegInit(0.U(32)))
      val scounteren = Option.when(parameter.enableSupervisorMode)(RegInit(0.U(32)))
      val inhibit = RegInit(0.U(32))
      val cycle = RegInit(0.U(64))
      val instret = RegInit(0.U(64))
      val hpm = Seq.fill(parameter.hpmCounters)(RegInit(0.U(64)))
      val selectors = Seq.fill(parameter.hpmCounters)(RegInit(0.U(2)))
      val filters = Seq.fill(parameter.hpmCounters)(RegInit(0.U(3)))
      val flags = Seq.fill(parameter.hpmCounters)(RegInit(false.B))
      for (address, register, mask) <- Seq((0x320, inhibit, inhibitMask)) ++
          mcounteren.map((0x306, _, countMask)) ++ scounteren.map((0x106, _, countMask)) do
        when(io.readAddress === address.U(12)) { io.readData := register; io.legal := true.B }
        when(io.write & (io.writeAddress === address.U(12))) { register := (io.writeData.asBits.bits(31, 0) & mask.B(32)).asUInt }
      for (index, register, delta) <- Seq((0, cycle, 1.U(parameter.issueCountBits)), (2, instret, io.retiredCount.get)) do
        when(!inhibit.asBits.bit(index)) { register := (register + delta).asBits.bits(63, 0).asUInt }
        when(io.write & (io.writeAddress === (0xb00 + index).U(12))) { register := io.writeData }
      val requests = (0 until parameter.hpmCounters).map { index =>
        val blocked = (privilege === 3.U(2)).?(filters(index).asBits.bit(2),
          (privilege === 1.U(2)).?(filters(index).asBits.bit(1), filters(index).asBits.bit(0)))
        val delta = (selectors(index) === 1.U(2)).?(1.U(parameter.issueCountBits),
          (selectors(index) === 2.U(2)).?(io.retiredCount.get, 0.U(parameter.issueCountBits)))
        val total = (0.U(65) + hpm(index) + delta).asBits
        val writing = io.write & (io.writeAddress === (0xb03 + index).U(12))
        val request = Wire(Bool())
        request := false.B
        when(!inhibit.asBits.bit(index + 3) & !blocked & !writing) {
          hpm(index) := total.bits(63, 0).asUInt
          when(total.bit(64)) { flags(index) := true.B; request := !flags(index) }
        }
        when(writing) { hpm(index) := io.writeData }
        when(io.write & (io.writeAddress === (0x323 + index).U(12))) {
          val selection = io.writeData.asBits.bits(1, 0).asUInt
          selectors(index) := (selection === 3.U(2)).?(0.U(2), selection)
          val mask = 4 | (if parameter.enableSupervisorMode then 2 else 0) | (if parameter.enableUserMode then 1 else 0)
          filters(index) := (io.writeData.asBits.bits(62, 60) & mask.B(3)).asUInt
          flags(index) := io.writeData.asBits.bit(63)
        }
        request
      }
      overflowRequest.foreach(_ := requests.foldLeft[Referable[Bool]](false.B)(_ | _))
      val values: Seq[Referable[UInt]] = Seq(cycle, io.timeValue.get, instret) ++ hpm ++ Seq.fill(29 - parameter.hpmCounters)(0.U(64))
      for index <- 0 until 32 do
        val lower = mcounteren.map(_.asBits.bit(index)).getOrElse(false.B) &
          (if parameter.enableSupervisorMode then (privilege =/= 0.U(2)) | scounteren.get.asBits.bit(index) else true.B)
        when(io.readAddress === (0xc00 + index).U(12)) { io.readData := values(index); io.legal := (privilege === 3.U(2)) | lower }
        if index != 1 then
          when(io.readAddress === (0xb00 + index).U(12)) { io.readData := values(index); io.legal := true.B }
        if index >= 3 then
          val event = if index < parameter.hpmCounters + 3 then
            flags(index - 3).asBits ## filters(index - 3).asBits ## 0.B(58) ## selectors(index - 3).asBits else 0.B(64)
          when(io.readAddress === (0x320 + index).U(12)) { io.readData := event.asUInt; io.legal := true.B }
      if parameter.enableSupervisorMode && parameter.hpmCounters > 0 then
        val bits = flags.zipWithIndex.foldLeft[Referable[Bits]](0.B(32)) { case (value, (flag, index)) =>
          value | flag.?((BigInt(1) << (index + 3)).B(32), 0.B(32)) }
        when(io.readAddress === 0xda0.U(12)) {
          io.readData := (bits & (privilege === 3.U(2)).?(countMask.B(32), mcounteren.get.asBits)).asUInt
          io.legal := true.B
        }
      if parameter.enableSstc then
        val allowed = (privilege === 3.U(2)) | ((privilege === 1.U(2)) & stce.get & mcounteren.get.asBits.bit(1))
        when(io.readAddress === 0x14d.U(12)) { io.readData := stimecmp.get; io.legal := allowed }
        when(io.readAddress === 0x30a.U(12)) { io.readData := (stce.get.asBits ## 0.B(63)).asUInt; io.legal := true.B }
        when(io.write & (io.writeAddress === 0x14d.U(12)) & allowed) { stimecmp.get := io.writeData }
        when(io.write & (io.writeAddress === 0x30a.U(12))) { stce.get := io.writeData.asBits.bit(63) }
    if parameter.enableZicboz || parameter.enableZicbom then
      val machineEnable = Option.when(parameter.enableUserMode)(RegInit(0.U(4)))
      val supervisorEnable = Option.when(parameter.enableSupervisorMode)(RegInit(0.U(4)))
      val machine = machineEnable.getOrElse(0.U(4)).asBits
      val supervisor = supervisorEnable.getOrElse(15.U(4)).asBits
      val unrestricted = privilege === 3.U(2)
      val supervisorMode = privilege === 1.U(2)
      io.zeroLegal.foreach(_ := unrestricted | (machine.bit(3) & (supervisorMode | supervisor.bit(3))))
      io.cleanLegal.foreach(_ := unrestricted | (machine.bit(2) & (supervisorMode | supervisor.bit(2))))
      io.invalidateLegal.foreach(_ := unrestricted | ((machine.bits(1, 0) =/= 0.B(2)) &
        (supervisorMode | (supervisor.bits(1, 0) =/= 0.B(2)))))
      val cbie = io.writeData.asBits.bits(5, 4)
      val fields = (io.writeData.asBits.bits(7, 6) ## (cbie === 2.B(2)).?(0.B(2), cbie)) &
        ((if parameter.enableZicboz then 8 else 0) | (if parameter.enableZicbom then 7 else 0)).B(4)
      if parameter.enableUserMode then
        when(io.readAddress === 0x30a.U(12)) {
          io.readData := (stce.getOrElse(false.B).asBits ## 0.B(55) ## machine ## 0.B(4)).asUInt
          io.legal := true.B
        }
        when(io.write & (io.writeAddress === 0x30a.U(12))) { machineEnable.get := fields.asUInt }
      if parameter.enableSupervisorMode then
        when(io.readAddress === 0x10a.U(12)) { io.readData := (0.B(56) ## supervisor ## 0.B(4)).asUInt }
        when(io.write & (io.writeAddress === 0x10a.U(12))) { supervisorEnable.get := fields.asUInt }
    val mtvec = RegInit(0.U(64))
    val mscratch = RegInit(0.U(64))
    val alignment = if parameter.enableC then 1 else 2
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
    if parameter.enableJtag then
      val debug = io.debug.get
      val dcsr = RegInit(3.U(16))
      val dpc = RegInit(parameter.resetVector.U(64))
      val dscratch = RegInit(0.U(64))
      val dscratch1 = Option.when(parameter.debugBase.nonEmpty)(RegInit(0.U(64)))
      debug.mode := debugging
      debug.step := dcsr.asBits.bit(2) & !debugging
      debug.ebreak := (savedPrivilege === 3.U(2)).?(dcsr.asBits.bit(15),
        (savedPrivilege === 1.U(2)).?(dcsr.asBits.bit(13), dcsr.asBits.bit(12)))
      Seq(0x7b0 -> ((BigInt("40000010", 16).B(64) | dcsr.asBits).asUInt),
        0x7b1 -> dpc, 0x7b2 -> dscratch).concat(dscratch1.map(0x7b3 -> _)).foreach { (address, value) =>
        when(io.readAddress === address.U(12)) { io.readData := value; io.legal := debugging }
      }
      when(debugging & io.write) {
        when(io.writeAddress === 0x7b0.U(12)) {
          val prv = io.writeData.asBits.bits(1, 0)
          val legalPrv = (prv === 3.B(2)) | (parameter.enableUserMode.B & (prv === 0.B(2))) |
            (parameter.enableSupervisorMode.B & (prv === 1.B(2)))
          val mask = 0x8004 | (if parameter.enableUserMode then 0x1000 else 0) | (if parameter.enableSupervisorMode then 0x2000 else 0)
          dcsr := ((dcsr.asBits & 0x1c0.B(16)) | (io.writeData.asBits.bits(15, 0) & mask.B(16)) |
            legalPrv.?(prv, 3.B(2))).asUInt
        }
        when(io.writeAddress === 0x7b1.U(12)) { dpc := (io.writeData.asBits.bits(63, alignment) ## 0.B(alignment)).asUInt }
        when(io.writeAddress === 0x7b2.U(12)) { dscratch := io.writeData }
        dscratch1.foreach(value => when(io.writeAddress === 0x7b3.U(12)) { value := io.writeData })
      }
      when(debug.enter) {
        debugMode.get := true.B
        dpc := (debug.pc.asBits.bits(63, alignment) ## 0.B(alignment)).asUInt
        dcsr := ((dcsr.asBits & 0xfe3c.B(16)) | (debug.cause.asBits ## 0.B(6)) | savedPrivilege.asBits).asUInt
      }
      when(debug.dret) {
        debugMode.get := false.B
        io.returnPc := dpc
        mode.foreach(_ := dcsr.asBits.bits(1, 0).asUInt)
        user.foreach(_ := dcsr.asBits.bits(1, 0) === 0.B(2))
        when(dcsr.asBits.bits(1, 0) =/= 3.B(2)) { status := (status.asBits & BigInt("fffffffffffdffff", 16).B(64)).asUInt }
      }
    Seq(0x301, 0x304, 0x344, 0xf11, 0xf12, 0xf13, 0xf14, 0xf15).foreach { address =>
      when(io.readAddress === address.U(12)) { io.legal := true.B }
    }
    if parameter.enableJtag then
      val extensions = Seq(0 -> parameter.enableA, 1 -> (parameter.enableZba && parameter.enableZbb && parameter.enableZbs),
        2 -> parameter.enableC, 3 -> (parameter.floatingPointBits == 64), 5 -> (parameter.floatingPointBits != 0),
        8 -> true, 12 -> parameter.enableM, 18 -> parameter.enableSupervisorMode, 20 -> parameter.enableUserMode)
      val misa = extensions.foldLeft(BigInt(2) << 62) { case (value, (bit, enabled)) => if enabled then value.setBit(bit) else value }
      when(io.readAddress === 0x301.U(12)) { io.readData := misa.U(64) }
    when(io.readAddress === 0xf14.U(12)) { io.readData := io.hartId }
    val machineRegisters = Seq((0x305, mtvec), (0x340, mscratch), (0x341, mepc), (0x342, mcause), (0x343, mtval))
    val supervisorRegisters = if parameter.enableSupervisorMode then
      Seq((0x105, stvec.get), (0x140, sscratch.get), (0x141, sepc.get), (0x142, scause.get), (0x143, stval.get))
    else Seq.empty
    (machineRegisters ++ supervisorRegisters).foreach { case (address, register) =>
      when(io.readAddress === address.U(12)) { io.readData := register; io.legal := true.B }
      when(io.write & (io.writeAddress === address.U(12))) {
        if Set(0x105, 0x141, 0x305, 0x341).contains(address) then
          val bits = if Set(0x141, 0x341).contains(address) then alignment else 2
          register := (io.writeData.asBits.bits(63, bits) ## 0.B(bits)).asUInt
        else register := io.writeData
      }
    }
    val fixedStatus = if parameter.enableSupervisorMode then BigInt("a00000000", 16)
      else if parameter.enableUserMode then BigInt("200000000", 16) else BigInt(0x1800)
    when(io.readAddress === 0x300.U(12)) { io.readData := (status.asBits | fixedStatus.B(64) | fpStatus.asBits).asUInt; io.legal := true.B }
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
        io.readData := ((status.asBits & supervisorMask.B(64)) | BigInt("200000000", 16).B(64) | fpStatus.asBits).asUInt
        io.legal := true.B
      }
      when(io.write & (io.writeAddress === 0x100.U(12))) {
        status := ((status.asBits & (BigInt("ffffffffffffffff", 16) ^ supervisorMask).B(64)) | (io.writeData.asBits & supervisorMask.B(64))).asUInt
      }
      Seq((0x302, medeleg.get, if parameter.enableTranslation then 0xb3ff else 0x3ff), (0x303, mideleg.get, 0x222 | (if parameter.hpmCounters > 0 then 0x2000 else 0))).foreach { case (address, register, mask) =>
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
            val asid = if parameter.asidBits == 0 then 0.B(16) else
              0.B(16 - parameter.asidBits) ## io.writeData.asBits.bits(43 + parameter.asidBits, 44)
            satp.get := (8.B(4) ## asid ## io.writeData.asBits.bits(43, 0)).asUInt
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
          sepc.get := (io.trapPc.asBits.bits(63, alignment) ## 0.B(alignment)).asUInt
          scause.get := io.trapCause
          stval.get := io.trapValue
          mode.get := 1.U(2)
          status := ((status.asBits & BigInt("fffffffffffffedd", 16).B(64)) |
            (privilege === 1.U(2)).?(0x100.B(64), 0.B(64)) | status.asBits.bit(1).?(0x20.B(64), 0.B(64))).asUInt
      }.otherwise {
        mepc := (io.trapPc.asBits.bits(63, alignment) ## 0.B(alignment)).asUInt
        mcause := io.trapCause
        mtval := io.trapValue
        mode.foreach(_ := 3.U(2))
        user.foreach(_ := false.B)
        val savedPrivilege = if parameter.enableUserMode then (privilege.asBits ## 0.B(11)).asUInt else 0.U(64)
        status := ((status.asBits & BigInt("ffffffffffffe777", 16).B(64)) | savedPrivilege.asBits |
          status.asBits.bit(3).?(0x80.B(64), 0.B(64))).asUInt
      }
    }
    if parameter.enableInterrupts then
      val supported = 0x888 | (if parameter.enableSupervisorMode then 0x222 else 0) | (if parameter.hpmCounters > 0 then 0x2000 else 0)
      val enables = RegInit(0.U(14))
      val softwarePending = Option.when(parameter.enableSupervisorMode)(RegInit(0.U(3)))
      val inputs = io.interrupts.get
      val machineLevels = 0.B(2) ## inputs.external.asBits ## 0.B(3) ## inputs.timer.asBits ## 0.B(3) ## inputs.software.asBits ## 0.B(3)
      val supervisorLevels = if parameter.enableSupervisorMode then
        val software = softwarePending.get.asBits
        val timer = if parameter.enableSstc then stce.get.?((io.timeValue.get >= stimecmp.get), software.bit(1)) else software.bit(1)
        0.B(4) ## software.bits(2, 2) ## 0.B(3) ## timer.asBits ## 0.B(3) ## software.bits(0, 0) ## 0.B(1)
      else 0.B(14)
      val pending = machineLevels | supervisorLevels | (overflowPending.getOrElse(false.B).asBits ## 0.B(13))
      val mask = if parameter.enableSupervisorMode then mideleg.get.asBits.bits(13, 0) else 0.B(14)
      val active = enables.asBits & pending
      val machinePending = active & (mask ^ 0x3fff.B(14))
      val supervisorPending = active & mask
      val machineEnabled = ((privilege =/= 3.U(2)) | status.asBits.bit(3)) & (machinePending =/= 0.B(14))
      val supervisorEnabled = parameter.enableSupervisorMode.B &
        ((privilege === 0.U(2)) | ((privilege === 1.U(2)) & status.asBits.bit(1))) & (supervisorPending =/= 0.B(14))
      def interruptCause(bits: Referable[Bits]): Referable[UInt] =
        Seq(13, 5, 1, 9, 7, 3, 11).foldLeft[Referable[UInt]](BigInt("8000000000000007", 16).U(64)) { (cause, bit) =>
          bits.bit(bit).?((BigInt("8000000000000000", 16) | bit).U(64), cause)
        }
      io.wakeup.get := active =/= 0.B(14)
      io.interruptPending.get := machineEnabled | supervisorEnabled
      io.interruptCause.get := machineEnabled.?(interruptCause(machinePending), interruptCause(supervisorPending))
      for (address, bits) <- Seq((0x304, enables.asBits), (0x344, pending)) ++
          (if parameter.enableSupervisorMode then Seq((0x104, enables.asBits & mask), (0x144, pending & mask)) else Seq.empty) do
        when(io.readAddress === address.U(12)) { io.readData := bits.asUInt; io.legal := true.B }
      when(io.write & (io.writeAddress === 0x304.U(12))) { enables := (io.writeData.asBits.bits(13, 0) & supported.B(14)).asUInt }
      if parameter.enableSupervisorMode then
        when(io.write & (io.writeAddress === 0x104.U(12))) {
          enables := ((enables.asBits & (mask ^ 0x3fff.B(14))) | (io.writeData.asBits.bits(13, 0) & mask & supported.B(14))).asUInt
        }
        when(io.write & (io.writeAddress === 0x344.U(12))) {
          val timer = stce.getOrElse(false.B).?(softwarePending.get.asBits.bits(1, 1), io.writeData.asBits.bits(5, 5))
          softwarePending.get := (io.writeData.asBits.bits(9, 9) ## timer ## io.writeData.asBits.bits(1, 1)).asUInt
        }
        when(io.write & (io.writeAddress === 0x144.U(12)) & mask.bit(1)) {
          softwarePending.get := (softwarePending.get.asBits.bits(2, 1) ## io.writeData.asBits.bits(1, 1)).asUInt
        }
      overflowPending.foreach { register =>
        val written = Wire(Bool())
        written := register
        when(io.write & ((io.writeAddress === 0x344.U(12)) | ((io.writeAddress === 0x144.U(12)) & mask.bit(13)))) {
          written := io.writeData.asBits.bit(13)
        }
        register := written | overflowRequest.get
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
