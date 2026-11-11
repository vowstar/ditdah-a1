// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

@generator
object DitDahA1Backend extends Generator[DitDahA1Parameter, DitDahA1Layers, DitDahA1BackendIO, DitDahA1Probe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Backend"
  def architecture(parameter: DitDahA1Parameter) =
    parameter.validateBackend()
    val io = summon[Interface[DitDahA1BackendIO]]
    val probe = summon[ProbeInterface[DitDahA1Probe]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val width = parameter.issueWidth
    val countBits = parameter.issueCountBits
    val instructionCount = RegInit(0.U(countBits))
    val instructionPackets = Reg(Vec(width, new FetchPacket))
    val decodedCount = RegInit(0.U(countBits))
    val decodedValid = decodedCount =/= 0.U
    val decodedPackets = Reg(Vec(width, new DecodedPacket(parameter)))
    val issuedCount = RegInit(0.U(countBits))
    val issuedValid = issuedCount =/= 0.U
    val issuedPackets = Reg(Vec(width, new IssuedPacket(parameter)))
    val issuedPacket = issuedPackets(0)
    val resultCount = RegInit(0.U(countBits))
    val resultValid = resultCount =/= 0.U
    val resultPackets = Reg(Vec(width, new ResultPacket(parameter)))
    val resultPacket = resultPackets(0)
    val resultResolved = RegInit(false.B)
    val memoryCount = RegInit(0.U(countBits))
    val memoryValid = memoryCount =/= 0.U
    val memoryPackets = Reg(Vec(width, new ResultPacket(parameter)))
    val memoryPacket = memoryPackets(0)
    val memoryResolved = RegInit(false.B)
    val commitCount = RegInit(0.U(countBits))
    val commitValid = commitCount =/= 0.U
    val commitPackets = Reg(Vec(width, new ResultPacket(parameter)))
    val commitPacket = commitPackets(0)
    def csrInstruction(instruction: Referable[UInt]): Referable[Bool] =
      val encoding = instruction.asBits
      (encoding.bits(6, 0) === 0x73.B(7)) & (encoding.bits(13, 12) =/= 0.B(2))
    val commitCsr = commitValid & csrInstruction(commitPacket.instruction.instruction)
    val csrInFlight = (issuedValid & csrInstruction(issuedPacket.decoded.instruction.instruction)) |
      (resultValid & csrInstruction(resultPacket.instruction.instruction)) |
      (memoryValid & csrInstruction(memoryPacket.instruction.instruction)) | commitCsr
    val commitResolved = RegInit(false.B)
    val memoryPending = RegInit(false.B)
    val concurrent = parameter.loadQueueEntries == 2
    val extraCount = Option.when(concurrent)(RegInit(0.U(countBits)))
    val extraPackets = Option.when(concurrent)(Reg(Vec(width, new ResultPacket(parameter))))
    val extraPending = Option.when(concurrent)(RegInit(false.B))
    val extraValid = extraCount.map(_ =/= 0.U).getOrElse(false.B)
    val executePending = Option.when(parameter.enableM || parameter.floatingPointBits != 0)(RegInit(false.B))
    val resumePc = Option.when(parameter.enableInterrupts || parameter.enableJtag)(RegInit(parameter.resetVector.U(64)))
    val debugBreakPending = Option.when(parameter.enableJtag)(RegInit(false.B))
    val stepIssued = Option.when(parameter.enableJtag)(RegInit(false.B))
    val sleep = Option.when(parameter.enableInterrupts)(RegInit(false.B))
    val sleeping = if parameter.enableInterrupts then sleep.get else false.B
    val decode = DitDahA1Decode.instantiate(parameter)
    val decodes = decode +: Seq.fill(width - 1)(DitDahA1Decode.instantiate(parameter))
    val issue = DitDahA1Issue.instantiate(parameter)
    val issues = issue +: Seq.fill(width - 1)(DitDahA1Issue.instantiate(parameter))
    val execute = DitDahA1Execute.instantiate(parameter)
    val mulDiv = Option.when(parameter.enableM)(DitDahA1MulDiv.instantiate(parameter))
    val fpu = Option.when(parameter.floatingPointBits != 0)(DitDahA1Fpu.instantiate(parameter))
    val commit = DitDahA1Commit.instantiate(parameter)
    val gpr = DitDahA1Gpr.instantiate(parameter)
    val csr = DitDahA1Csr.instantiate(parameter)
    val lsu = DitDahA1Lsu.instantiate(parameter)
    val debugging = csr.io.debug.map(_.mode).getOrElse(false.B)
    val stepping = csr.io.debug.map(_.step).getOrElse(false.B)
    val haltReq = io.debug.map(_.haltReq).getOrElse(false.B)
    val stopDispatch = if parameter.enableJtag then !debugging & (haltReq | debugBreakPending.get | stepIssued.get) else false.B
    val enterDebug = if parameter.enableJtag then stopDispatch & !issuedValid & !resultValid & !memoryValid &
      !commitValid & !extraValid & !executePending.getOrElse(false.B) & lsu.io.idle.get else false.B
    io.debug.foreach(_.mode := debugging)
    execute.io.debugMode.foreach(_ := debugging)
    lsu.io.debugMode.foreach(_ := debugging)
    if parameter.pmpEntries != 0 then
      io.pmp.get :<= csr.io.pmp.get
      lsu.io.pmp.get :<= csr.io.pmp.get
    gpr.io.clock := io.clock
    gpr.io.reset := io.reset
    csr.io.clock := io.clock
    csr.io.reset := io.reset
    csr.io.hartId := io.hartId
    csr.io.timeValue.foreach(_ := io.timeValue.get)
    if parameter.enableInterrupts then csr.io.interrupts.get :<= io.interrupts.get
    lsu.io.clock := io.clock
    io.reservation.foreach(_ :<>= lsu.io.reservation.get)
    lsu.io.reset := io.reset
    mulDiv.foreach { resource => resource.io.clock := io.clock; resource.io.reset := io.reset }
    fpu.foreach { resource => resource.io.clock := io.clock; resource.io.reset := io.reset }
    execute.io.fpEnabled.foreach(_ := csr.io.fpEnabled.get)
    execute.io.roundingMode.foreach(_ := csr.io.roundingMode.get)
    execute.io.input.bits :<= issuedPacket
    execute.io.csrValue := csr.io.readData
    execute.io.csrLegal := csr.io.legal
    execute.io.privilege := csr.io.privilege
    execute.io.wfiLegal := csr.io.wfiLegal
    execute.io.zeroLegal.foreach(_ := csr.io.zeroLegal.get)
    execute.io.cleanLegal.foreach(_ := csr.io.cleanLegal.get)
    execute.io.invalidateLegal.foreach(_ := csr.io.invalidateLegal.get)
    execute.io.sretLegal := csr.io.sretLegal
    execute.io.sfenceLegal := csr.io.sfenceLegal
    if parameter.enableTranslation then
      io.translationState.get :<= csr.io.translationState.get
      io.translation.get :<>= lsu.io.translation.get
    io.privilege := csr.io.privilege
    lsu.io.privilege := csr.io.dataPrivilege
    csr.io.readAddress := commitCsr.?(commitPacket.csrAddress, execute.io.csrAddress)
    // Completed data operations keep ownership until their architectural event.
    val interruptEligible = if parameter.enableInterrupts then
      csr.io.interruptPending.get & !debugging & !stepping & !stopDispatch
    else false.B
    val takeInterrupt = interruptEligible & !memoryPending &
      (if concurrent then !extraValid & !(memoryValid & (memoryPacket.load | memoryPacket.store)) else true.B) &
      !(commitValid & (commitPacket.load | commitPacket.store | commitPacket.instruction.fault))
    val interruptCause = if parameter.enableInterrupts then csr.io.interruptCause.get else 0.U(64)
    val waitStall = Wire(Bool())
    val waitFault = Wire(Bool())
    waitStall := false.B
    waitFault := false.B
    if parameter.enableZawrs then
      val elapsed = RegInit(0.U(6))
      val encoding = commitPacket.instruction.instruction
      val waiting = commitValid & !commitPacket.instruction.fault &
        ((encoding === 0x00d00073.U(32)) | (encoding === 0x01d00073.U(32))) &
        lsu.io.reservationValid.get & !csr.io.wakeup.getOrElse(false.B) &
        !debugging & !stepping & !stopDispatch & !takeInterrupt
      val expired = elapsed === 63.U(6)
      waitStall := waiting & !expired
      waitFault := waiting & expired & (encoding === 0x00d00073.U(32)) & csr.io.waitTimeout.get
      elapsed := waitStall.?((elapsed + 1.U(6)).asBits.bits(5, 0).asUInt, 0.U(6))
    commit.io.input.valid := commitValid & !takeInterrupt & !waitStall
    commit.io.input.bits :<= commitPacket
    when(waitFault) {
      commit.io.input.bits.instruction.fault := true.B
      commit.io.input.bits.instruction.cause := 2.U(64)
      commit.io.input.bits.instruction.tval := commitPacket.instruction.instruction
    }
    when(commitCsr & !commitPacket.instruction.fault) {
      commit.io.input.bits.value := csr.io.readData
      val action = commitPacket.instruction.instruction.asBits.bits(13, 12)
      when(action === 2.B(2)) { commit.io.input.bits.csrData := (csr.io.readData.asBits | commitPacket.csrData.asBits).asUInt }
      when(action === 3.B(2)) { commit.io.input.bits.csrData := (csr.io.readData.asBits & (commitPacket.csrData.asBits ^ BigInt("ffffffffffffffff", 16).B(64))).asUInt }
    }
    commit.io.output.ready := true.B
    commit.io.trapVector := csr.io.trapVector
    commit.io.returnPc := csr.io.returnPc
    val retire = commit.io.output
    val retired = retire.valid & retire.ready
    val retireCount = retired.?(retire.bits.instruction.fault.?(1.U(countBits), commitCount), 0.U(countBits))
    csr.io.retiredCount.foreach(_ := (retired & !retire.bits.instruction.fault).?(commitCount, 0.U(countBits)))
    val retirement = Wire(Vec(width, new ResultPacket(parameter)))
    retirement(0) :<= retire.bits
    for lane <- 1 until width do
      retirement(lane) :<= commitPackets(lane)
      retirement(lane).rdWrite := commitPackets(lane).rdWrite & (commitPackets(lane).rd =/= 0.U(5))
    val breakpoint = retired & retire.bits.instruction.fault & (retire.bits.instruction.cause === 3.U(64))
    val debugBreak = parameter.enableJtag.B & breakpoint & !debugging & csr.io.debug.map(_.ebreak).getOrElse(false.B)
    val debugReturn = parameter.enableJtag.B & retired & retire.bits.mret & !retire.bits.instruction.fault &
      (retire.bits.instruction.instruction === 0x7b200073L.U(32))
    csr.io.debug.foreach { debug =>
      debug.enter := enterDebug
      debug.pc := resumePc.get
      debug.cause := haltReq.?(3.U(3), debugBreakPending.get.?(1.U(3), 4.U(3)))
      debug.dret := debugReturn
      when(debugBreak) { debugBreakPending.get := true.B }
      when(enterDebug) { debugBreakPending.get := false.B }
      when(debugging) { stepIssued.get := false.B }
    }
    val floatingOperands = Option.when(parameter.floatingPointBits != 0) {
      val packet = decodedPackets(0)
      val write = retired & !retire.bits.instruction.fault & retire.bits.fpWrite.get
      csr.io.fpDirty.get := write | (retired & !retire.bits.instruction.fault & (retire.bits.fpFlags.get =/= 0.U(5)))
      csr.io.fpFlags.get := retire.bits.fpFlags.get
      DitDahA1RegisterFile(parameter.floatingPointBits, false,
        Seq(packet.rs1, packet.rs2, packet.instruction.instruction.asBits.bits(31, 27).asUInt),
        Seq((write, retire.bits.rd, retire.bits.value)))
    }
    val sequentialPc = (retire.bits.instruction.pc + retire.bits.instruction.length).asBits.bits(63, 0).asUInt
    val enterWfi = retired & retire.bits.wfi & !retire.bits.instruction.fault & !debugging & !stepping
    val pmpUpdate = if parameter.pmpEntries == 0 then false.B else
      retire.bits.csrWrite & (((retire.bits.csrAddress >= 0x3a0.U(12)) & (retire.bits.csrAddress <= 0x3ae.U(12))) |
        ((retire.bits.csrAddress >= 0x3b0.U(12)) & (retire.bits.csrAddress <= 0x3ef.U(12))))
    val translationUpdate = if parameter.enableTranslation then
      retire.bits.sfenceVma | (retire.bits.csrWrite & (retire.bits.csrAddress === 0x180.U(12))) else false.B
    val satpUpdate = retire.bits.csrWrite & (retire.bits.csrAddress === 0x180.U(12))
    io.invalidateTranslation.foreach(_ := retired & (pmpUpdate | (if parameter.preciseTranslationMaintenance then
      (if parameter.asidBits == 0 then satpUpdate else false.B) else translationUpdate)))
    io.translationMaintenance.foreach { maintenance =>
      maintenance.valid := retired & !retire.bits.instruction.fault & (retire.bits.sfenceVma | (parameter.asidBits != 0).B & satpUpdate)
      maintenance.fence := retire.bits.sfenceVma
      maintenance.addressValid := retire.bits.instruction.instruction.asBits.bits(19, 15) =/= 0.B(5)
      maintenance.address := retire.bits.address
      maintenance.asidValid := retire.bits.instruction.instruction.asBits.bits(24, 20) =/= 0.B(5)
      maintenance.asid := (if parameter.asidBits == 0 then 0.U(1) else retire.bits.storeData.asBits.bits(parameter.asidBits - 1, 0).asUInt)
    }
    val redirect = takeInterrupt | (retired & (retire.bits.instruction.fault | retire.bits.mret | retire.bits.sret |
      pmpUpdate | translationUpdate | retire.bits.fenceI | (!commitResolved & (retire.bits.nextPc =/= sequentialPc)))) | enterWfi | enterDebug
    if parameter.iCacheBytes != 0 then io.invalidate.get := retired & (retire.bits.fenceI | pmpUpdate | translationUpdate)
    val commitReady = !commitValid | retired
    val memoryOperation = (resultPacket.load | resultPacket.store) & !resultPacket.instruction.fault
    val memoryCompletion = (memoryPacket.load | memoryPacket.store) & !memoryPacket.instruction.fault
    val completion = Wire(new ResultPacket(parameter))
    completion :<= memoryPacket
    when(memoryPending & (if concurrent then lsu.io.output.valid else true.B)) { completion :<= lsu.io.output.bits }
    val memoryFault = memoryValid & completion.instruction.fault
    val tailReceiving = extraPending.getOrElse(false.B) & !memoryPending & lsu.io.output.valid
    val memoryReady = if concurrent then !memoryPending | lsu.io.output.valid else !memoryCompletion | (memoryPending & lsu.io.output.valid)
    val memoryAdvance = memoryValid & memoryReady & commitReady & !redirect &
      (if concurrent then !tailReceiving & (!memoryFault | !extraPending.get) else true.B)
    val append = if !concurrent then false.B else memoryValid & !extraValid & !memoryAdvance & !memoryFault &
      memoryPacket.load & !memoryPacket.store & !memoryPacket.atomic &
      resultPacket.load & !resultPacket.store & !resultPacket.atomic & !resultPacket.instruction.fault
    val resultAdvance = resultValid & ((!memoryValid | (memoryAdvance & !extraValid)) | append) &
      (!memoryOperation | (lsu.io.input.valid & lsu.io.input.ready)) & !redirect &
      (if concurrent then !interruptEligible | !(resultPacket.load | resultPacket.store) else true.B)
    val floating = issuedPacket.decoded.floating.getOrElse(false.B)
    val arithmetic = issuedPacket.decoded.operation === DitDahA1Isa.Arithmetic.U(DitDahA1Isa.operationBits)
    val isMulDiv = parameter.enableM.B & arithmetic & !floating & !issuedPacket.decoded.instruction.fault
    val isFloating = floating & arithmetic & !execute.io.output.bits.instruction.fault
    val longOperation = isMulDiv | isFloating
    val longReady = (isMulDiv & mulDiv.map(_.io.output.valid).getOrElse(false.B)) | (isFloating & fpu.map(_.io.output.valid).getOrElse(false.B))
    execute.io.input.valid := issuedValid & (!longOperation | (executePending.getOrElse(false.B) & longReady)) & !redirect
    execute.io.output.ready := (!resultValid | resultAdvance) & !redirect
    mulDiv.foreach { resource =>
      resource.io.input.bits :<= issuedPacket
      resource.io.input.valid := issuedValid & isMulDiv & !executePending.get & !redirect
      resource.io.output.ready := !issuedValid | (isMulDiv & execute.io.output.ready)
      when(resource.io.input.valid & resource.io.input.ready) { executePending.get := true.B }
      when(resource.io.output.valid & resource.io.output.ready) { executePending.get := false.B }
    }
    fpu.foreach { resource =>
      val encoding = issuedPacket.decoded.instruction.instruction.asBits
      resource.io.input.bits.instruction := encoding.asUInt
      resource.io.input.bits.a := issuedPacket.operand1
      resource.io.input.bits.b := issuedPacket.operand2
      resource.io.input.bits.c := issuedPacket.operand3.get
      resource.io.input.bits.roundingMode := (encoding.bits(14, 12) === 7.B(3)).?(csr.io.roundingMode.get, encoding.bits(14, 12).asUInt)
      resource.io.input.valid := issuedValid & isFloating & !executePending.get & !redirect
      resource.io.output.ready := !issuedValid | (isFloating & execute.io.output.ready)
      when(resource.io.input.valid & resource.io.input.ready) { executePending.get := true.B }
      when(resource.io.output.valid & resource.io.output.ready) { executePending.get := false.B }
    }
    val executed = execute.io.output.valid & execute.io.output.ready
    val execution = Wire(Vec(width, new ResultPacket(parameter)))
    execution(0) :<= execute.io.output.bits
    mulDiv.foreach { resource => when(isMulDiv) { execution(0).value := resource.io.output.bits } }
    fpu.foreach { resource => when(isFloating) { execution(0).value := resource.io.output.bits.value; execution(0).fpFlags.get := resource.io.output.bits.flags } }
    for lane <- 1 until width do DitDahA1Alu.result(parameter, issuedPackets(lane), execution(lane))
    val control = Seq(DitDahA1Isa.Beq, DitDahA1Isa.Branch, DitDahA1Isa.Jal, DitDahA1Isa.Jalr)
      .map(op => issuedPacket.decoded.operation === op.U(DitDahA1Isa.operationBits)).reduce(_ | _)
    val resolved = control & !execution(0).instruction.fault
    val predictedOffset = if parameter.enableBranchPrediction then issuedPacket.decoded.instruction.predictedTaken
      .?(issuedPacket.decoded.immediate, issuedPacket.decoded.instruction.length) else issuedPacket.decoded.instruction.length
    val predictedPc = if parameter.branchPredictorEntries != 0 then
      issuedPacket.decoded.instruction.predictedTaken.?(issuedPacket.decoded.instruction.predictedPc.get,
        (issuedPacket.decoded.instruction.pc + issuedPacket.decoded.instruction.length).asBits.bits(63, 0).asUInt)
      else (issuedPacket.decoded.instruction.pc + predictedOffset).asBits.bits(63, 0).asUInt
    val earlyRedirect = executed & resolved & (execution(0).nextPc =/= predictedPc)
    io.prediction.foreach { update =>
      val conditional = (issuedPacket.decoded.operation === DitDahA1Isa.Beq.U(DitDahA1Isa.operationBits)) |
        (issuedPacket.decoded.operation === DitDahA1Isa.Branch.U(DitDahA1Isa.operationBits))
      update.clear := redirect
      update.valid := executed & resolved & (conditional |
        (issuedPacket.decoded.operation === DitDahA1Isa.Jalr.U(DitDahA1Isa.operationBits)))
      update.pc := issuedPacket.decoded.instruction.pc
      update.nextPc := execution(0).nextPc
      update.conditional := conditional
      update.taken := execution(0).nextPc =/= (issuedPacket.decoded.instruction.pc + issuedPacket.decoded.instruction.length).asBits.bits(63, 0).asUInt
    }
    val flushYounger = redirect | earlyRedirect
    val destinations = (0 until width).map { lane =>
      val packet = commitPackets(lane)
      ((lane.U < commitCount) & packet.rdWrite, packet.rd, !packet.instruction.fault, packet.value)
    } ++ (0 until width).map { lane =>
      val packet = memoryPackets(lane)
      val completed = if lane == 0 then completion else packet
      ((lane.U < memoryCount) & packet.rdWrite, packet.rd,
        (if lane == 0 then (if concurrent then !memoryPending | lsu.io.output.valid else !memoryCompletion | (memoryPending & lsu.io.output.valid)) else true.B) & !completed.instruction.fault, completed.value)
    } ++ (if !concurrent then Seq.empty else (0 until width).map { lane =>
      val packet = extraPackets.get(lane)
      ((lane.U < extraCount.get) & packet.rdWrite, packet.rd, !extraPending.get & !packet.instruction.fault, packet.value)
    }) ++ (0 until width).map { lane =>
      val packet = resultPackets(lane)
      ((lane.U < resultCount) & packet.rdWrite, packet.rd,
        (if lane == 0 then !memoryOperation else true.B) & !packet.instruction.fault, packet.value)
    } ++ (0 until width).map { lane =>
      val packet = issuedPackets(lane).decoded
      ((lane.U < issuedCount) & packet.writesRd, packet.rd,
        execute.io.output.valid & !execution(lane).instruction.fault & !execution(lane).load & !execution(lane).store, execution(lane).value)
    }
    def resolve(address: Referable[UInt], original: Referable[UInt]) =
      val value = Wire(UInt(64))
      val blocked = Wire(Bool())
      value := original
      blocked := false.B
      for (valid, rd, ready, data) <- destinations do
        when(valid & (rd =/= 0.U(5)) & (address === rd)) { value := data; blocked := !ready }
      (value, blocked)
    val older = issuedValid | resultValid | memoryValid | commitValid
    val available = (!issuedValid | executed) & !csrInFlight & !executePending.getOrElse(false.B) & !flushYounger & !sleeping & !stopDispatch &
      (if parameter.enableJtag then !debugging | !older else true.B)
    val prefix = Wire(Vec(width, Bool()))
    val simple = (0 until width).map { lane =>
      import DitDahA1Isa.*
      !decodedPackets(lane).instruction.fault & Seq(Lui, Auipc, Addi, Add, AluImmediate, AluRegister,
        AluWordImmediate, AluWordRegister).map(op => decodedPackets(lane).operation === op.U(operationBits)).reduce(_ | _)
    }
    val groupedHead = simple(0) | (!decodedPackets(0).floating.getOrElse(false.B) & !decodedPackets(0).instruction.fault &
      Seq(DitDahA1Isa.Ld, DitDahA1Isa.Lw, DitDahA1Isa.Lwu, DitDahA1Isa.Load, DitDahA1Isa.Sd, DitDahA1Isa.Sw, DitDahA1Isa.Store)
        .map(op => decodedPackets(0).operation === op.U(DitDahA1Isa.operationBits)).reduce(_ | _))
    val dependencies = (0 until width).map { lane =>
      val unit = issues(lane)
      val packet = decodedPackets(lane)
      unit.io.input.bits :<= packet
      gpr.io.raddr1(lane) := unit.io.raddr1
      gpr.io.raddr2(lane) := unit.io.raddr2
      val (operand1, blocked1) = resolve(unit.io.raddr1, gpr.io.rdata1(lane))
      val (operand2, blocked2) = resolve(unit.io.raddr2, gpr.io.rdata2(lane))
      unit.io.rdata1 := operand1
      unit.io.rdata2 := operand2
      if parameter.floatingPointBits != 0 then
        unit.io.rdata3.get := (if lane == 0 then floatingOperands.get(2) else 0.U(parameter.floatingPointBits))
        if lane == 0 then
          when(packet.floating.get) {
            when((packet.operation === DitDahA1Isa.Arithmetic.U(5)) & !packet.usesRs1) { unit.io.rdata1 := floatingOperands.get(0) }
            unit.io.rdata2 := floatingOperands.get(1)
          }

      val blocked = blocked1 | blocked2 | (packet.serializing & older)
      val conflict = (0 until lane).map { previous =>
        val writer = decodedPackets(previous)
        writer.writesRd & (writer.rd =/= 0.U(5)) &
          ((packet.usesRs1 & (writer.rd === packet.rs1)) | (packet.usesRs2 & (writer.rd === packet.rs2)) |
            (packet.writesRd & (writer.rd === packet.rd)))
      }.foldLeft[Referable[Bool]](false.B)(_ | _)
      prefix(lane) := (lane.U < decodedCount) & !blocked &
        (if lane == 0 then true.B else prefix(lane - 1) & groupedHead & simple(lane) & !conflict & !stepping & !debugging)
      unit.io.input.valid := prefix(lane) & !flushYounger & !sleeping
      unit.io.output.ready := available
      blocked
    }
    val stalled = dependencies.head
    val issueCount = Wire(UInt(countBits))
    issueCount := available.?((0 until width).map(lane => prefix(lane).?(1.U(countBits), 0.U(countBits))).reduce(_ + _)
      .asBits.bits(countBits - 1, 0).asUInt, 0.U(countBits))
    val issued = issueCount =/= 0.U
    val decodedFree = width.U(countBits) - (decodedCount - issueCount)
    val decodeCount = (!flushYounger & !sleeping & !stopDispatch).?((instructionCount <= decodedFree).?(instructionCount, decodedFree), 0.U(countBits))
      .asBits.bits(countBits - 1, 0).asUInt
    val decodedInput = Wire(Vec(width, new DecodedPacket(parameter)))
    for lane <- 0 until width do
      decodes(lane).io.input.bits :<= instructionPackets(lane)
      decodes(lane).io.input.valid := (lane.U < instructionCount) & !flushYounger & !sleeping
      decodes(lane).io.output.ready := lane.U < decodeCount
      decodedInput(lane) :<= decodes(lane).io.output.bits
    io.instruction.ready := !flushYounger & !sleeping & !stopDispatch & (io.instruction.bits.count <= width.U - (instructionCount - decodeCount))
    val received = io.instruction.valid & io.instruction.ready
    io.redirect := flushYounger
    io.redirectPc := earlyRedirect.?(execution(0).nextPc, retire.bits.nextPc)
    io.debug.foreach { debug =>
      when(debugging & retired & retire.bits.instruction.fault) { io.redirectPc := breakpoint.?(debug.entryPc, debug.exceptionPc) }
      when(enterDebug) { io.redirectPc := debug.entryPc }
    }
    lsu.io.input.valid := resultValid & memoryOperation & !commitValid & !redirect &
      (if concurrent then !interruptEligible else true.B) &
      (if concurrent then ((!memoryValid & !extraValid) | append) & !memoryFault else !memoryPending & !memoryValid)
    lsu.io.input.bits :<= resultPacket
    lsu.io.storeAllowed := (if concurrent then !memoryValid | memoryPending else !memoryValid) & !commitValid & !redirect & !memoryFault
    lsu.io.output.ready := (if concurrent then memoryPending | extraPending.get else memoryValid & memoryPending & commitReady) & !redirect
    if parameter.enableJtag then
      when((debugging | stopDispatch) & !memoryPending & !extraPending.getOrElse(false.B) & !redirect) { lsu.io.output.ready := true.B }
    lsu.io.cancel.foreach(_ := memoryFault | redirect)
    for lane <- 0 until width do
      gpr.io.we(lane) := (lane.U < retireCount) & retirement(lane).rdWrite
      gpr.io.waddr(lane) := retirement(lane).rd
      gpr.io.wdata(lane) := retirement(lane).value
    csr.io.write := retired & retire.bits.csrWrite
    csr.io.writeAddress := retire.bits.csrAddress
    csr.io.writeData := retire.bits.csrData
    csr.io.trap := retired & retire.bits.instruction.fault & !debugging & !debugBreak
    csr.io.trapPc := retire.bits.instruction.pc
    csr.io.trapCause := retire.bits.instruction.cause
    csr.io.trapValue := retire.bits.instruction.tval
    csr.io.mret := retired & retire.bits.mret & !debugReturn
    csr.io.sret := retired & retire.bits.sret
    if parameter.enableInterrupts || parameter.enableJtag then
      for lane <- 0 until width do
        when(retired & !debugging & (retireCount === (lane + 1).U)) { resumePc.get := debugBreak.?(retire.bits.instruction.pc, retirement(lane).nextPc) }
      when(debugReturn) { resumePc.get := retire.bits.nextPc }
    if parameter.enableJtag then
      when(issued & stepping) { stepIssued.get := true.B }
    if parameter.enableInterrupts then
      sleep.get := (sleep.get | enterWfi) & !csr.io.wakeup.get & !csr.io.trap
      when(enterDebug) { sleep.get := false.B }
      when(takeInterrupt) {
        resumePc.get := csr.io.trapVector
        io.redirectPc := csr.io.trapVector
        csr.io.trap := true.B
        csr.io.trapPc := resumePc.get
        csr.io.trapCause := interruptCause
        csr.io.trapValue := 0.U(64)
      }
    io.status.trap := csr.io.trap
    io.status.busy := true.B
    io.status.sleep := sleeping
    io.data :<>= lsu.io.memory
    when(retired) { commitCount := 0.U }
    when(memoryAdvance) {
      commitCount := memoryCount
      commitPackets :<= memoryPackets
      commitPackets(0) :<= completion
      commitResolved := memoryResolved
      memoryCount := 0.U
      if concurrent then
        memoryPending := false.B
        when(extraValid & !memoryFault) {
          memoryCount := extraCount.get; memoryPackets :<= extraPackets.get; memoryResolved := false.B
          memoryPending := extraPending.get
        }
        extraCount.get := 0.U; extraPending.get := false.B
    }
    when(resultAdvance) {
      resultCount := 0.U
      if concurrent then
        when(append) { extraCount.get := resultCount; extraPackets.get :<= resultPackets; extraPending.get := true.B }
          .otherwise { memoryCount := resultCount; memoryPackets :<= resultPackets; memoryResolved := resultResolved }
      else { memoryCount := resultCount; memoryPackets :<= resultPackets; memoryResolved := resultResolved }
    }
    when(executed) { resultPackets :<= execution; resultResolved := resolved; resultCount := issuedCount; issuedCount := 0.U }
    // Accepted arithmetic drains before the issued group is reused.
    when(issued) {
      issuedCount := issueCount
      for lane <- 0 until width do issuedPackets(lane) :<= issues(lane).io.output.bits
    }
    def compact[T <: Data & Connectable](count: Reg[UInt], packets: Reg[Vec[T]], taken: Referable[UInt],
        incoming: Referable[Vec[T]], added: Referable[UInt]): Unit =
      val remaining = (count - taken).asBits.bits(countBits - 1, 0).asUInt
      val total = (remaining + added).asBits.bits(countBits - 1, 0).asUInt
      when(!redirect) {
        count := total
        for lane <- 0 until width do
          when(lane.U < remaining) { packets(lane) :<= packets.ref((taken + lane.U).asBits.bits(countBits - 1, 0).asUInt) }
          when((lane.U >= remaining) & (lane.U < total)) { packets(lane) :<= incoming.ref((lane.U(countBits) - remaining).asBits.bits(countBits - 1, 0).asUInt) }
      }
    compact(decodedCount, decodedPackets, issueCount, decodedInput, decodeCount)
    compact(instructionCount, instructionPackets, decodeCount, io.instruction.bits.packets, received.?(io.instruction.bits.count, 0.U(countBits)))
    when(lsu.io.input.valid & lsu.io.input.ready & !append) { memoryPending := true.B }
    when(lsu.io.output.valid & lsu.io.output.ready) {
      if concurrent then
        when(memoryPending) {
          when(!memoryAdvance) { memoryPackets(0) :<= lsu.io.output.bits; memoryPending := false.B }
        }.otherwise { extraPackets.get(0) :<= lsu.io.output.bits; extraPending.get := false.B }
      else memoryPending := false.B
    }
    when(earlyRedirect) { instructionCount := 0.U; decodedCount := 0.U }
    when(redirect) {
      instructionCount := 0.U
      decodedCount := 0.U
      issuedCount := 0.U
      resultCount := 0.U
      memoryCount := 0.U
      commitCount := 0.U
      if concurrent then { extraCount.get := 0.U; extraPending.get := false.B; memoryPending := false.B }
    }
    layer("DV"):
      val traceCount = Wire(UInt(countBits))
      traceCount := (debugging | debugBreak).?(0.U(countBits), takeInterrupt.?(1.U(countBits), retireCount))
      val traceValid = traceCount =/= 0.U
      val traceIssueCount = Wire(UInt(countBits))
      traceIssueCount := issueCount
      val traceOrder = RegInit(0.U(64))
      when(traceValid) { traceOrder := (traceOrder + traceCount).asBits.bits(63, 0).asUInt }
      val tracePc = Wire(Vec(width, UInt(64)))
      val traceInstruction = Wire(Vec(width, UInt(32)))
      val traceFetchTag = Wire(Vec(width, UInt(8)))
      val traceNextPc = Wire(Vec(width, UInt(64)))
      val traceRd = Wire(Vec(width, UInt(5)))
      val traceRdWrite = Wire(Vec(width, Bool()))
      val traceValue = Wire(Vec(width, UInt(64)))
      val traceTrap = Wire(Vec(width, Bool()))
      val traceCause = Wire(Vec(width, UInt(64)))
      val traceTval = Wire(Vec(width, UInt(64)))
      val occupancyBits = parameter.pipelineOccupancyBits
      val pipelineOccupancy = Wire(UInt(occupancyBits))
      val pipelineStall = Wire(Bool())
      pipelineOccupancy := (Seq(instructionCount, decodedCount, issuedCount, resultCount, memoryCount, commitCount) ++ extraCount.toSeq)
        .map(count => (0.U(occupancyBits) + count)).reduce(_ + _).asBits.bits(occupancyBits - 1, 0).asUInt
      pipelineStall := decodedValid & stalled
      for lane <- 0 until width do
        val packet = retirement(lane)
        tracePc(lane) := packet.instruction.pc
        traceInstruction(lane) := packet.instruction.instruction
        traceFetchTag(lane) := packet.instruction.tag
        traceNextPc(lane) := packet.nextPc
        traceRd(lane) := packet.rd
        traceRdWrite(lane) := packet.rdWrite
        traceValue(lane) := packet.rdWrite.?(packet.value, 0.U(64))
        traceTrap(lane) := packet.instruction.fault
        traceCause(lane) := packet.instruction.cause
        traceTval(lane) := packet.instruction.tval
      if parameter.enableInterrupts then
        when(takeInterrupt) {
          tracePc(0) := resumePc.get
          traceInstruction(0) := 0.U(32)
          traceFetchTag(0) := 0.U(8)
          traceNextPc(0) := csr.io.trapVector
          traceRd(0) := 0.U(5)
          traceRdWrite(0) := false.B
          traceValue(0) := 0.U(64)
          traceTrap(0) := true.B
          traceCause(0) := interruptCause
          traceTval(0) := 0.U(64)
        }
      probe.valid <== traceValid
      probe.count <== traceCount
      probe.issueCount <== traceIssueCount
      probe.order <== traceOrder
      probe.pc <== tracePc.asBits.asUInt
      probe.instruction <== traceInstruction.asBits.asUInt
      probe.fetchTag <== traceFetchTag.asBits.asUInt
      probe.nextPc <== traceNextPc.asBits.asUInt
      probe.rd <== traceRd.asBits.asUInt
      probe.rdWrite <== traceRdWrite.asBits.asUInt
      probe.value <== traceValue.asBits.asUInt
      probe.trap <== traceTrap.asBits.asUInt
      probe.cause <== traceCause.asBits.asUInt
      probe.tval <== traceTval.asBits.asUInt
      probe.pipelineOccupancy <== pipelineOccupancy
      probe.pipelineStall <== pipelineStall

