// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

@generator
object DitDahA1Core extends Generator[DitDahA1Parameter, DitDahA1Layers, DitDahA1CoreIO, DitDahA1Probe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Core"
  def architecture(parameter: DitDahA1Parameter) =
    parameter.validateCore()
    val io = summon[Interface[DitDahA1CoreIO]]
    val probe = summon[ProbeInterface[DitDahA1Probe]]
    val frontend = DitDahA1Frontend.instantiate(parameter)
    val backend = DitDahA1Backend.instantiate(parameter)
    frontend.io.clock := io.clock
    frontend.io.reset := io.reset
    backend.io.clock := io.clock
    backend.io.reset := io.reset
    backend.io.hartId := io.hartId
    if parameter.enableInterrupts then backend.io.interrupts.get :<= io.interrupts.get
    if parameter.pmpEntries != 0 then frontend.io.pmp.get :<= backend.io.pmp.get
    backend.io.instruction :<>= frontend.io.output
    if parameter.iCacheBytes != 0 then frontend.io.invalidate.get := backend.io.invalidate.get
    frontend.io.redirect := backend.io.redirect
    frontend.io.redirectPc := backend.io.redirectPc
    frontend.io.halt := backend.io.status.sleep
    frontend.io.privilege := backend.io.privilege
    io.instruction :<>= frontend.io.memory
    if !parameter.enableTranslation then io.data :<>= backend.io.data
    else
      given ClockScope = ClockScope.posedge(io.clock)
      given ResetScope = ResetScope.syncActiveHigh(io.reset)
      val translation = DitDahA1Translation.instantiate(parameter)
      translation.io.clock := io.clock
      translation.io.reset := io.reset
      translation.io.state :<= backend.io.translationState.get
      translation.io.cancelInstruction := backend.io.redirect
      if parameter.tlbEntries != 0 then translation.io.invalidate.get := backend.io.invalidateTranslation.get
      if parameter.pmpEntries != 0 then translation.io.pmp.get :<= backend.io.pmp.get
      translation.io.ports(0) :<>= frontend.io.translation.get
      translation.io.ports(1) :<>= backend.io.translation.get
      DitDahA1MemoryArbiter.arbitrate(Seq(backend.io.data, translation.io.memory), io.data)
    io.status :<= backend.io.status
    layer("DV"):
      probe.valid <== backend.probe.valid
      probe.count <== backend.probe.count
      probe.issueCount <== backend.probe.issueCount
      probe.order <== backend.probe.order
      probe.pc <== backend.probe.pc
      probe.instruction <== backend.probe.instruction
      probe.nextPc <== backend.probe.nextPc
      probe.rd <== backend.probe.rd
      probe.rdWrite <== backend.probe.rdWrite
      probe.value <== backend.probe.value
      probe.trap <== backend.probe.trap
      probe.cause <== backend.probe.cause
      probe.tval <== backend.probe.tval
      probe.pipelineOccupancy <== backend.probe.pipelineOccupancy
      probe.pipelineStall <== backend.probe.pipelineStall

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
    val decodedPackets = Reg(Vec(width, new DecodedPacket))
    val issuedCount = RegInit(0.U(countBits))
    val issuedValid = issuedCount =/= 0.U
    val issuedPackets = Reg(Vec(width, new IssuedPacket))
    val issuedPacket = issuedPackets(0)
    val resultCount = RegInit(0.U(countBits))
    val resultValid = resultCount =/= 0.U
    val resultPackets = Reg(Vec(width, new ResultPacket))
    val resultPacket = resultPackets(0)
    val memoryCount = RegInit(0.U(countBits))
    val memoryValid = memoryCount =/= 0.U
    val memoryPackets = Reg(Vec(width, new ResultPacket))
    val memoryPacket = memoryPackets(0)
    val commitCount = RegInit(0.U(countBits))
    val commitValid = commitCount =/= 0.U
    val commitPackets = Reg(Vec(width, new ResultPacket))
    val commitPacket = commitPackets(0)
    val memoryPending = RegInit(false.B)
    val executePending = RegInit(false.B)
    val resumePc = Option.when(parameter.enableInterrupts)(RegInit(parameter.resetVector.U(64)))
    val sleep = Option.when(parameter.enableInterrupts)(RegInit(false.B))
    val sleeping = if parameter.enableInterrupts then sleep.get else false.B
    val decode = DitDahA1Decode.instantiate(parameter)
    val decodes = decode +: Seq.fill(width - 1)(DitDahA1Decode.instantiate(parameter))
    val issue = DitDahA1Issue.instantiate(parameter)
    val issues = issue +: Seq.fill(width - 1)(DitDahA1Issue.instantiate(parameter))
    val execute = DitDahA1Execute.instantiate(parameter)
    val multiply = DitDahA1Multiply.instantiate(parameter)
    val commit = DitDahA1Commit.instantiate(parameter)
    val gpr = DitDahA1Gpr.instantiate(parameter)
    val csr = DitDahA1Csr.instantiate(parameter)
    val lsu = DitDahA1Lsu.instantiate(parameter)
    if parameter.pmpEntries != 0 then
      io.pmp.get :<= csr.io.pmp.get
      lsu.io.pmp.get :<= csr.io.pmp.get
    gpr.io.clock := io.clock
    gpr.io.reset := io.reset
    csr.io.clock := io.clock
    csr.io.reset := io.reset
    csr.io.hartId := io.hartId
    if parameter.enableInterrupts then csr.io.interrupts.get :<= io.interrupts.get
    lsu.io.clock := io.clock
    lsu.io.reset := io.reset
    multiply.io.clock := io.clock
    multiply.io.reset := io.reset
    execute.io.input.bits :<= issuedPacket
    multiply.io.input.bits :<= issuedPacket
    execute.io.csrValue := csr.io.readData
    execute.io.csrLegal := csr.io.legal
    execute.io.privilege := csr.io.privilege
    execute.io.wfiLegal := csr.io.wfiLegal
    execute.io.sretLegal := csr.io.sretLegal
    execute.io.sfenceLegal := csr.io.sfenceLegal
    if parameter.enableTranslation then
      io.translationState.get :<= csr.io.translationState.get
      io.translation.get :<>= lsu.io.translation.get
    io.privilege := csr.io.privilege
    lsu.io.privilege := csr.io.dataPrivilege
    csr.io.readAddress := execute.io.csrAddress
    // Completed data operations keep ownership until their architectural event.
    val takeInterrupt = if parameter.enableInterrupts then
      csr.io.interruptPending.get & !memoryPending & !(commitValid & (commitPacket.load | commitPacket.store | commitPacket.instruction.fault))
    else false.B
    val interruptCause = if parameter.enableInterrupts then csr.io.interruptCause.get else 0.U(64)
    commit.io.input.valid := (if parameter.enableInterrupts then commitValid & !takeInterrupt else commitValid)
    commit.io.input.bits :<= commitPacket
    commit.io.output.ready := true.B
    commit.io.trapVector := csr.io.trapVector
    commit.io.returnPc := csr.io.returnPc
    val retire = commit.io.output
    val retired = retire.valid & retire.ready
    val retireCount = retired.?(commitCount, 0.U(countBits))
    val retirement = Wire(Vec(width, new ResultPacket))
    retirement(0) :<= retire.bits
    for lane <- 1 until width do
      retirement(lane) :<= commitPackets(lane)
      retirement(lane).rdWrite := commitPackets(lane).rdWrite & (commitPackets(lane).rd =/= 0.U(5))
    val sequentialPc = (retire.bits.instruction.pc + retire.bits.instruction.length).asBits.bits(63, 0).asUInt
    val enterWfi = retired & retire.bits.wfi & !retire.bits.instruction.fault
    val pmpUpdate = if parameter.pmpEntries == 0 then false.B else
      retire.bits.csrWrite & (((retire.bits.csrAddress >= 0x3a0.U(12)) & (retire.bits.csrAddress <= 0x3ae.U(12))) |
        ((retire.bits.csrAddress >= 0x3b0.U(12)) & (retire.bits.csrAddress <= 0x3ef.U(12))))
    val translationUpdate = if parameter.enableTranslation then
      retire.bits.sfenceVma | (retire.bits.csrWrite & (retire.bits.csrAddress === 0x180.U(12))) else false.B
    io.invalidateTranslation.foreach(_ := retired & (translationUpdate | pmpUpdate))
    val redirect = takeInterrupt | (retired & (retire.bits.instruction.fault | retire.bits.mret | retire.bits.sret |
      pmpUpdate | translationUpdate | retire.bits.fenceI | (retire.bits.nextPc =/= sequentialPc))) | enterWfi
    if parameter.iCacheBytes != 0 then io.invalidate.get := retired & (retire.bits.fenceI | pmpUpdate | translationUpdate)
    val commitReady = !commitValid | retired
    val memoryOperation = (resultPacket.load | resultPacket.store) & !resultPacket.instruction.fault
    val memoryCompletion = (memoryPacket.load | memoryPacket.store) & !memoryPacket.instruction.fault
    val completion = Wire(new ResultPacket)
    completion :<= memoryPacket
    when(memoryPending) { completion :<= lsu.io.output.bits }
    val memoryAdvance = memoryValid & (!memoryCompletion | (memoryPending & lsu.io.output.valid)) & commitReady & !redirect
    val resultAdvance = resultValid & (!memoryValid | memoryAdvance) &
      (!memoryOperation | (lsu.io.input.valid & lsu.io.input.ready)) & !redirect
    val isMultiply = (issuedPacket.decoded.operation === DitDahA1Isa.Mul.U(DitDahA1Isa.operationBits)) & !issuedPacket.decoded.instruction.fault
    multiply.io.input.valid := issuedValid & isMultiply & !executePending & !redirect
    execute.io.input.valid := issuedValid & (!isMultiply | (executePending & multiply.io.output.valid)) & !redirect
    execute.io.output.ready := (!resultValid | resultAdvance) & !redirect
    multiply.io.output.ready := !issuedValid | (isMultiply & execute.io.output.ready)
    val executed = execute.io.output.valid & execute.io.output.ready
    val execution = Wire(Vec(width, new ResultPacket))
    execution(0) :<= execute.io.output.bits
    when(isMultiply) { execution(0).value := multiply.io.output.bits }
    for lane <- 1 until width do DitDahA1Alu.result(issuedPackets(lane), execution(lane))
    val destinations = (0 until width).map { lane =>
      val packet = commitPackets(lane)
      ((lane.U < commitCount) & packet.rdWrite, packet.rd, !packet.instruction.fault, packet.value)
    } ++ (0 until width).map { lane =>
      val packet = memoryPackets(lane)
      val completed = if lane == 0 then completion else packet
      ((lane.U < memoryCount) & packet.rdWrite, packet.rd,
        (if lane == 0 then !memoryCompletion | (memoryPending & lsu.io.output.valid) else true.B) & !completed.instruction.fault, completed.value)
    } ++ (0 until width).map { lane =>
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
    val available = (!issuedValid | executed) & !executePending & !redirect & !sleeping
    val prefix = Wire(Vec(width, Bool()))
    val simple = (0 until width).map { lane =>
      import DitDahA1Isa.*
      !decodedPackets(lane).instruction.fault & Seq(Lui, Auipc, Addi, Add, AluImmediate, AluRegister,
        AluWordImmediate, AluWordRegister).map(op => decodedPackets(lane).operation === op.U(operationBits)).reduce(_ | _)
    }
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
      val blocked = blocked1 | blocked2 | (packet.serializing & older)
      val conflict = (0 until lane).map { previous =>
        val writer = decodedPackets(previous)
        writer.writesRd & (writer.rd =/= 0.U(5)) &
          ((packet.usesRs1 & (writer.rd === packet.rs1)) | (packet.usesRs2 & (writer.rd === packet.rs2)) |
            (packet.writesRd & (writer.rd === packet.rd)))
      }.foldLeft[Referable[Bool]](false.B)(_ | _)
      prefix(lane) := (lane.U < decodedCount) & !blocked &
        (if lane == 0 then true.B else prefix(lane - 1) & simple(0) & simple(lane) & !conflict)
      unit.io.input.valid := prefix(lane) & !redirect & !sleeping
      unit.io.output.ready := available
      blocked
    }
    val stalled = dependencies.head
    val issueCount = Wire(UInt(countBits))
    issueCount := available.?((0 until width).map(lane => prefix(lane).?(1.U(countBits), 0.U(countBits))).reduce(_ + _)
      .asBits.bits(countBits - 1, 0).asUInt, 0.U(countBits))
    val issued = issueCount =/= 0.U
    val decodedFree = width.U(countBits) - (decodedCount - issueCount)
    val decodeCount = (!redirect & !sleeping).?((instructionCount <= decodedFree).?(instructionCount, decodedFree), 0.U(countBits))
      .asBits.bits(countBits - 1, 0).asUInt
    val decodedInput = Wire(Vec(width, new DecodedPacket))
    for lane <- 0 until width do
      decodes(lane).io.input.bits :<= instructionPackets(lane)
      decodes(lane).io.input.valid := (lane.U < instructionCount) & !redirect & !sleeping
      decodes(lane).io.output.ready := lane.U < decodeCount
      decodedInput(lane) :<= decodes(lane).io.output.bits
    io.instruction.ready := !redirect & !sleeping & (io.instruction.bits.count <= width.U - (instructionCount - decodeCount))
    val received = io.instruction.valid & io.instruction.ready
    io.redirect := redirect
    io.redirectPc := retire.bits.nextPc
    lsu.io.input.valid := resultValid & memoryOperation & !memoryPending & !memoryValid & !commitValid & !redirect
    lsu.io.input.bits :<= resultPacket
    lsu.io.storeAllowed := !memoryValid & !commitValid & !redirect
    lsu.io.output.ready := memoryValid & memoryPending & commitReady & !redirect
    for lane <- 0 until width do
      gpr.io.we(lane) := (lane.U < retireCount) & retirement(lane).rdWrite
      gpr.io.waddr(lane) := retirement(lane).rd
      gpr.io.wdata(lane) := retirement(lane).value
    csr.io.write := retired & retire.bits.csrWrite
    csr.io.writeAddress := retire.bits.csrAddress
    csr.io.writeData := retire.bits.csrData
    csr.io.trap := retired & retire.bits.instruction.fault
    csr.io.trapPc := retire.bits.instruction.pc
    csr.io.trapCause := retire.bits.instruction.cause
    csr.io.trapValue := retire.bits.instruction.tval
    csr.io.mret := retired & retire.bits.mret
    csr.io.sret := retired & retire.bits.sret
    if parameter.enableInterrupts then
      sleep.get := (sleep.get | enterWfi) & !csr.io.wakeup.get & !csr.io.trap
      for lane <- 0 until width do
        when(retired & (retireCount === (lane + 1).U)) { resumePc.get := retirement(lane).nextPc }
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
      memoryCount := 0.U
    }
    when(resultAdvance) { memoryCount := resultCount; memoryPackets :<= resultPackets; resultCount := 0.U }
    when(executed) { resultPackets :<= execution; resultCount := issuedCount; issuedCount := 0.U }
    // Accepted arithmetic drains before the issued group is reused.
    when(multiply.io.input.valid & multiply.io.input.ready) { executePending := true.B }
    when(multiply.io.output.valid & multiply.io.output.ready) { executePending := false.B }
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
    when(lsu.io.input.valid & lsu.io.input.ready) { memoryPending := true.B }
    when(lsu.io.output.valid & lsu.io.output.ready) { memoryPending := false.B }
    when(redirect) {
      instructionCount := 0.U
      decodedCount := 0.U
      issuedCount := 0.U
      resultCount := 0.U
      memoryCount := 0.U
      commitCount := 0.U
    }
    layer("DV"):
      val traceCount = Wire(UInt(countBits))
      traceCount := takeInterrupt.?(1.U(countBits), retireCount)
      val traceValid = traceCount =/= 0.U
      val traceIssueCount = Wire(UInt(countBits))
      traceIssueCount := issueCount
      val traceOrder = RegInit(0.U(64))
      when(traceValid) { traceOrder := (traceOrder + traceCount).asBits.bits(63, 0).asUInt }
      val tracePc = Wire(Vec(width, UInt(64)))
      val traceInstruction = Wire(Vec(width, UInt(32)))
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
      pipelineOccupancy := Seq(instructionCount, decodedCount, issuedCount, resultCount, memoryCount, commitCount)
        .map(count => (0.U(occupancyBits) + count)).reduce(_ + _).asBits.bits(occupancyBits - 1, 0).asUInt
      pipelineStall := decodedValid & stalled
      for lane <- 0 until width do
        val packet = retirement(lane)
        tracePc(lane) := packet.instruction.pc
        traceInstruction(lane) := packet.instruction.instruction
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
      probe.nextPc <== traceNextPc.asBits.asUInt
      probe.rd <== traceRd.asBits.asUInt
      probe.rdWrite <== traceRdWrite.asBits.asUInt
      probe.value <== traceValue.asBits.asUInt
      probe.trap <== traceTrap.asBits.asUInt
      probe.cause <== traceCause.asBits.asUInt
      probe.tval <== traceTval.asBits.asUInt
      probe.pipelineOccupancy <== pipelineOccupancy
      probe.pipelineStall <== pipelineStall

@generator
object DitDahA1Frontend extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1FrontendIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Frontend"
  def architecture(parameter: DitDahA1Parameter) =
    parameter.validateFrontend()
    val io = summon[Interface[DitDahA1FrontendIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val pc = RegInit(parameter.resetVector.U(64))
    val tag = RegInit(0.U(8))
    val fetch = DitDahA1Fetch.instantiate(parameter)
    if parameter.pmpEntries != 0 then fetch.io.pmp.get :<= io.pmp.get
    fetch.io.clock := io.clock
    fetch.io.reset := io.reset
    fetch.io.privilege := io.privilege
    if parameter.enableTranslation then io.translation.get :<>= fetch.io.translation.get
    fetch.io.request.valid := !io.redirect & !io.halt
    fetch.io.request.bits.pc := pc
    fetch.io.request.bits.tag := tag
    fetch.io.cancel := io.redirect
    if parameter.iCacheBytes != 0 then fetch.io.invalidate.get := io.invalidate.get
    io.memory :<>= fetch.io.memory
    val width = parameter.issueWidth
    val words = parameter.fetchWords
    val capacity = parameter.frontendCapacity
    val countBits = 32 - Integer.numberOfLeadingZeros(capacity + words)
    val queued = RegInit(0.U(countBits))
    val buffer = Reg(Vec(capacity, new FetchPacket))
    val held = RegInit(0.U(32 - Integer.numberOfLeadingZeros(width)))
    val pending = RegInit(false.B)
    val pendingPc = Reg(UInt(64))
    val reserved = Reg(UInt(parameter.fetchCountBits))
    val faultPending = RegInit(false.B)
    val flush = io.redirect | io.invalidate.getOrElse(false.B)
    val returned = fetch.io.output.valid & !flush
    val fetched = fetch.io.output.bits
    val incoming = Wire(Vec(words, new FetchPacket))
    for i <- 0 until words do
      incoming(i).pc := (fetched.pc + (4 * i).U(64)).asBits.bits(63, 0).asUInt
      incoming(i).tag := (fetched.tag + i.U(8)).asBits.bits(7, 0).asUInt
      incoming(i).instruction := (if i == 0 then fetched.instruction else fetched.following.get(i - 1))
      incoming(i).length := 4.U(3)
      incoming(i).fault := (if i == 0 then fetched.fault else false.B)
      incoming(i).cause := (if i == 0 then fetched.cause else 0.U(64))
      incoming(i).tval := (if i == 0 then fetched.tval else 0.U(64))
    val returnedCount = returned.?(fetched.count.getOrElse(1.U(1)), 0.U(parameter.fetchCountBits))
    val available = (queued + returnedCount).asBits.bits(countBits - 1, 0).asUInt
    val view = Wire(Vec(capacity + words, new FetchPacket))
    for i <- 0 until capacity + words do
      view(i) :<= incoming.ref((i.U(countBits) - queued).asBits.bits(countBits - 1, 0).asUInt)
      if i < capacity then when(i.U(countBits) < queued) { view(i) :<= buffer(i) }
    val offered = (held =/= 0.U).?(held, (available >= width.U).?(width.U, available))
      .asBits.bits(31 - Integer.numberOfLeadingZeros(width), 0).asUInt
    val take = (io.output.valid & io.output.ready).?(offered, 0.U(countBits))
    val remaining = (available - take).asBits.bits(countBits - 1, 0).asUInt
    io.output.valid := (available =/= 0.U) & !flush
    io.output.bits.count := offered
    for i <- 0 until width do io.output.bits.packets(i) :<= view(i)
    fetch.io.output.ready := !flush
    val expected = if words == 1 then 1.U(parameter.fetchCountBits) else
      (words.U(parameter.fetchCountBits) - pc.asBits.bits(Integer.numberOfTrailingZeros(words) + 1, 2).asUInt)
        .asBits.bits(parameter.fetchCountBits - 1, 0).asUInt
    val owned = remaining + (pending & !returned).?(reserved, 0.U(parameter.fetchCountBits))
    val queuedFault = (0 until capacity).map(i => (i.U(countBits) < queued) & buffer(i).fault).reduce(_ | _)
    fetch.io.request.valid := !flush & !io.halt & !faultPending & !queuedFault & !(returned & fetched.fault) &
      (owned + expected <= capacity.U)
    when(!flush) {
      queued := remaining
      held := (io.output.valid & !io.output.ready).?(offered, 0.U)
      for i <- 0 until capacity do
        when(i.U(countBits) < remaining) { buffer(i) :<= view.ref((take + i.U(countBits)).asBits.bits(countBits - 1, 0).asUInt) }
    }
    when(io.output.valid & io.output.ready) {
      for i <- 0 until width do
        when((i.U < offered) & view(i).fault) { faultPending := true.B }
    }
    when(returned) {
      pending := false.B
      when(returnedCount < reserved) { pc := (fetched.pc + (returnedCount << 2)).asBits.bits(63, 0).asUInt }
    }
    when(fetch.io.request.valid & fetch.io.request.ready) {
      pending := true.B
      pendingPc := pc
      reserved := expected
      pc := (pc + (expected << 2)).asBits.bits(63, 0).asUInt
      tag := (tag + expected).asBits.bits(7, 0).asUInt
    }
    when(flush) {
      pc := (queued =/= 0.U).?(buffer(0).pc, pending.?(pendingPc, pc))
      queued := 0.U
      held := 0.U
      pending := false.B
    }
    when(io.redirect) { pc := io.redirectPc; faultPending := false.B }
