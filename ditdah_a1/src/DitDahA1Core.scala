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
    io.instruction :<>= frontend.io.memory
    io.data :<>= backend.io.data
    io.status :<= backend.io.status
    layer("DV"):
      probe.valid <== backend.probe.valid
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
    val decodedValid = RegInit(false.B)
    val issuedValid = RegInit(false.B)
    val resultValid = RegInit(false.B)
    val commitValid = RegInit(false.B)
    val decodedPacket = Reg(new DecodedPacket)
    val issuedPacket = Reg(new IssuedPacket)
    val resultPacket = Reg(new ResultPacket)
    val commitPacket = Reg(new ResultPacket)
    val memoryPending = RegInit(false.B)
    val executePending = RegInit(false.B)
    val resumePc = Option.when(parameter.enableInterrupts)(RegInit(parameter.resetVector.U(64)))
    val decode = DitDahA1Decode.instantiate(parameter)
    val issue = DitDahA1Issue.instantiate(parameter)
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
    decode.io.input :<>= io.instruction
    issue.io.input.bits :<= decodedPacket
    execute.io.input.bits :<= issuedPacket
    multiply.io.input.bits :<= issuedPacket
    gpr.io.raddr1 := issue.io.raddr1
    gpr.io.raddr2 := issue.io.raddr2
    issue.io.rdata1 := gpr.io.rdata1
    issue.io.rdata2 := gpr.io.rdata2
    execute.io.csrValue := csr.io.readData
    execute.io.csrLegal := csr.io.legal
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
    val sequentialPc = (retire.bits.instruction.pc + retire.bits.instruction.length).asBits.bits(63, 0).asUInt
    val pmpUpdate = if parameter.pmpEntries == 0 then false.B else
      retire.bits.csrWrite & (((retire.bits.csrAddress >= 0x3a0.U(12)) & (retire.bits.csrAddress <= 0x3ae.U(12))) |
        ((retire.bits.csrAddress >= 0x3b0.U(12)) & (retire.bits.csrAddress <= 0x3ef.U(12))))
    val redirect = takeInterrupt | (retired & (retire.bits.instruction.fault | retire.bits.mret |
      pmpUpdate | retire.bits.fenceI | (retire.bits.nextPc =/= sequentialPc)))
    if parameter.iCacheBytes != 0 then io.invalidate.get := retired & (retire.bits.fenceI | pmpUpdate)
    val commitReady = !commitValid | retired
    val memoryOperation = (resultPacket.load | resultPacket.store) & !resultPacket.instruction.fault
    val resultAdvance = resultValid & (!memoryOperation | (memoryPending & lsu.io.output.valid)) & commitReady & !redirect
    val isMultiply = (issuedPacket.decoded.operation === DitDahA1Isa.Mul.U(DitDahA1Isa.operationBits)) & !issuedPacket.decoded.instruction.fault
    multiply.io.input.valid := issuedValid & isMultiply & !executePending & !redirect
    execute.io.input.valid := issuedValid & (!isMultiply | (executePending & multiply.io.output.valid)) & !redirect
    execute.io.output.ready := (!resultValid | resultAdvance) & !redirect
    multiply.io.output.ready := !issuedValid | (isMultiply & execute.io.output.ready)
    val executed = execute.io.output.valid & execute.io.output.ready
    val destinations = Seq(
      (issuedValid & issuedPacket.decoded.writesRd, issuedPacket.decoded.rd),
      (resultValid & resultPacket.rdWrite & !resultPacket.instruction.fault, resultPacket.rd),
      (commitValid & commitPacket.rdWrite & !commitPacket.instruction.fault, commitPacket.rd)
    )
    val dependency = destinations.map { case (valid, rd) =>
      valid & (rd =/= 0.U(5)) & ((decodedPacket.usesRs1 & (decodedPacket.rs1 === rd)) | (decodedPacket.usesRs2 & (decodedPacket.rs2 === rd)))
    }.reduce(_ | _)
    val stalled = dependency | (decodedPacket.serializing & (issuedValid | resultValid | commitValid))
    issue.io.input.valid := decodedValid & !stalled & !redirect
    issue.io.output.ready := (!issuedValid | executed) & !executePending & !redirect
    val issued = issue.io.output.valid & issue.io.output.ready
    decode.io.output.ready := (!decodedValid | issued) & !redirect
    val decoded = decode.io.output.valid & decode.io.output.ready
    io.redirect := redirect
    io.redirectPc := retire.bits.nextPc
    lsu.io.input.valid := resultValid & memoryOperation & !memoryPending & !commitValid & !redirect
    lsu.io.input.bits :<= resultPacket
    lsu.io.storeAllowed := !commitValid & !redirect
    lsu.io.output.ready := resultValid & memoryPending & commitReady & !redirect
    gpr.io.we := retired & retire.bits.rdWrite
    gpr.io.waddr := retire.bits.rd
    gpr.io.wdata := retire.bits.value
    csr.io.write := retired & retire.bits.csrWrite
    csr.io.writeAddress := retire.bits.csrAddress
    csr.io.writeData := retire.bits.csrData
    csr.io.trap := retired & retire.bits.instruction.fault
    csr.io.trapPc := retire.bits.instruction.pc
    csr.io.trapCause := retire.bits.instruction.cause
    csr.io.trapValue := retire.bits.instruction.tval
    csr.io.mret := retired & retire.bits.mret
    if parameter.enableInterrupts then
      when(retired) { resumePc.get := retire.bits.nextPc }
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
    io.status.sleep := false.B
    io.data :<>= lsu.io.memory
    when(retired) { commitValid := false.B }
    when(resultAdvance) {
      commitValid := true.B
      commitPacket :<= resultPacket
      when(memoryPending) { commitPacket :<= lsu.io.output.bits }
      resultValid := false.B
    }
    when(executed) {
      resultPacket :<= execute.io.output.bits
      when(isMultiply) { resultPacket.value := multiply.io.output.bits }
      resultValid := true.B
      issuedValid := false.B
    }
    // Accepted arithmetic drains before the issued slot is reused.
    when(multiply.io.input.valid & multiply.io.input.ready) { executePending := true.B }
    when(multiply.io.output.valid & multiply.io.output.ready) { executePending := false.B }
    when(issued) { issuedPacket :<= issue.io.output.bits; issuedValid := true.B; decodedValid := false.B }
    when(decoded) { decodedPacket :<= decode.io.output.bits; decodedValid := true.B }
    when(lsu.io.input.valid & lsu.io.input.ready) { memoryPending := true.B }
    when(lsu.io.output.valid & lsu.io.output.ready) { memoryPending := false.B }
    when(redirect) {
      decodedValid := false.B
      issuedValid := false.B
      resultValid := false.B
      commitValid := false.B
    }
    layer("DV"):
      val traceValid = Wire(Bool())
      val traceOrder = RegInit(0.U(64))
      val tracePc = Wire(UInt(64))
      val traceInstruction = Wire(UInt(32))
      val traceNextPc = Wire(UInt(64))
      val traceRd = Wire(UInt(5))
      val traceRdWrite = Wire(Bool())
      val traceValue = Wire(UInt(64))
      val traceTrap = Wire(Bool())
      val traceCause = Wire(UInt(64))
      val traceTval = Wire(UInt(64))
      val pipelineOccupancy = Wire(UInt(3))
      val pipelineStall = Wire(Bool())
      pipelineOccupancy := (decodedValid.?(1.U(3), 0.U(3)) + issuedValid.?(1.U(3), 0.U(3)) + resultValid.?(1.U(3), 0.U(3)) + commitValid.?(1.U(3), 0.U(3))).asBits.bits(2, 0).asUInt
      pipelineStall := decodedValid & stalled
      traceValid := (if parameter.enableInterrupts then retired | takeInterrupt else retired)
      when(if parameter.enableInterrupts then retired | takeInterrupt else retired) { traceOrder := (traceOrder + 1.U(64)).asBits.bits(63, 0).asUInt }
      tracePc := retire.bits.instruction.pc
      traceInstruction := retire.bits.instruction.instruction
      traceNextPc := retire.bits.nextPc
      traceRd := retire.bits.rd
      traceRdWrite := retire.bits.rdWrite
      traceValue := retire.bits.rdWrite.?(retire.bits.value, 0.U(64))
      traceTrap := retire.bits.instruction.fault
      traceCause := retire.bits.instruction.cause
      traceTval := retire.bits.instruction.tval
      if parameter.enableInterrupts then
        when(takeInterrupt) {
          tracePc := resumePc.get
          traceInstruction := 0.U(32)
          traceNextPc := csr.io.trapVector
          traceRd := 0.U(5)
          traceRdWrite := false.B
          traceValue := 0.U(64)
          traceTrap := true.B
          traceCause := interruptCause
          traceTval := 0.U(64)
        }
      probe.valid <== traceValid
      probe.order <== traceOrder
      probe.pc <== tracePc
      probe.instruction <== traceInstruction
      probe.nextPc <== traceNextPc
      probe.rd <== traceRd
      probe.rdWrite <== traceRdWrite
      probe.value <== traceValue
      probe.trap <== traceTrap
      probe.cause <== traceCause
      probe.tval <== traceTval
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
    fetch.io.request.valid := !io.redirect
    fetch.io.request.bits.pc := pc
    fetch.io.request.bits.tag := tag
    fetch.io.cancel := io.redirect
    if parameter.iCacheBytes != 0 then fetch.io.invalidate.get := io.invalidate.get
    io.output :<>= fetch.io.output
    io.memory :<>= fetch.io.memory
    when(fetch.io.request.valid & fetch.io.request.ready) { tag := (tag + 1.U(8)).asBits.bits(7, 0).asUInt }
    when(io.output.valid & io.output.ready) { pc := (pc + io.output.bits.length).asBits.bits(63, 0).asUInt }
    when(io.redirect) { pc := io.redirectPc }
