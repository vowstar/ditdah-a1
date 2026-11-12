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
    io.reservation.foreach(_ :<>= backend.io.reservation.get)
    backend.io.timeValue.foreach(_ := io.timeValue.get)
    backend.io.debug.foreach { debug =>
      debug.haltReq := io.debug.get.haltReq
      debug.entryPc := io.debug.get.entryPc
      debug.exceptionPc := io.debug.get.exceptionPc
      io.debug.get.mode := debug.mode
    }
    if parameter.enableInterrupts then backend.io.interrupts.get :<= io.interrupts.get
    if parameter.pmpEntries != 0 then frontend.io.pmp.get :<= backend.io.pmp.get
    backend.io.instruction :<>= frontend.io.output
    frontend.io.backendIdle.foreach(_ := backend.io.idle.get)
    if parameter.iCacheBytes != 0 then frontend.io.invalidate.get := backend.io.invalidate.get
    frontend.io.redirect := backend.io.redirect
    frontend.io.redirectPc := backend.io.redirectPc
    frontend.io.prediction.foreach(_ :<= backend.io.prediction.get)
    frontend.io.halt := backend.io.status.sleep
    if parameter.enableJtag then frontend.io.halt := backend.io.status.sleep | (io.debug.get.haltReq & !backend.io.debug.get.mode)
    frontend.io.privilege := backend.io.privilege
    frontend.io.debugMode.foreach(_ := backend.io.debug.get.mode)
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
      if parameter.hasTranslationCache then translation.io.invalidate.get := backend.io.invalidateTranslation.get
      if parameter.preciseTranslationMaintenance then translation.io.maintenance.get :<= backend.io.translationMaintenance.get
      if parameter.pmpEntries != 0 then translation.io.pmp.get :<= backend.io.pmp.get
      translation.io.ports(0) :<>= frontend.io.translation.get
      translation.io.ports(1) :<>= backend.io.translation.get
      if parameter.loadQueueEntries == 1 then
        DitDahA1MemoryArbiter.arbitrate(parameter, Seq(backend.io.data, translation.io.memory), io.data)
      else DitDahA1MemoryArbiter.dataTranslation(backend.io.data, translation.io.memory, io.data)
    io.status :<= backend.io.status
    layer("DV"):
      probe.valid <== backend.probe.valid
      probe.count <== backend.probe.count
      probe.issueCount <== backend.probe.issueCount
      probe.order <== backend.probe.order
      probe.pc <== backend.probe.pc
      probe.instruction <== backend.probe.instruction
      probe.fetchTag <== backend.probe.fetchTag
      probe.nextPc <== backend.probe.nextPc
      probe.rd <== backend.probe.rd
      probe.rdWrite <== backend.probe.rdWrite
      probe.value <== backend.probe.value
      probe.trap <== backend.probe.trap
      probe.cause <== backend.probe.cause
      probe.tval <== backend.probe.tval
      probe.pipelineOccupancy <== backend.probe.pipelineOccupancy
      probe.pipelineStall <== backend.probe.pipelineStall

