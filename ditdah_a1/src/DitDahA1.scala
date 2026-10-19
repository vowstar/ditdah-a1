// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

@generator
object DitDahA1Module extends Generator[DitDahA1Parameter, DitDahA1Layers, DitDahA1IO, DitDahA1SystemProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1"
  def architecture(parameter: DitDahA1Parameter) =
    parameter.validateRtl()
    val io = summon[Interface[DitDahA1IO]]
    val cores = Seq.tabulate(parameter.hartCount) { hart =>
      given sourcecode.Name.Machine = sourcecode.Name.Machine(s"core_$hart")
      DitDahA1Core.instantiate(parameter)
    }
    val fabric = DitDahA1MemoryFabric.instantiate(parameter)
    for (core, hart) <- cores.zipWithIndex do
      core.io.clock := io.clock
      core.io.reset := io.reset
      core.io.hartId := hart.U(4)
      if parameter.enableInterrupts then
        core.io.interrupts.get :<= io.interrupts.get(hart)
        if parameter.localInterruptBase.nonEmpty then
          core.io.interrupts.get.software := io.interrupts.get(hart).software | fabric.io.localInterrupts.get(hart).software
          core.io.interrupts.get.timer := io.interrupts.get(hart).timer | fabric.io.localInterrupts.get(hart).timer
      fabric.io.instruction(hart) :<>= core.io.instruction
      if parameter.dCacheBytes == 0 then fabric.io.data(hart) :<>= core.io.data
      else
        given sourcecode.Name.Machine = sourcecode.Name.Machine(s"data_cache_$hart")
        val cache = DitDahA1DataCache.instantiate(parameter)
        cache.io.clock := io.clock
        cache.io.reset := io.reset
        cache.io.upstream :<>= core.io.data
        fabric.io.data(hart) :<>= cache.io.downstream
        cache.io.invalidate :<>= fabric.io.invalidate.get(hart)
    fabric.io.clock := io.clock
    fabric.io.reset := io.reset
    if parameter.localInterruptBase.nonEmpty then fabric.io.timeTick.get := io.timeTick.get
    io.axi :<>= fabric.io.axi
    io.status.trap := cores.map[Referable[Bool]](_.io.status.trap).reduce(_ | _)
    io.status.busy := cores.map[Referable[Bool]](_.io.status.busy).reduce(_ | _)
    io.status.sleep := cores.map[Referable[Bool]](_.io.status.sleep).reduce(_ & _)

@generator
object DitDahA1MemoryFabric extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1MemoryFabricIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1MemoryFabric"
  def architecture(parameter: DitDahA1Parameter) =
    parameter.validateFabric()
    val io = summon[Interface[DitDahA1MemoryFabricIO]]
    val arbiter = DitDahA1MemoryArbiter.instantiate(parameter)
    val memory = DitDahA1Memory.instantiate(parameter)
    val axi = DitDahA1Axi.instantiate(parameter)
    arbiter.io.clock := io.clock
    arbiter.io.reset := io.reset
    memory.io.clock := io.clock
    memory.io.reset := io.reset
    axi.io.clock := io.clock
    axi.io.reset := io.reset
    axi.io.hartId := arbiter.io.hartId
    for hart <- 0 until parameter.hartCount do
      arbiter.io.ports(2 * hart) :<>= io.instruction(hart)
      arbiter.io.ports(2 * hart + 1) :<>= io.data(hart)
    memory.io.upstream :<>= arbiter.io.downstream
    val physical = if parameter.dCacheBytes == 0 then memory.io.downstream else
      val coherence = DitDahA1Coherence.instantiate(parameter)
      coherence.io.clock := io.clock
      coherence.io.reset := io.reset
      coherence.io.upstream :<>= memory.io.downstream
      io.invalidate.get :<>= coherence.io.invalidate
      coherence.io.downstream
    if parameter.localInterruptBase.isEmpty then axi.io.memory :<>= physical
    else
      given ClockScope = ClockScope.posedge(io.clock)
      given ResetScope = ResetScope.syncActiveHigh(io.reset)
      val localInterrupts = DitDahA1LocalInterrupts.instantiate(parameter)
      val port = physical
      val base = parameter.localInterruptBase.get
      val selected = (port.request.bits.address >= base.U(64)) & (port.request.bits.address < (base + 65536).U(64))
      val responseLocal = RegInit(false.B)
      localInterrupts.io.clock := io.clock
      localInterrupts.io.reset := io.reset
      localInterrupts.io.timeTick := io.timeTick.get
      io.localInterrupts.get :<= localInterrupts.io.interrupts
      axi.io.memory.request.bits :<= port.request.bits
      localInterrupts.io.memory.request.bits :<= port.request.bits
      axi.io.memory.request.valid := port.request.valid & !selected
      localInterrupts.io.memory.request.valid := port.request.valid & selected
      port.request.ready := selected.?(localInterrupts.io.memory.request.ready, axi.io.memory.request.ready)
      when(port.request.valid & port.request.ready) { responseLocal := selected }
      port.response.valid := responseLocal.?(localInterrupts.io.memory.response.valid, axi.io.memory.response.valid)
      port.response.bits :<= axi.io.memory.response.bits
      when(responseLocal) { port.response.bits :<= localInterrupts.io.memory.response.bits }
      axi.io.memory.response.ready := port.response.ready & !responseLocal
      localInterrupts.io.memory.response.ready := port.response.ready & responseLocal
    io.axi :<>= axi.io.axi
