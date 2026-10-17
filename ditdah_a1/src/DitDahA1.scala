// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

@generator
object DitDahA1Module extends Generator[DitDahA1Parameter, DitDahA1Layers, DitDahA1IO, DitDahA1Probe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1"
  def architecture(parameter: DitDahA1Parameter) =
    parameter.validateRtl()
    val io = summon[Interface[DitDahA1IO]]
    val probe = summon[ProbeInterface[DitDahA1Probe]]
    val core = DitDahA1Core.instantiate(parameter)
    val fabric = DitDahA1MemoryFabric.instantiate(parameter)
    core.io.clock := io.clock
    core.io.reset := io.reset
    if parameter.enableInterrupts then core.io.interrupts.get :<= io.interrupts.get
    fabric.io.clock := io.clock
    fabric.io.reset := io.reset
    fabric.io.instruction :<>= core.io.instruction
    fabric.io.data :<>= core.io.data
    io.axi :<>= fabric.io.axi
    io.status :<= core.io.status
    layer("DV"):
      probe.valid <== core.probe.valid
      probe.order <== core.probe.order
      probe.pc <== core.probe.pc
      probe.instruction <== core.probe.instruction
      probe.nextPc <== core.probe.nextPc
      probe.rd <== core.probe.rd
      probe.rdWrite <== core.probe.rdWrite
      probe.value <== core.probe.value
      probe.trap <== core.probe.trap
      probe.cause <== core.probe.cause
      probe.tval <== core.probe.tval
      probe.pipelineOccupancy <== core.probe.pipelineOccupancy
      probe.pipelineStall <== core.probe.pipelineStall

@generator
object DitDahA1MemoryFabric extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1MemoryFabricIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1MemoryFabric"
  def architecture(parameter: DitDahA1Parameter) =
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
    arbiter.io.instruction :<>= io.instruction
    arbiter.io.data :<>= io.data
    memory.io.upstream :<>= arbiter.io.downstream
    axi.io.memory :<>= memory.io.downstream
    io.axi :<>= axi.io.axi
