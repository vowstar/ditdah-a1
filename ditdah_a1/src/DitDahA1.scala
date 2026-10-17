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
      if parameter.enableInterrupts then core.io.interrupts.get :<= io.interrupts.get(hart)
      fabric.io.instruction(hart) :<>= core.io.instruction
      fabric.io.data(hart) :<>= core.io.data
    fabric.io.clock := io.clock
    fabric.io.reset := io.reset
    io.axi :<>= fabric.io.axi
    io.status.trap := cores.map[Referable[Bool]](_.io.status.trap).reduce(_ | _)
    io.status.busy := cores.map[Referable[Bool]](_.io.status.busy).reduce(_ | _)
    io.status.sleep := cores.map[Referable[Bool]](_.io.status.sleep).reduce(_ & _)

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
    for hart <- 0 until parameter.hartCount do
      arbiter.io.ports(2 * hart) :<>= io.instruction(hart)
      arbiter.io.ports(2 * hart + 1) :<>= io.data(hart)
    memory.io.upstream :<>= arbiter.io.downstream
    axi.io.memory :<>= memory.io.downstream
    io.axi :<>= axi.io.axi
