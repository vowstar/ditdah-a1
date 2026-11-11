// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

@generator
object DitDahA1MemoryFabric extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1MemoryFabricIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1MemoryFabric"
  def architecture(parameter: DitDahA1Parameter) =
    parameter.validateFabric()
    val io = summon[Interface[DitDahA1MemoryFabricIO]]
    val arbiter = DitDahA1MemoryArbiter.instantiate(parameter)
    val memory = DitDahA1Memory.instantiate(parameter)
    val axi = DitDahA1Axi.instantiate(parameter)
    val readers = Option.when(parameter.resolvedFabricReadSlots > 0)(DitDahA1ReadQueue.instantiate(parameter))
    arbiter.io.clock := io.clock
    arbiter.io.reset := io.reset
    memory.io.clock := io.clock
    memory.io.reset := io.reset
    axi.io.clock := io.clock
    axi.io.reset := io.reset
    axi.io.hartId := arbiter.io.hartId
    io.writeEvent.foreach(_ :<= axi.io.writeEvent.get)
    val exclusive = readers.map { queue =>
      given ClockScope = ClockScope.posedge(io.clock)
      given ResetScope = ResetScope.syncActiveHigh(io.reset)
      val active = RegInit(false.B)
      val preferRead = RegInit(true.B)
      queue.io.clock := io.clock
      queue.io.reset := io.reset
      val ports = (0 until 2 * parameter.hartCount).map(i => if i % 2 == 0 then io.instruction(i / 2) else io.data(i / 2))
      val ordinary = ports.map { port =>
        val request = port.request.bits
        val device = parameter.memoryRegions.filter(_.device).foldLeft[Referable[Bool]](false.B) { (selected, region) =>
          selected | ((request.address >= region.base.U(64)) & (request.address < (region.base + region.size).U(64)))
        }
        val coherent = if parameter.dCacheWriteback then DitDahA1Memory.dataCacheable(parameter, request.address, 1) else false.B
        val debug = DitDahA1Memory.debugWindow(parameter, request.address, 0.U(3))
        (request.cacheOperation === 0.U(2)) & !request.write & !request.atomic &
          ((request.size <= 3.U(3)) | DitDahA1Axi.lineRead(parameter, request)) & !device & !coherent & !debug
      }
      val readWaiting = ports.indices.map(i => ports(i).request.valid & ordinary(i)).reduce(_ | _)
      val exclusiveWaiting = ports.indices.map(i => ports(i).request.valid & !ordinary(i)).reduce(_ | _)
      val allowRead = !active & (!exclusiveWaiting | preferRead)
      val allowExclusive = queue.io.empty & !(preferRead & readWaiting)
      for i <- ports.indices do
        val port = ports(i)
        val read = queue.io.ports(i)
        val single = arbiter.io.ports(i)
        read.request.bits :<= port.request.bits
        single.request.bits :<= port.request.bits
        read.request.valid := port.request.valid & ordinary(i) & allowRead
        single.request.valid := port.request.valid & !ordinary(i) & allowExclusive
        port.request.ready := ordinary(i).?(read.request.ready & allowRead, single.request.ready & allowExclusive)
        port.response.valid := read.response.valid | single.response.valid
        port.response.bits :<= single.response.bits
        when(read.response.valid) { port.response.bits :<= read.response.bits }
        read.response.ready := port.response.ready
        single.response.ready := port.response.ready
        when(read.request.valid & read.request.ready) { preferRead := false.B }
        when(single.request.valid & single.request.ready) { active := true.B }
        when(single.response.valid & single.response.ready & single.response.bits.last) {
          active := false.B
          preferRead := true.B
        }
      active
    }.getOrElse(true.B)
    if readers.isEmpty then
      for hart <- 0 until parameter.hartCount do
        arbiter.io.ports(2 * hart) :<>= io.instruction(hart)
        arbiter.io.ports(2 * hart + 1) :<>= io.data(hart)
    val serialized = if !parameter.enableDebugMemory then arbiter.io.downstream else
      given ClockScope = ClockScope.posedge(io.clock)
      given ResetScope = ResetScope.syncActiveHigh(io.reset)
      val up = arbiter.io.downstream
      val down = Wire(new MemoryPort(parameter))
      val debug = io.debugMemory.get
      val selected = DitDahA1Memory.debugWindow(parameter, up.request.bits.address, 0.U(3))
      val responseDebug = RegInit(false.B)
      io.debugHart.get := arbiter.io.hartId
      down.request.bits :<= up.request.bits
      debug.request.bits :<= up.request.bits
      down.request.valid := up.request.valid & !selected
      debug.request.valid := up.request.valid & selected
      up.request.ready := selected.?(debug.request.ready, down.request.ready)
      when(up.request.valid & up.request.ready) { responseDebug := selected }
      up.response.valid := responseDebug.?(debug.response.valid, down.response.valid)
      up.response.bits :<= down.response.bits
      when(responseDebug) { up.response.bits :<= debug.response.bits }
      down.response.ready := up.response.ready & !responseDebug
      debug.response.ready := up.response.ready & responseDebug
      down
    val physical = if parameter.dCacheBytes == 0 then
      memory.io.upstream :<>= serialized
      memory.io.downstream
    else
      val coherence = DitDahA1Coherence.instantiate(parameter)
      coherence.io.clock := io.clock
      coherence.io.reset := io.reset
      coherence.io.hartId := arbiter.io.hartId
      io.probe.get :<>= coherence.io.probe
      if parameter.dCacheWriteback then
        coherence.io.upstream :<>= serialized
        memory.io.upstream :<>= coherence.io.downstream
        memory.io.downstream
      else
        memory.io.upstream :<>= serialized
        coherence.io.upstream :<>= memory.io.downstream
        coherence.io.downstream
    val controlled = if !parameter.enableZicbom then physical else
      given ClockScope = ClockScope.posedge(io.clock)
      given ResetScope = ResetScope.syncActiveHigh(io.reset)
      val up = physical
      val down = Wire(new MemoryPort(parameter))
      val completed = RegInit(false.B)
      val tag = Reg(UInt(8))
      val maintenance = up.request.bits.cacheOperation === 3.U(2)
      val ready = io.maintenance.map(_.ready).getOrElse(true.B)
      io.maintenance.foreach { port =>
        port.valid := up.request.valid & maintenance & !completed
        port.bits := up.request.bits.address
      }
      down.request.bits :<= up.request.bits
      down.request.valid := up.request.valid & !maintenance & !completed
      up.request.ready := !completed & maintenance.?(ready, down.request.ready)
      up.response.valid := completed | down.response.valid
      up.response.bits :<= down.response.bits
      when(completed) {
        up.response.bits.data := 0.U(64); up.response.bits.fault := false.B
        up.response.bits.tag := tag; up.response.bits.last := true.B
      }
      down.response.ready := up.response.ready & !completed
      when(up.request.valid & up.request.ready & maintenance) { completed := true.B; tag := up.request.bits.tag }
      when(completed & up.response.ready) { completed := false.B }
      down
    if parameter.localInterruptBase.isEmpty then axi.io.memory :<>= controlled
    else
      given ClockScope = ClockScope.posedge(io.clock)
      given ResetScope = ResetScope.syncActiveHigh(io.reset)
      val localInterrupts = DitDahA1LocalInterrupts.instantiate(parameter)
      val port = controlled
      val base = parameter.localInterruptBase.get
      val selected = (port.request.bits.address >= base.U(64)) & (port.request.bits.address < (base + 65536).U(64))
      val responseLocal = RegInit(false.B)
      localInterrupts.io.clock := io.clock
      localInterrupts.io.reset := io.reset
      localInterrupts.io.timeTick := io.timeTick.get
      io.timeValue.foreach(_ := localInterrupts.io.timeValue.get)
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
    readers.foreach { queue =>
      io.axi.ar.valid := exclusive.?(axi.io.axi.ar.valid, queue.io.ar.valid)
      when(!exclusive) { io.axi.ar.bits :<= queue.io.ar.bits }
      axi.io.axi.ar.ready := io.axi.ar.ready & exclusive
      queue.io.ar.ready := io.axi.ar.ready & !exclusive
      queue.io.r.bits :<= io.axi.r.bits
      queue.io.r.valid := io.axi.r.valid & !exclusive
      axi.io.axi.r.valid := io.axi.r.valid & exclusive
      io.axi.r.ready := exclusive.?(axi.io.axi.r.ready, queue.io.r.ready)
    }
