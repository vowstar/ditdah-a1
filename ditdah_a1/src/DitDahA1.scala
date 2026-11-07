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
    val processorReset = if !parameter.enableJtag then io.reset else
      val dtm = DitDahA1JtagDtm.instantiate(parameter)
      val bridge = DitDahA1DmiBridge.instantiate(parameter)
      val dm = DitDahA1DebugModule.instantiate(parameter)
      val pins = io.jtag.get
      dtm.io.tck := pins.tck
      dtm.io.reset := io.reset
      dtm.io.trstN := pins.trstN
      dtm.io.tms := pins.tms
      dtm.io.tdi := pins.tdi
      pins.tdo := dtm.io.tdo
      pins.tdoEnable := dtm.io.tdoEnable
      bridge.io.clock := io.clock
      bridge.io.tck := pins.tck
      bridge.io.reset := io.reset
      bridge.io.upstream :<>= dtm.io.dmi
      dm.io.clock := io.clock
      dm.io.reset := DebugReset.release(io.clock, io.reset)
      dm.io.dmi :<>= bridge.io.downstream
      dm.io.memory :<>= fabric.io.debugMemory.get
      dm.io.memoryHart := fabric.io.debugHart.get
      val requestedReset = Wire(new DebugReset.Signal)
      requestedReset.value := (io.reset.asBool | io.systemReset.get | dm.io.ndmreset).asReset
      val reset = DebugReset.release(io.clock, requestedReset.value)
      dm.io.hartsReset := reset.asBool
      io.systemResetActive.get := reset.asBool
      for (core, hart) <- cores.zipWithIndex do
        core.io.debug.get.haltReq := dm.io.harts(hart).haltReq
        core.io.debug.get.entryPc := dm.io.harts(hart).entryPc
        core.io.debug.get.exceptionPc := dm.io.harts(hart).exceptionPc
        dm.io.harts(hart).mode := core.io.debug.get.mode
      reset
    for (core, hart) <- cores.zipWithIndex do
      core.io.clock := io.clock
      core.io.reset := processorReset
      core.io.hartId := hart.U(4)
      core.io.timeValue.foreach(_ := (if parameter.localInterruptBase.nonEmpty then fabric.io.timeValue.get else io.timeValue.get))
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
        cache.io.reset := processorReset
        cache.io.upstream :<>= core.io.data
        fabric.io.data(hart) :<>= cache.io.downstream
        cache.io.probe :<>= fabric.io.probe.get(hart)
    fabric.io.clock := io.clock
    fabric.io.reset := processorReset
    if parameter.localInterruptBase.nonEmpty then fabric.io.timeTick.get := io.timeTick.get
    if parameter.l2CacheBytes == 0 then io.axi :<>= fabric.io.axi
    else
      val sharedCache = DitDahA1SharedCache.instantiate(parameter)
      sharedCache.io.clock := io.clock
      sharedCache.io.reset := processorReset
      sharedCache.io.upstream :<>= fabric.io.axi
      io.axi :<>= sharedCache.io.downstream
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
    val readers = Option.when(parameter.resolvedFabricReadSlots > 0)(DitDahA1ReadQueue.instantiate(parameter))
    arbiter.io.clock := io.clock
    arbiter.io.reset := io.reset
    memory.io.clock := io.clock
    memory.io.reset := io.reset
    axi.io.clock := io.clock
    axi.io.reset := io.reset
    axi.io.hartId := arbiter.io.hartId
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
