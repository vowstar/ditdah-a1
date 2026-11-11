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
    val writes = Option.when(parameter.enableA)(Seq.fill(1 + (if parameter.dCacheWriteback then parameter.hartCount else 0))(
      Wire(new MemoryWriteEvent)))
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
        cache.io.writeEvent.foreach(event => writes.get(hart + 1) :<= event)
    fabric.io.clock := io.clock
    fabric.io.reset := processorReset
    if parameter.localInterruptBase.nonEmpty then fabric.io.timeTick.get := io.timeTick.get
    if parameter.l2CacheBytes == 0 then io.axi :<>= fabric.io.axi
    else
      val sharedCache = DitDahA1SharedCache.instantiate(parameter)
      sharedCache.io.clock := io.clock
      sharedCache.io.reset := processorReset
      sharedCache.io.upstream :<>= fabric.io.axi
      sharedCache.io.maintenance.foreach(_ :<>= fabric.io.maintenance.get)
      io.axi :<>= sharedCache.io.downstream
    writes.foreach { events =>
      events.head :<= fabric.io.writeEvent.get
      for (core, hart) <- cores.zipWithIndex do
        val reservation = core.io.reservation.get
        reservation.begin := io.axi.ar.valid & io.axi.ar.ready & io.axi.ar.bits.lock & (io.axi.ar.bits.id === hart.U(parameter.axiIdBits))
        reservation.invalidate := events.map(event => event.valid & (event.address === reservation.address) &
          ((event.mask.asBits & reservation.mask.asBits) =/= 0.B(8))).reduce(_ | _)
    }
    io.status.trap := cores.map[Referable[Bool]](_.io.status.trap).reduce(_ | _)
    io.status.busy := cores.map[Referable[Bool]](_.io.status.busy).reduce(_ | _)
    io.status.sleep := cores.map[Referable[Bool]](_.io.status.sleep).reduce(_ & _)

