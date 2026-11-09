// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1CoherenceIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val hartId = Flipped(UInt(4))
  val upstream = Flipped(new MemoryPort(parameter))
  val downstream = Aligned(new MemoryPort(parameter))
  val probe = Aligned(Vec(parameter.hartCount, new CacheProbePort))

@generator
object DitDahA1Coherence extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1CoherenceIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Coherence"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1CoherenceIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val up = io.upstream
    val down = io.downstream
    val request = up.request.bits
    val state = RegInit(0.U(3))
    val pending = RegInit(0.B(parameter.hartCount))
    val sent = RegInit(0.B(parameter.hartCount))
    val selected = Reg(UInt(4))
    val tag = Reg(UInt(8))
    val fault = Reg(Bool())
    val acquire = request.cacheOperation === 1.U(2)
    val release = request.cacheOperation === 2.U(2)
    val special = acquire | release
    val maintenance = parameter.enableZicbom.B & (request.cacheOperation === 3.U(2))
    val cacheable = DitDahA1Memory.dataCacheable(parameter, request.address, 1)
    val releaseAllowed = parameter.memoryRegions.filter(r => r.readable && r.dataCacheable && !r.device).foldLeft[Referable[Bool]](false.B) { (allowed, region) =>
      allowed | ((request.address >= (region.base & ~BigInt(63)).U(64)) &
        (request.address <= ((region.base + region.size - 1) & ~BigInt(63)).U(64)))
    }
    val authorized = maintenance.?(DitDahA1Memory.managementPermitted(parameter, request),
      (if parameter.dCacheWriteback then release else false.B).?(releaseAllowed,
        cacheable & DitDahA1Memory.permitted(parameter, request)))
    val invalidOperation = (request.cacheOperation =/= 0.U(2)) &
      maintenance.?(!authorized, (if parameter.dCacheWriteback then !special | request.atomic | request.fetch |
        (acquire & !request.write) | (release & (request.write | (request.size =/= 3.U(3)) |
          (request.address.asBits.bits(5, 0) =/= 0.B(6)))) |
        !authorized else true.B))
    val coherent = authorized &
      (maintenance | (if parameter.dCacheWriteback then true.B else request.write))
    val invalidate = request.write | release | request.atomic | maintenance
    val targets = (0 until parameter.hartCount).reverse.map { hart =>
      val owner = io.hartId === hart.U(4)
      (maintenance | (if parameter.dCacheWriteback then release.?(owner, (!acquire | !owner))
        else request.atomic | !owner)).asBits
    }.reduce(_ ## _)
    val acknowledged = (0 until parameter.hartCount).reverse.map(hart =>
      (io.probe(hart).request.valid & io.probe(hart).request.ready).asBits).reduce(_ ## _)
    val completed = (0 until parameter.hartCount).reverse.map(hart =>
      (io.probe(hart).response.valid & io.probe(hart).response.ready & io.probe(hart).response.bits.last).asBits).reduce(_ ## _)
    val dirty = (0 until parameter.hartCount).map(hart =>
      pending.bit(hart) & sent.bit(hart) & io.probe(hart).response.valid & (io.probe(hart).response.bits.mask =/= 0.U(8)))
    val choice = dirty.zipWithIndex.reverse.foldLeft[Referable[UInt]](0.U(4)) {
      case (previous, (valid, hart)) => valid.?(hart.U(4), previous)
    }
    val frame = Wire(new CacheProbeResponse)
    frame :<= io.probe(0).response.bits
    for hart <- 1 until parameter.hartCount do
      when(selected === hart.U(4)) { frame :<= io.probe(hart).response.bits }
    val writebackFault = fault | down.response.bits.fault | (down.response.bits.tag =/= tag) | !down.response.bits.last
    for hart <- 0 until parameter.hartCount do
      val probe = io.probe(hart)
      probe.request.valid := ((state === 1.U(3)) | (state === 2.U(3)) | (state === 3.U(3))) & pending.bit(hart) & !sent.bit(hart)
      probe.request.bits.address := (request.address.asBits.bits(63, 6) ## 0.B(6)).asUInt
      probe.request.bits.invalidate := invalidate
      probe.response.ready := pending.bit(hart) & sent.bit(hart) &
        (((state === 1.U(3)) & (probe.response.bits.mask === 0.U(8))) |
          ((state === 3.U(3)) & (selected === hart.U(4)) & down.response.valid & !writebackFault))
    val forwarding = ((state === 0.U(3)) & !coherent & !invalidOperation) |
      ((state === 4.U(3)) & !special)
    up.request.ready := (forwarding & down.request.ready) |
      ((state === 0.U(3)) & invalidOperation) | ((state === 4.U(3)) & special)
    down.request.valid := ((state === 2.U(3)) | forwarding) & up.request.valid
    down.request.bits :<= request
    down.request.bits.cacheOperation := maintenance.?(3.U(2), 0.U(2))
    when(state === 2.U(3)) {
      down.request.bits.cacheOperation := 0.U(2)
      down.request.bits.debug.foreach(_ := false.B)
      down.request.bits.address := (request.address.asBits.bits(63, 6) ## frame.word.asBits ## 0.B(3)).asUInt
      down.request.bits.data := frame.data
      down.request.bits.mask := frame.mask
      down.request.bits.size := 3.U(3)
      down.request.bits.tag := tag
      down.request.bits.write := true.B
      down.request.bits.fetch := false.B
      down.request.bits.atomic := false.B
      down.request.bits.atomicOperation := 0.U(5)
      down.request.bits.scEligible := false.B
      down.request.bits.privileged := true.B
      down.request.bits.refillSize := 0.U(3)
    }
    up.response.valid := (state === 5.U(3)) | ((state === 6.U(3)) & down.response.valid)
    up.response.bits :<= down.response.bits
    when(state === 5.U(3)) {
      up.response.bits.data := 0.U(64)
      up.response.bits.fault := fault
      up.response.bits.tag := tag
      up.response.bits.last := true.B
    }
    down.response.ready := (state === 3.U(3)) | ((state === 6.U(3)) & up.response.ready)
    when(state === 0.U(3)) {
      when(up.request.valid & invalidOperation) { tag := request.tag; fault := true.B; state := 5.U(3) }
        .otherwise { when(up.request.valid & coherent) {
          pending := targets
          sent := 0.B(parameter.hartCount)
          tag := request.tag
          fault := false.B
          state := 1.U(3)
        } }
    }
    when(state === 1.U(3)) {
      when(pending === 0.B(parameter.hartCount)) { state := 4.U(3) }
        .otherwise { when(dirty.reduce(_ | _)) { selected := choice; state := 2.U(3) } }
    }
    when((state =/= 0.U(3)) & (state =/= 5.U(3)) & (state =/= 6.U(3))) {
      sent := sent | acknowledged
      pending := pending & ~completed
    }
    when(down.request.valid & down.request.ready) {
      when(state === 2.U(3)) { fault := false.B }
      state := (state === 2.U(3)).?(3.U(3), 6.U(3))
    }
    when((state === 3.U(3)) & down.response.valid) {
      fault := writebackFault
      when(down.response.bits.last) { state := writebackFault.?(2.U(3), 1.U(3)) }
    }
    when((state === 4.U(3)) & special & up.request.valid) { state := 5.U(3) }
    when(up.response.valid & up.response.ready & up.response.bits.last) { state := 0.U(3) }
