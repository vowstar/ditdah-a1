// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1FetchIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val pmp = Option.when(parameter.pmpEntries != 0)(Flipped(new PmpState(parameter)))
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val privilege = Flipped(UInt(2))
  val request = Flipped(new Decoupled(new FetchRequest))
  val output = Aligned(new Decoupled(new FetchPacket))
  val cancel = Flipped(Bool())
  val invalidate = Option.when(parameter.iCacheBytes != 0)(Flipped(Bool()))
  val translation = Option.when(parameter.enableTranslation)(Aligned(new TranslationPort))
  val memory = Aligned(new MemoryPort)

@generator
object DitDahA1Fetch extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1FetchIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Fetch"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1FetchIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val stateBits = if parameter.enableTranslation then 3 else 2
    val state = RegInit(0.U(stateBits))
    val packet = Reg(new FetchPacket)
    val killed = RegInit(false.B)
    val privilege = Option.when(parameter.enableUserMode)(Reg(UInt(2)))
    val physicalAddress = Option.when(parameter.enableTranslation)(Reg(UInt(64)))
    val cache = Option.when(parameter.iCacheBytes != 0)(DitDahA1InstructionCache.instantiate(parameter))
    val memory = cache.map(_.io.upstream).getOrElse(io.memory)
    val request = memory.request
    val response = memory.response
    val permitted = if parameter.pmpEntries == 0 then true.B else
      val pmp = DitDahA1Pmp.instantiate(parameter)
      pmp.io.state :<= io.pmp.get
      val checkAddress = cache.map(c => (state === 0.U(stateBits)).?(io.request.bits.pc, c.io.checkAddress)).getOrElse(io.request.bits.pc)
      pmp.io.address := io.translation.map(t => (state === 5.U(stateBits)).?(t.response.bits.address, checkAddress)).getOrElse(checkAddress)
      pmp.io.size := 2.U(3)
      pmp.io.write := false.B
      pmp.io.fetch := true.B
      pmp.io.atomic := false.B
      pmp.io.privilege := (state === 0.U(stateBits)).?(io.privilege, privilege.getOrElse(3.U(2)))
      pmp.io.allowed
    cache.foreach { c =>
      c.io.clock := io.clock
      c.io.reset := io.reset
      c.io.cancel := io.cancel
      c.io.invalidate := io.invalidate.get
      c.io.allowed := permitted & DitDahA1Memory.executable(parameter, c.io.checkAddress, 4)
      io.memory :<>= c.io.downstream
    }
    val demandPermitted = if cache.isDefined then permitted & DitDahA1Memory.executable(parameter, io.request.bits.pc, 4) else permitted
    io.request.ready := (state === 0.U(stateBits)) & !io.cancel
    io.output.valid := (state === 3.U(stateBits)) & !killed & !io.cancel
    io.output.bits :<= packet
    request.valid := state === 1.U(stateBits)
    request.bits.address := physicalAddress.getOrElse(packet.pc)
    request.bits.data := 0.U(64)
    request.bits.size := 2.U(3)
    request.bits.mask := 0.U(8)
    request.bits.tag := packet.tag
    request.bits.fetch := true.B
    request.bits.privileged := privilege.map(_ =/= 0.U(2)).getOrElse(true.B)
    request.bits.write := false.B
    request.bits.atomic := false.B
    request.bits.atomicOperation := 0.U(5)
    request.bits.scEligible := false.B
    response.ready := state === 2.U(stateBits)
    io.translation.foreach { t =>
      t.request.valid := (state === 4.U(stateBits)) & !killed & !io.cancel
      t.request.bits.address := packet.pc
      t.request.bits.privilege := privilege.get
      t.request.bits.fetch := true.B
      t.request.bits.write := false.B
      t.response.ready := state === 5.U(stateBits)
      when(t.request.valid & t.request.ready) { state := 5.U(stateBits) }
      when((state === 4.U(stateBits)) & (killed | io.cancel)) { state := 0.U(stateBits) }
      when(t.response.valid & t.response.ready) {
        physicalAddress.get := t.response.bits.address
        packet.fault := t.response.bits.fault
        packet.cause := t.response.bits.fault.?(t.response.bits.cause, 0.U(64))
        packet.tval := t.response.bits.fault.?(packet.pc, 0.U(64))
        state := 1.U(stateBits)
        when(!t.response.bits.fault & (!permitted | !DitDahA1Memory.executable(parameter, t.response.bits.address, 4))) {
          packet.fault := true.B
          packet.cause := 1.U(64)
          packet.tval := packet.pc
          state := 3.U(stateBits)
        }
        when(t.response.bits.fault | killed | io.cancel) { state := 3.U(stateBits) }
      }
    }
    when(io.request.valid & io.request.ready) {
      privilege.foreach(_ := io.privilege)
      packet.pc := io.request.bits.pc
      packet.tag := io.request.bits.tag
      packet.instruction := 0.U(32)
      packet.length := 4.U(3)
      packet.fault := false.B
      packet.cause := 0.U(64)
      packet.tval := 0.U(64)
      killed := false.B
      state := (if parameter.enableTranslation then 4 else 1).U(stateBits)
      if !parameter.enableTranslation && (parameter.pmpEntries != 0 || cache.isDefined) then
        when(!demandPermitted) {
          packet.fault := true.B
          packet.cause := 1.U(64)
          packet.tval := io.request.bits.pc
          state := 3.U(stateBits)
        }
      when(io.request.bits.pc.asBits.bits(1, 0) =/= 0.B(2)) {
        packet.fault := true.B
        packet.cause := 0.U(64)
        packet.tval := io.request.bits.pc
        state := 3.U(stateBits)
      }
    }
    when(request.valid & request.ready) { state := 2.U(stateBits) }
    when(response.valid & response.ready) {
      val fault = response.bits.fault | (response.bits.tag =/= packet.tag)
      packet.instruction := fault.?(0.U(32), response.bits.data.asBits.bits(31, 0).asUInt)
      packet.fault := fault
      packet.cause := fault.?(1.U(64), 0.U(64))
      packet.tval := fault.?(packet.pc, 0.U(64))
      state := 3.U(stateBits)
    }
    when(io.cancel & (state =/= 0.U(stateBits))) { killed := true.B }
    when((state === 3.U(stateBits)) & (killed | io.cancel | io.output.ready)) { state := 0.U(stateBits) }
