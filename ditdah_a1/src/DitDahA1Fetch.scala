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
  val output = Aligned(new Decoupled(new FetchPacket(parameter.fetchWords)))
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
    val wide = parameter.fetchWords > 1
    val bankBits = Integer.numberOfTrailingZeros(parameter.fetchWords)
    val stateBits = if parameter.enableTranslation || wide then 3 else 2
    val state = RegInit(0.U(stateBits))
    val packet = Reg(new FetchPacket)
    val killed = RegInit(false.B)
    val flush = io.cancel | io.invalidate.getOrElse(false.B)
    val cached = parameter.iCacheBytes != 0
    val pipelined = cached && !parameter.enableTranslation
    val accepting = Wire(Bool())
    val wholeBlock = Option.when(wide)(Reg(Bool()))
    val privilege = Option.when(parameter.enableUserMode)(Reg(UInt(2)))
    val physicalAddress = Option.when(parameter.enableTranslation)(Reg(UInt(64)))
    val cache = Option.when(parameter.iCacheBytes != 0)(DitDahA1InstructionCache.instantiate(parameter))
    val request = cache.map(_.io.upstream.request).getOrElse(io.memory.request)
    val response = cache.map(_.io.upstream.response).getOrElse(io.memory.response)
    val rechecking = if wide then state === 6.U(stateBits) else false.B
    val translating = if parameter.enableTranslation then state === 5.U(stateBits) else false.B
    val checkingDemand = accepting | translating | rechecking
    val demandAddress = io.translation.map(t => translating.?(t.response.bits.address,
      accepting.?(io.request.bits.pc, physicalAddress.get))).getOrElse(accepting.?(io.request.bits.pc, packet.pc))
    val checkedAddress = if wide then rechecking.?(demandAddress,
      (demandAddress.asBits.bits(63, bankBits + 2) ## 0.B(bankBits + 2)).asUInt) else demandAddress
    val checkedSize = if wide then rechecking.?(2.U(3), (bankBits + 2).U(3)) else 2.U(3)
    val permitted = if parameter.pmpEntries == 0 then true.B else
      val pmp = DitDahA1Pmp.instantiate(parameter)
      pmp.io.state :<= io.pmp.get
      pmp.io.address := cache.map(c => checkingDemand.?(checkedAddress, c.io.checkAddress)).getOrElse(checkedAddress)
      pmp.io.size := cache.map(c => checkingDemand.?(checkedSize, c.io.checkSize)).getOrElse(checkedSize)
      pmp.io.write := false.B
      pmp.io.fetch := true.B
      pmp.io.atomic := false.B
      pmp.io.privilege := accepting.?(io.privilege, privilege.getOrElse(3.U(2)))
      pmp.io.allowed
    cache.foreach { c =>
      c.io.clock := io.clock
      c.io.reset := io.reset
      c.io.cancel := io.cancel
      c.io.invalidate := io.invalidate.get
      val ordinary = if parameter.enableBurstRefill then (c.io.checkSize === 6.U(3)).?(
        DitDahA1Memory.executable(parameter, c.io.checkAddress, 64), DitDahA1Memory.executable(parameter, c.io.checkAddress, 4))
      else DitDahA1Memory.executable(parameter, c.io.checkAddress, 4)
      c.io.allowed := permitted & ordinary
      io.memory :<>= c.io.downstream
    }
    val ordinaryDemand = if wide then rechecking.?(DitDahA1Memory.executable(parameter, demandAddress, 4),
      DitDahA1Memory.executable(parameter, checkedAddress, 4 * parameter.fetchWords))
      else DitDahA1Memory.executable(parameter, demandAddress, 4)
    val demandPermitted = if cache.isDefined then permitted & ordinaryDemand else permitted
    val shortReturn = if wide then io.output.valid & (io.output.bits.count.get <
      (parameter.fetchWords.U(parameter.fetchCountBits) - packet.pc.asBits.bits(bankBits + 1, 2).asUInt)) else false.B
    accepting := (state === 0.U(stateBits)) | (if pipelined then io.output.valid & io.output.ready & !io.output.bits.fault & !shortReturn else false.B)
    io.request.ready := accepting & !flush & (if pipelined then request.ready else true.B)
    io.output.valid := ((state === 3.U(stateBits)) | (if cached then (state === 2.U(stateBits)) & response.valid else false.B)) & !killed & !flush
    for field <- Seq("pc", "tag", "instruction", "length", "cause", "tval") do
      io.output.bits.asRecord.field[UInt](field) := packet.asRecord.field[UInt](field)
    io.output.bits.fault := packet.fault
    io.output.bits.count.foreach(_ := 1.U(parameter.fetchCountBits))
    io.output.bits.following.foreach { words => for i <- 0 until parameter.fetchWords - 1 do words(i) := 0.U(32) }
    if cached then
      when(state === 2.U(stateBits)) {
        val failed = response.bits.fault | (response.bits.tag =/= packet.tag)
        io.output.bits.instruction := failed.?(0.U(32), response.bits.data.asBits.bits(31, 0).asUInt)
        io.output.bits.fault := failed
        io.output.bits.cause := failed.?(1.U(64), 0.U(64))
        io.output.bits.tval := failed.?(packet.pc, 0.U(64))
        io.output.bits.count.foreach(_ := failed.?(1.U(parameter.fetchCountBits), response.bits.count.get))
        io.output.bits.following.foreach { words =>
          for i <- 0 until parameter.fetchWords - 1 do
            words(i) := failed.?(0.U(32), response.bits.data.asBits.bits(32 * (i + 2) - 1, 32 * (i + 1)).asUInt)
        }
      }
    request.valid := (if pipelined then (io.request.valid & accepting & !flush & demandPermitted &
      (io.request.bits.pc.asBits.bits(1, 0) === 0.B(2))) | (if wide then state === 1.U(stateBits) else false.B) else state === 1.U(stateBits))
    request.bits.address := (if pipelined then (if wide then accepting.?(io.request.bits.pc, packet.pc) else io.request.bits.pc) else physicalAddress.getOrElse(packet.pc))
    request.bits.data := 0.U(64)
    request.bits.size := (if wide then accepting.?(true.B, wholeBlock.get).?((bankBits + 2).U(3), 2.U(3)) else 2.U(3))
    request.bits.mask := 0.U(8)
    request.bits.tag := (if pipelined then (if wide then accepting.?(io.request.bits.tag, packet.tag) else io.request.bits.tag) else packet.tag)
    request.bits.fetch := true.B
    request.bits.privileged := (if pipelined && parameter.enableUserMode then
      (if wide then accepting.?(io.privilege, privilege.get) else io.privilege) =/= 0.U(2)
      else privilege.map(_ =/= 0.U(2)).getOrElse(true.B))
    request.bits.write := false.B
    request.bits.atomic := false.B
    request.bits.atomicOperation := 0.U(5)
    request.bits.scEligible := false.B
    response.ready := (state === 2.U(stateBits)) & (if cached then killed | flush | io.output.ready else true.B)
    io.translation.foreach { t =>
      t.request.valid := (state === 4.U(stateBits)) & !killed & !flush
      t.request.bits.address := packet.pc
      t.request.bits.privilege := privilege.get
      t.request.bits.fetch := true.B
      t.request.bits.write := false.B
      t.response.ready := state === 5.U(stateBits)
      when(t.request.valid & t.request.ready) { state := 5.U(stateBits) }
      when((state === 4.U(stateBits)) & (killed | flush)) { state := 0.U(stateBits) }
      when(t.response.valid & t.response.ready) {
        physicalAddress.get := t.response.bits.address
        packet.fault := t.response.bits.fault
        packet.cause := t.response.bits.fault.?(t.response.bits.cause, 0.U(64))
        packet.tval := t.response.bits.fault.?(packet.pc, 0.U(64))
        state := 1.U(stateBits)
        when(!t.response.bits.fault & !demandPermitted) {
          if wide then
            wholeBlock.get := false.B
            state := 6.U(stateBits)
          else
            packet.fault := true.B
            packet.cause := 1.U(64)
            packet.tval := packet.pc
            state := 3.U(stateBits)
        }
        when(t.response.bits.fault | killed | flush) { state := 3.U(stateBits) }
      }
    }
    if wide then
      when(state === 6.U(stateBits)) {
        state := 1.U(stateBits)
        when(!demandPermitted) {
          packet.fault := true.B
          packet.cause := 1.U(64)
          packet.tval := packet.pc
          state := 3.U(stateBits)
        }
        when(killed | flush) { state := 0.U(stateBits) }
      }
    when(request.valid & request.ready) { state := 2.U(stateBits) }
    when(response.valid & response.ready) {
      if !cached then
        val fault = response.bits.fault | (response.bits.tag =/= packet.tag)
        packet.instruction := fault.?(0.U(32), response.bits.data.asBits.bits(31, 0).asUInt)
        packet.fault := fault
        packet.cause := fault.?(1.U(64), 0.U(64))
        packet.tval := fault.?(packet.pc, 0.U(64))
      state := (if cached then 0 else 3).U(stateBits)
    }
    when(flush & (state =/= 0.U(stateBits))) { killed := true.B }
    when((state === 3.U(stateBits)) & (killed | flush | io.output.ready)) { state := 0.U(stateBits) }
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
      wholeBlock.foreach(_ := true.B)
      state := (if parameter.enableTranslation then 4 else if pipelined then 2 else 1).U(stateBits)
      if !parameter.enableTranslation && (parameter.pmpEntries != 0 || cache.isDefined) then
        when(!demandPermitted) {
          if wide then
            wholeBlock.get := false.B
            state := 6.U(stateBits)
          else
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
