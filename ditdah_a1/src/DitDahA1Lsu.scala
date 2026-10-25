// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1LsuIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val pmp = Option.when(parameter.pmpEntries != 0)(Flipped(new PmpState(parameter)))
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val privilege = Flipped(UInt(2))
  val input = Flipped(new Decoupled(new ResultPacket))
  val output = Aligned(new Decoupled(new ResultPacket))
  val storeAllowed = Flipped(Bool())
  val cancel = Option.when(parameter.loadQueueEntries == 2)(Flipped(Bool()))
  val translation = Option.when(parameter.enableTranslation)(Aligned(new TranslationPort))
  val memory = Aligned(new MemoryPort)

@generator
object DitDahA1Lsu extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1LsuIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Lsu"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1LsuIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val checkRefill = parameter.dCacheBytes != 0 && parameter.pmpEntries != 0
    val lineRefill = parameter.dCacheBytes != 0 && parameter.enableDataBurstRefill
    val stateBits = if parameter.enableTranslation || checkRefill then 3 else 2
    val state = RegInit(0.U(stateBits))
    val concurrent = parameter.loadQueueEntries == 2
    val packet = Reg(new ResultPacket)
    val packets = Seq(packet) ++ Option.when(concurrent)(Reg(new ResultPacket))
    val owner = Option.when(concurrent)(RegInit(0.U(1)))
    val head = Option.when(concurrent)(RegInit(0.U(1)))
    val tail = Option.when(concurrent)(RegInit(0.U(1)))
    val contexts = Option.when(concurrent)(Seq.fill(2)(RegInit(0.U(2))))
    val live = contexts.map(_.map(_ =/= 0.U(2)))
    val pending = contexts.map(_.map(_ === 2.U(2)))
    val done = contexts.map(_.map(_ === 3.U(2)))
    val killed = Option.when(concurrent)(Seq.fill(2)(RegInit(false.B)))
    val effect = Option.when(concurrent)(Seq.fill(2)(RegInit(false.B)))
    val address = Option.when(concurrent && parameter.enableTranslation)(Seq.fill(2)(Reg(UInt(61))))
    val offered = Option.when(concurrent)(RegInit(false.B))
    val poisoned = Option.when(concurrent)(RegInit(false.B))
    val current = if !concurrent then packet else
      val selected = Wire(new ResultPacket)
      selected :<= packet
      when(owner.get === 1.U(1)) { selected :<= packets(1) }
      selected
    val updated = if !concurrent then packet else
      val next = Wire(new ResultPacket)
      next :<= current
      next
    val privileged = Option.when(parameter.enableUserMode && !parameter.enableTranslation && !checkRefill)(Reg(Bool()))
    val privilege = Option.when(parameter.enableTranslation || checkRefill)(Reg(UInt(2)))
    val physicalAddress = Option.when(parameter.enableTranslation)(Reg(UInt(64)))
    val refillSize = Option.when(parameter.dCacheBytes != 0)(RegInit(0.U(3)))
    val reserved = RegInit(false.B)
    val reservedWord = Reg(UInt(parameter.physicalAddressBits - 3))
    val scEligible = Reg(Bool())
    val reservedAddress = (0.B(64 - parameter.physicalAddressBits) ## reservedWord.asBits ## 0.B(3)).asUInt
    val inputOperation = io.input.bits.instruction.instruction.asBits.bits(31, 27).asUInt
    val operation = current.instruction.instruction.asBits.bits(31, 27).asUInt
    val request = io.memory.request
    val response = io.memory.response
    val refilling = if checkRefill then state === 6.U(stateBits) else false.B
    val exact = if checkRefill && lineRefill then state === 7.U(stateBits) else false.B
    val demandAddress = io.translation.map(_.response.bits.address).getOrElse(io.input.bits.address)
    val demandSize = if parameter.enableTranslation then current.memorySize else io.input.bits.memorySize
    val demandStore = if parameter.enableTranslation then current.store else io.input.bits.store
    val demandLoad = if parameter.enableTranslation then current.load else io.input.bits.load
    val demandAtomic = if parameter.enableTranslation then current.atomic else io.input.bits.atomic
    val refillCandidate = if parameter.dCacheBytes != 0 then
      demandLoad & !demandStore & !demandAtomic & (demandSize < 3.U(3)) &
        DitDahA1Memory.dataCacheable(parameter, (demandAddress.asBits.bits(63, 3) ## 0.B(3)).asUInt, 8)
    else false.B
    val lineCandidate = if lineRefill then
      demandLoad & !demandStore & !demandAtomic & (demandSize <= 3.U(3)) &
        DitDahA1Memory.dataCacheable(parameter, (demandAddress.asBits.bits(63, 6) ## 0.B(6)).asUInt, 64)
    else false.B
    val initialSize = if lineRefill then lineCandidate.?(6.U(3), refillCandidate.?(3.U(3), demandSize)) else demandSize
    val initialAddress = if lineRefill then lineCandidate.?(
      (demandAddress.asBits.bits(63, 6) ## 0.B(6)).asUInt,
      refillCandidate.?((demandAddress.asBits.bits(63, 3) ## 0.B(3)).asUInt, demandAddress)) else demandAddress
    val heldAddress = physicalAddress.getOrElse(current.address)
    val permitted = if parameter.pmpEntries == 0 then true.B else
      val pmp = DitDahA1Pmp.instantiate(parameter)
      pmp.io.state :<= io.pmp.get
      pmp.io.address := refilling.?((heldAddress.asBits.bits(63, 3) ## 0.B(3)).asUInt, exact.?(heldAddress, initialAddress))
      pmp.io.size := refilling.?(3.U(3), exact.?(current.memorySize, initialSize))
      pmp.io.write := !refilling & !exact & demandStore
      pmp.io.fetch := false.B
      pmp.io.atomic := !refilling & !exact & demandLoad & demandStore
      pmp.io.privilege := (if parameter.enableTranslation then privilege.get
        else if checkRefill then (refilling | exact).?(privilege.get, io.privilege) else io.privilege)
      pmp.io.allowed
    val initialState = if checkRefill && lineRefill then
      permitted.?(1.U(stateBits), (lineCandidate & refillCandidate).?(6.U(stateBits), 7.U(stateBits)))
    else if checkRefill then refillCandidate.?(6.U(stateBits), 1.U(stateBits)) else 1.U(stateBits)
    val denied = !permitted & (if lineRefill then !lineCandidate & !refillCandidate else true.B)
    val initialGrant = if lineRefill then permitted.?(lineCandidate.?(6.U(3), refillCandidate.?(3.U(3), 0.U(3))), 0.U(3))
      else if !checkRefill then refillCandidate.?(3.U(3), 0.U(3)) else 0.U(3)
    io.input.ready := (state === 0.U(stateBits)) & (io.input.bits.instruction.fault | !io.input.bits.store | io.storeAllowed)
    io.output.valid := state === 3.U(stateBits)
    io.output.bits :<= packet
    request.valid := state === 1.U(stateBits)
    if concurrent then
      val busy = live.get.foldLeft[Referable[Bool]](false.B)(_ | _)
      val serial = (0 until 2).map(n => live.get(n) & (packets(n).store | packets(n).atomic)).reduce(_ | _)
      val abandoned = (0 until 2).map(n => live.get(n) & killed.get(n)).reduce(_ | _)
      val available = (0 until 2).map(n => (tail.get === n.U(1)) & !live.get(n)).reduce(_ | _)
      io.input.ready := (state === 0.U(stateBits)) & available & !serial & !io.cancel.get & !poisoned.get & !abandoned &
        (!(io.input.bits.store | io.input.bits.atomic) | (!busy & io.storeAllowed))
      io.output.valid := (0 until 2).map(n => (head.get === n.U(1)) & done.get(n)).reduce(_ | _)
      for n <- 0 until 2 do
        when(head.get === n.U(1)) { io.output.bits :<= packets(n) }
        when((owner.get === n.U(1)) | (io.input.valid & io.input.ready & (tail.get === n.U(1)))) {
          when(!(io.input.valid & io.input.ready) | (tail.get === n.U(1))) { packets(n) :<= updated }
        }
        when(io.input.valid & io.input.ready & (tail.get === n.U(1))) {
          contexts.get(n) := 1.U(2); killed.get(n) := false.B
          effect.get(n) := !busy & io.storeAllowed
        }
        when(live.get(n) & (head.get === n.U(1)) & io.storeAllowed) { effect.get(n) := true.B }
        when(io.cancel.get & live.get(n)) { killed.get(n) := true.B }
        when((state === 3.U(stateBits)) & (owner.get === n.U(1))) { contexts.get(n) := 3.U(2) }
        when(io.output.valid & io.output.ready & (head.get === n.U(1))) {
          contexts.get(n) := 0.U(2); killed.get(n) := false.B
        }
      when(io.input.valid & io.input.ready) { owner.get := tail.get; tail.get := (~tail.get.asBits).asUInt }
      when(io.output.valid & io.output.ready) { head.get := (~head.get.asBits).asUInt }
      when(state === 3.U(stateBits)) { state := 0.U(stateBits) }
      val device = parameter.memoryRegions.filter(_.device).foldLeft[Referable[Bool]](false.B) { (selected, region) =>
        selected | ((heldAddress >= region.base.U(64)) & (heldAddress < (region.base + region.size).U(64)))
      }
      val cancelled = io.cancel.get | (0 until 2).map(n => (owner.get === n.U(1)) & killed.get(n)).reduce(_ | _)
      val alias = (0 until 2).map(n => pending.get(n) & (owner.get =/= n.U(1)) &
        (address.map(_(n)).getOrElse(packets(n).address.asBits.bits(63, 3).asUInt) === heldAddress.asBits.bits(63, 3).asUInt)).reduce(_ | _)
      val allowed = (0 until 2).map(n => (owner.get === n.U(1)) & effect.get(n)).reduce(_ | _)
      request.valid := (state === 1.U(stateBits)) & (offered.get |
        (!cancelled & !poisoned.get & !alias & (!device | ((owner.get === head.get) & (allowed | io.storeAllowed)))))
      when(request.valid & !request.ready) { offered.get := true.B }
      when((state === 1.U(stateBits)) & !offered.get & (cancelled | poisoned.get)) { state := 3.U(stateBits) }
      when((state === 1.U(stateBits)) & !offered.get & poisoned.get) {
        updated.instruction.fault := true.B; updated.instruction.cause := 5.U(64); updated.instruction.tval := current.address
      }
      when(request.valid & request.ready) { offered.get := false.B }
      when(state === 3.U(stateBits)) { offered.get := false.B }
    request.bits.address := physicalAddress.getOrElse(current.address)
    request.bits.data := current.storeData
    request.bits.size := current.memorySize
    request.bits.mask := 0.U(8)
    for size <- 0 to 3 do
      when(current.store & (current.memorySize === size.U(3))) { request.bits.mask := ((1 << (1 << size)) - 1).U(8) }
    request.bits.tag := owner.getOrElse(current.instruction.tag)
    request.bits.write := current.store
    request.bits.fetch := false.B
    request.bits.privileged := privilege.map(_ =/= 0.U(2)).getOrElse(privileged.getOrElse(true.B))
    request.bits.atomic := current.atomic
    request.bits.atomicOperation := current.atomic.?(operation, 0.U(5))
    request.bits.cacheOperation := 0.U(2)
    request.bits.scEligible := scEligible
    request.bits.refillSize := refillSize.getOrElse(0.U(3))
    response.ready := state === 2.U(stateBits)
    io.translation.foreach { t =>
      t.request.valid := state === 4.U(stateBits)
      t.request.bits.address := current.address
      t.request.bits.privilege := privilege.get
      t.request.bits.fetch := false.B
      t.request.bits.write := current.store
      t.response.ready := state === 5.U(stateBits)
      when(t.request.valid & t.request.ready) { state := 5.U(stateBits) }
      when(t.response.valid & t.response.ready) {
        physicalAddress.get := t.response.bits.address
        scEligible := scEligible & (t.response.bits.address === reservedAddress)
        updated.instruction.fault := t.response.bits.fault
        updated.instruction.cause := t.response.bits.fault.?(t.response.bits.cause, 0.U(64))
        updated.instruction.tval := t.response.bits.fault.?(current.address, 0.U(64))
        state := initialState
        refillSize.foreach(_ := initialGrant)
        when(!t.response.bits.fault & denied) {
          updated.instruction.fault := true.B
          updated.instruction.cause := current.store.?(7.U(64), 5.U(64))
          updated.instruction.tval := current.address
          state := 3.U(stateBits)
        }
        when(t.response.bits.fault) { state := 3.U(stateBits) }
      }
    }
    when(io.input.valid & io.input.ready) {
      privileged.foreach(_ := (io.privilege =/= 0.U(2)))
      privilege.foreach(_ := io.privilege)
      updated :<= io.input.bits
      refillSize.foreach(_ := (if !parameter.enableTranslation then initialGrant else 0.U(3)))
      scEligible := io.input.bits.atomic & (inputOperation === 3.U(5)) & reserved &
        (if parameter.enableTranslation then true.B else io.input.bits.address === reservedAddress) & (io.input.bits.memorySize === 3.U(3))
      when(io.input.bits.atomic) { reserved := false.B }
      state := (if parameter.enableTranslation then 4.U(stateBits) else initialState)
      if parameter.pmpEntries != 0 && !parameter.enableTranslation then
        when(!io.input.bits.instruction.fault & denied) {
          updated.instruction.fault := true.B
          updated.instruction.cause := io.input.bits.store.?(7.U(64), 5.U(64))
          updated.instruction.tval := io.input.bits.address
          state := 3.U(stateBits)
        }
      val alignment = Wire(UInt(64))
      alignment := 7.U(64)
      for size <- 0 to 2 do
        when(io.input.bits.memorySize === size.U(3)) { alignment := ((1 << size) - 1).U(64) }
      when(!io.input.bits.instruction.fault & ((io.input.bits.address.asBits & alignment.asBits).asUInt =/= 0.U(64))) {
        updated.instruction.fault := true.B
        updated.instruction.cause := io.input.bits.store.?(6.U(64), 4.U(64))
        updated.instruction.tval := io.input.bits.address
        state := 3.U(stateBits)
      }
      when(io.input.bits.instruction.fault) { state := 3.U(stateBits) }
    }
    if checkRefill then
      when(refilling) {
        refillSize.get := permitted.?(3.U(3), 0.U(3))
        state := (if lineRefill then permitted.?(1.U(stateBits), 7.U(stateBits)) else 1.U(stateBits))
      }
      if lineRefill then
        when(exact) {
          refillSize.get := 0.U(3)
          state := permitted.?(1.U(stateBits), 3.U(stateBits))
          when(!permitted) { updated.instruction.fault := true.B; updated.instruction.cause := 5.U(64); updated.instruction.tval := current.address }
        }
    when(request.valid & request.ready) {
      state := (if concurrent then 0.U(stateBits) else 2.U(stateBits))
      if concurrent then
        for n <- 0 until 2 do
          when(owner.get === n.U(1)) { contexts.get(n) := 2.U(2); address.foreach(_(n) := request.bits.address.asBits.bits(63, 3).asUInt) }
    }
    if concurrent then
      response.ready := pending.get.foldLeft[Referable[Bool]](false.B)(_ | _)
      val known = (0 until 2).map(n => pending.get(n) & (response.bits.tag === n.U(8))).reduce(_ | _)
      when(response.valid & response.ready & !known) { poisoned.get := true.B }
    for n <- packets.indices do
      val completed = packets(n)
      val identity = if concurrent then n.U(8) else completed.instruction.tag
      val matching = if concurrent then pending.get(n) & (response.bits.tag === identity) else true.B
      when(response.valid & response.ready & matching) {
        when(completed.load | completed.atomic) {
          completed.value := response.bits.data
          for size <- 0 to 2 do
            val bits = 8 << size
            val low = response.bits.data.asBits.bits(bits - 1, 0)
            val high = (!completed.unsignedLoad & low.bit(bits - 1)).?(((BigInt(1) << (64 - bits)) - 1).B(64 - bits), 0.B(64 - bits))
            when(completed.memorySize === size.U(3)) { completed.value := (high ## low).asUInt }
        }
        when(response.bits.fault | poisoned.getOrElse(false.B) | (if concurrent then !response.bits.last else false.B) | (response.bits.tag =/= identity)) {
          completed.instruction.fault := true.B
          completed.instruction.cause := completed.store.?(7.U(64), 5.U(64))
          completed.instruction.tval := completed.address
        }
        when(completed.atomic & (operation === 2.U(5)) & (completed.memorySize === 3.U(3)) &
          !response.bits.fault & (response.bits.tag === identity) &
          (if concurrent then response.bits.last & !completed.instruction.fault & !poisoned.get & !killed.get(n) & !io.cancel.get else true.B)) {
          reserved := true.B
          reservedWord := physicalAddress.getOrElse(completed.address).asBits.bits(parameter.physicalAddressBits - 1, 3).asUInt
        }
        if !concurrent then state := 3.U(stateBits)
        else
          when(response.bits.last) { contexts.get(n) := 3.U(2) }
      }
    if !concurrent then
      when(io.output.valid & io.output.ready) { state := 0.U(stateBits) }
    else
      when(io.cancel.get) { reserved := false.B }
