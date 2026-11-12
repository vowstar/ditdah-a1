// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1LsuIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val reservation = Option.when(parameter.enableA)(Aligned(new ReservationPort))
  val reservationValid = Option.when(parameter.enableZawrs)(Aligned(Bool()))
  val debugMode = Option.when(parameter.enableDebugMemory)(Flipped(Bool()))
  val idle = Option.when(parameter.enableJtag)(Aligned(Bool()))
  val pmp = Option.when(parameter.pmpEntries != 0)(Flipped(new PmpState(parameter)))
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val privilege = Flipped(UInt(2))
  val pointerMask = Option.when(parameter.enableSsnpm)(Flipped(Bool()))
  val virtualPointers = Option.when(parameter.enableSsnpm && parameter.enableTranslation)(Flipped(Bool()))
  val input = Flipped(new Decoupled(new ResultPacket(parameter)))
  val output = Aligned(new Decoupled(new ResultPacket(parameter)))
  val storeAllowed = Flipped(Bool())
  val cancel = Option.when(parameter.loadQueueEntries == 2)(Flipped(Bool()))
  val translation = Option.when(parameter.enableTranslation)(Aligned(new TranslationPort(parameter)))
  val memory = Aligned(new MemoryPort(parameter))

@generator
object DitDahA1Lsu extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1LsuIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Lsu"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1LsuIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val checkRefill = parameter.dCacheBytes != 0 && parameter.pmpEntries != 0
    val lineRefill = parameter.dCacheBytes != 0 && parameter.enableDataBurstRefill
    val cacheBlocks = parameter.enableZicboz || parameter.enableZicbom
    val fragments = parameter.enableMisaligned || cacheBlocks
    val pointerMask = Option.when(parameter.enableSsnpm && fragments)(Reg(Bool()))
    val virtualPointers = Option.when(parameter.enableSsnpm && fragments && parameter.enableTranslation)(Reg(Bool()))
    val inputAddress = DitDahA1Memory.maskedAddress(parameter, io.input.bits.address,
      io.pointerMask.getOrElse(false.B), io.virtualPointers.getOrElse(false.B))
    val offsetBits = if cacheBlocks then 6 else 3
    val stateBits = if parameter.enableTranslation || checkRefill || fragments then 3 else 2
    val state = RegInit(0.U(stateBits))
    val concurrent = parameter.loadQueueEntries == 2
    val packet = Reg(new ResultPacket(parameter))
    val packets = Seq(packet) ++ Option.when(concurrent)(Reg(new ResultPacket(parameter)))
    val owner = Option.when(concurrent)(RegInit(0.U(1)))
    val head = Option.when(concurrent)(RegInit(0.U(1)))
    val tail = Option.when(concurrent)(RegInit(0.U(1)))
    val contexts = Option.when(concurrent)(Seq.fill(2)(RegInit(0.U(2))))
    val live = contexts.map(_.map(_ =/= 0.U(2)))
    io.idle.foreach(_ := (state === 0.U(stateBits)) & !live.map(_.reduce(_ | _)).getOrElse(false.B))
    val pending = contexts.map(_.map(_ === 2.U(2)))
    val done = contexts.map(_.map(_ === 3.U(2)))
    val killed = Option.when(concurrent)(Seq.fill(2)(RegInit(false.B)))
    val effect = Option.when(concurrent)(Seq.fill(2)(RegInit(false.B)))
    val address = Option.when(concurrent && parameter.enableTranslation)(Seq.fill(2)(Reg(UInt(61))))
    val offered = Option.when(concurrent)(RegInit(false.B))
    val poisoned = Option.when(concurrent)(RegInit(false.B))
    val current = if !concurrent then packet else
      val selected = Wire(new ResultPacket(parameter))
      selected :<= packet
      when(owner.get === 1.U(1)) { selected :<= packets(1) }
      selected
    val updated = if !concurrent then packet else
      val next = Wire(new ResultPacket(parameter))
      next :<= current
      next
    val zero = parameter.enableZicboz.B & current.store & !current.atomic &
      ((current.instruction.instruction.asBits & BigInt("fff07fff", 16).B(32)) === 0x0040200f.B(32))
    val inputZero = parameter.enableZicboz.B & io.input.bits.store & !io.input.bits.atomic &
      ((io.input.bits.instruction.instruction.asBits & BigInt("fff07fff", 16).B(32)) === 0x0040200f.B(32))
    val management = parameter.enableZicbom.B & current.store & !current.atomic &
      ((current.instruction.instruction.asBits & BigInt("ffc07fff", 16).B(32)) === 0x0000200f.B(32)) &
      (current.instruction.instruction.asBits.bits(21, 20) =/= 3.B(2))
    val inputManagement = parameter.enableZicbom.B & io.input.bits.store & !io.input.bits.atomic &
      ((io.input.bits.instruction.instruction.asBits & BigInt("ffc07fff", 16).B(32)) === 0x0000200f.B(32)) &
      (io.input.bits.instruction.instruction.asBits.bits(21, 20) =/= 3.B(2))
    val block = zero | management
    val inputBlock = inputZero | inputManagement
    val splitting = Option.when(fragments)(RegInit(false.B))
    val offset = Option.when(fragments)(RegInit(0.U(offsetBits)))
    val split = splitting.getOrElse(false.B)
    val baseAddress = block.?((current.address.asBits.bits(63, 6) ## 0.B(6)).asUInt, current.address)
    val serviceAddress = DitDahA1Memory.maskedAddress(parameter,
      offset.map(n => (baseAddress + n).asBits.bits(63, 0).asUInt).getOrElse(current.address),
      pointerMask.getOrElse(false.B), virtualPointers.getOrElse(false.B))
    val faultAddress = block.?(current.address, serviceAddress)
    val serviceSize = Wire(UInt(3))
    serviceSize := current.memorySize
    val ordinaryBytes = (1.U(offsetBits + 1) << current.memorySize).asBits.bits(offsetBits, 0).asUInt
    val fragmentBytes = if cacheBlocks then block.?(64.U(7), ordinaryBytes) else ordinaryBytes
    val nextOffset = Option.when(fragments) {
      val remaining = fragmentBytes - offset.get
      when(split) {
        serviceSize := 0.U(3)
        for size <- 1 to 2 do
          when((remaining >= (1 << size).U(4)) & (serviceAddress.asBits.bits(size - 1, 0) === 0.B(size))) {
            serviceSize := size.U(3)
          }
      }
      when(block) { serviceSize := 3.U(3) }
      offset.get + (1.U(offsetBits + 1) << serviceSize)
    }
    val finalFragment = nextOffset.map(_ === fragmentBytes).getOrElse(true.B)
    val alignment = Wire(UInt(64))
    alignment := 7.U(64)
    for size <- 0 to 2 do
      when(io.input.bits.memorySize === size.U(3)) { alignment := ((1 << size) - 1).U(64) }
    val misaligned = (io.input.bits.address.asBits & alignment.asBits).asUInt =/= 0.U(64)
    val inputSplit = inputBlock | (parameter.enableMisaligned.B & misaligned & !io.input.bits.atomic &
      (io.input.bits.load | io.input.bits.store) & (io.input.bits.memorySize <= 3.U(3)))
    val privileged = Option.when(parameter.enableUserMode && !parameter.enableTranslation && !checkRefill && !fragments)(Reg(Bool()))
    val privilege = Option.when(parameter.enableTranslation || checkRefill || fragments)(Reg(UInt(2)))
    val debugOrigin = Option.when(parameter.enableDebugMemory)(Reg(Bool()))
    val physicalAddress = Option.when(parameter.enableTranslation)(Reg(UInt(64)))
    val pbmt = Option.when(parameter.enableSvpbmt)(Reg(UInt(2)))
    val refillSize = Option.when(parameter.dCacheBytes != 0)(RegInit(0.U(3)))
    val reserved = Option.when(parameter.enableA)(RegInit(false.B))
    io.reservationValid.foreach(_ := reserved.get & !io.reservation.get.invalidate)
    val reservedWord = Option.when(parameter.enableA)(Reg(UInt(parameter.physicalAddressBits - 2)))
    val reservedDoubleword = Option.when(parameter.enableA)(Reg(Bool()))
    val scEligible = Option.when(parameter.enableA)(Reg(Bool()))
    val reservedAddress = reservedWord.map(word => (0.B(64 - parameter.physicalAddressBits) ## word.asBits ## 0.B(2)).asUInt).getOrElse(0.U(64))
    val inputOperation = io.input.bits.instruction.instruction.asBits.bits(31, 27).asUInt
    val operation = current.instruction.instruction.asBits.bits(31, 27).asUInt
    val request = io.memory.request
    val response = io.memory.response
    val refilling = if checkRefill then !block & (state === 6.U(stateBits)) else false.B
    val exact = if checkRefill && lineRefill then !block & (state === 7.U(stateBits)) else false.B
    val preparing = (if fragments && !parameter.enableTranslation then split & (state === 4.U(stateBits)) else false.B) |
      (if cacheBlocks then block & ((state === 6.U(stateBits)) | (state === 7.U(stateBits))) else false.B)
    val heldAddress = physicalAddress.map(a => if cacheBlocks then
      block.?(((a.asBits.bits(63, 6) ## 0.B(6)).asUInt + offset.get).asBits.bits(63, 0).asUInt, a) else a).getOrElse(serviceAddress)
    val translatedAddress = io.translation.map(t => block.?((t.response.bits.address.asBits.bits(63, 6) ## 0.B(6)).asUInt, t.response.bits.address))
    val demandAddress = translatedAddress.map(a => preparing.?(heldAddress, a)).getOrElse(preparing.?(serviceAddress, inputAddress))
    val demandPbmt = if parameter.enableSvpbmt then (preparing | refilling | exact).?(pbmt.get, io.translation.get.response.bits.pbmt.get) else 0.U(2)
    val demandSize = if parameter.enableTranslation then serviceSize else preparing.?(serviceSize, io.input.bits.memorySize)
    val demandStore = if parameter.enableTranslation then current.store else preparing.?(current.store, io.input.bits.store)
    val demandLoad = if parameter.enableTranslation then current.load else preparing.?(current.load, io.input.bits.load)
    val demandAtomic = if parameter.enableTranslation then current.atomic else preparing.?(current.atomic, io.input.bits.atomic)
    val refillCandidate = if parameter.dCacheBytes != 0 then
      (demandPbmt === 0.U(2)) & demandLoad & !demandStore & !demandAtomic & !split & (if parameter.enableTranslation then true.B else !inputSplit) & (demandSize < 3.U(3)) &
        DitDahA1Memory.dataCacheable(parameter, (demandAddress.asBits.bits(63, 3) ## 0.B(3)).asUInt, 8)
    else false.B
    val lineCandidate = if lineRefill then
      (demandPbmt === 0.U(2)) & demandLoad & !demandStore & !demandAtomic & !split & (if parameter.enableTranslation then true.B else !inputSplit) & (demandSize <= 3.U(3)) &
        DitDahA1Memory.dataCacheable(parameter, (demandAddress.asBits.bits(63, 6) ## 0.B(6)).asUInt, 64)
    else false.B
    val initialSize = if lineRefill then lineCandidate.?(6.U(3), refillCandidate.?(3.U(3), demandSize)) else demandSize
    val initialAddress = if lineRefill then lineCandidate.?(
      (demandAddress.asBits.bits(63, 6) ## 0.B(6)).asUInt,
      refillCandidate.?((demandAddress.asBits.bits(63, 3) ## 0.B(3)).asUInt, demandAddress)) else demandAddress
    val checkedAddress = refilling.?((heldAddress.asBits.bits(63, 3) ## 0.B(3)).asUInt, exact.?(heldAddress, initialAddress))
    val checkedSize = refilling.?(3.U(3), exact.?(current.memorySize, initialSize))
    val blockPermissions = Option.when(cacheBlocks && parameter.pmpEntries != 0)(Reg(UInt(3)))
    val pmpPermissions = Wire(UInt(3))
    pmpPermissions := 7.U(3)
    val pmpPermitted = if parameter.pmpEntries == 0 then true.B else
      val pmp = DitDahA1Pmp.instantiate(parameter)
      pmp.io.state :<= io.pmp.get
      pmp.io.address := checkedAddress
      pmp.io.size := checkedSize
      pmp.io.write := !refilling & !exact & demandStore
      pmp.io.fetch := false.B
      pmp.io.atomic := !refilling & !exact & demandLoad & demandStore
      pmp.io.management.foreach(_ := management)
      pmp.io.privilege := (if parameter.enableTranslation then privilege.get
        else if checkRefill || fragments then (refilling | exact | preparing).?(privilege.get, io.privilege) else io.privilege)
      pmp.io.permissions.foreach(pmpPermissions := _)
      pmp.io.allowed
    val debugging = if parameter.enableTranslation then debugOrigin.getOrElse(false.B)
      else if checkRefill || fragments then (refilling | exact | preparing).?(debugOrigin.getOrElse(false.B), io.debugMode.getOrElse(false.B))
      else io.debugMode.getOrElse(false.B)
    val permitted = pmpPermitted | (debugging & DitDahA1Memory.debugWindow(parameter, checkedAddress, checkedSize))
    val initialState = if checkRefill && lineRefill then
      permitted.?(1.U(stateBits), (lineCandidate & refillCandidate).?(6.U(stateBits), 7.U(stateBits)))
    else if checkRefill then refillCandidate.?(6.U(stateBits), 1.U(stateBits)) else 1.U(stateBits)
    val splitAllowed = parameter.blockMemoryRegions.filter(_.size >= 8).foldLeft[Referable[Bool]](false.B) { (allowed, region) =>
      val supported = management.?(((region.readable || region.writable) && (!region.writable || region.readable)).B,
        (region.readable && region.writable && !region.device).B)
      allowed | (block.?(supported & (region.size >= 64).B &
        ((demandAddress.asBits.bits(63, 6) ## 0.B(6)).asUInt >= region.base.U(64)) &
        ((demandAddress.asBits.bits(63, 6) ## 0.B(6)).asUInt <= (region.base + region.size - 64).max(BigInt(0)).U(64)),
        !region.device.B & (demandAddress >= region.base.U(64)) & (demandAddress < (region.base + region.size).U(64))))
    }
    val mixedPermissions = blockPermissions.map(p => block & (state === 7.U(stateBits)) &
      (offset.get =/= 0.U(offsetBits)) & (pmpPermissions =/= p)).getOrElse(false.B)
    val denied = (!permitted & (if lineRefill then !lineCandidate & !refillCandidate else true.B)) | (split &
      (!splitAllowed | (!block & DitDahA1Memory.device(parameter, demandAddress, demandPbmt)))) | mixedPermissions
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
      io.input.ready := (state === 0.U(stateBits)) & available & !serial & !split & (!inputSplit | !busy) & !io.cancel.get & !poisoned.get & !abandoned &
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
      val device = DitDahA1Memory.device(parameter, heldAddress, pbmt.getOrElse(0.U(2)))
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
    request.bits.address := heldAddress
    request.bits.data := offset.map(n => (current.storeData >> (n.asBits.bits(2, 0) ## 0.B(3)).asUInt).asBits.bits(63, 0).asUInt).getOrElse(current.storeData)
    request.bits.size := serviceSize
    request.bits.mask := 0.U(8)
    for size <- 0 to 3 do
      when(current.store & !management & (serviceSize === size.U(3))) { request.bits.mask := ((1 << (1 << size)) - 1).U(8) }
    request.bits.tag := owner.getOrElse(current.instruction.tag)
    request.bits.write := current.store & !management
    request.bits.fetch := false.B
    request.bits.privileged := privilege.map(_ =/= 0.U(2)).getOrElse(privileged.getOrElse(true.B))
    request.bits.atomic := current.atomic
    request.bits.atomicOperation := current.atomic.?(operation, 0.U(5))
    request.bits.cacheOperation := management.?(3.U(2), 0.U(2))
    request.bits.scEligible := scEligible.getOrElse(false.B)
    request.bits.refillSize := refillSize.getOrElse(0.U(3))
    request.bits.pbmt.foreach(_ := pbmt.get)
    request.bits.debug.foreach(_ := debugOrigin.get)
    response.ready := state === 2.U(stateBits)
    io.translation.foreach { t =>
      t.request.valid := state === 4.U(stateBits)
      t.request.bits.address := block.?(current.address, serviceAddress)
      t.request.bits.privilege := privilege.get
      t.request.bits.fetch := false.B
      t.request.bits.write := current.store
      t.request.bits.atomic := current.atomic
      t.request.bits.management.foreach(_ := management)
      t.response.ready := state === 5.U(stateBits)
      when(t.request.valid & t.request.ready) { state := 5.U(stateBits) }
      when(t.response.valid & t.response.ready) {
        pbmt.foreach(_ := t.response.bits.pbmt.get)
        physicalAddress.get := t.response.bits.address
        scEligible.foreach(value => value := value & (t.response.bits.address === reservedAddress))
        updated.instruction.fault := t.response.bits.fault
        updated.instruction.cause := t.response.bits.fault.?(t.response.bits.cause, 0.U(64))
        updated.instruction.tval := t.response.bits.fault.?(faultAddress, 0.U(64))
        state := block.?((if parameter.pmpEntries != 0 then 7 else 6).U(stateBits), initialState)
        refillSize.foreach(_ := initialGrant)
        when(!t.response.bits.fault & denied) {
          updated.instruction.fault := true.B
          updated.instruction.cause := current.store.?(7.U(64), 5.U(64))
          updated.instruction.tval := faultAddress
          state := 3.U(stateBits)
        }
        when(t.response.bits.fault) { state := 3.U(stateBits) }
      }
    }
    io.reservation.foreach { port =>
      val lr = current.atomic & (operation === 2.U(5))
      val watched = lr.?(physicalAddress.getOrElse(current.address), reservedAddress)
      val doubleword = lr.?(current.memorySize === 3.U(3), reservedDoubleword.get)
      port.address := (watched.asBits.bits(63, 3) ## 0.B(3)).asUInt
      port.mask := (doubleword.?(255.U(8), 15.U(8)) << watched.asBits.bits(2, 0).asUInt).asBits.bits(7, 0).asUInt
      val live = if !concurrent then (state === 2.U(stateBits)) | (request.valid & request.ready) else
        (0 until 2).map(n => (owner.get === n.U(1)) & !killed.get(n) &
          (pending.get(n) | (request.valid & request.ready))).reduce(_ | _)
      when(port.begin & lr & live & !current.instruction.fault & !poisoned.getOrElse(false.B) & !io.cancel.getOrElse(false.B)) {
        reserved.get := true.B
        reservedWord.get := watched.asBits.bits(parameter.physicalAddressBits - 1, 2).asUInt
        reservedDoubleword.get := doubleword
      }
    }
    when(io.input.valid & io.input.ready) {
      privileged.foreach(_ := (io.privilege =/= 0.U(2)))
      debugOrigin.foreach(_ := io.debugMode.get)
      privilege.foreach(_ := io.privilege)
      updated :<= io.input.bits
      updated.address := inputAddress
      pointerMask.foreach(_ := io.pointerMask.get)
      virtualPointers.foreach(_ := io.virtualPointers.get)
      splitting.foreach(_ := inputSplit)
      offset.foreach(_ := 0.U(offsetBits))
      when(inputSplit) { updated.value := 0.U(64) }
      refillSize.foreach(_ := (if !parameter.enableTranslation then initialGrant else 0.U(3)))
      scEligible.foreach(_ := io.input.bits.atomic & (inputOperation === 3.U(5)) & reserved.get & !io.reservation.get.invalidate &
        (if parameter.enableTranslation then true.B else inputAddress === reservedAddress) &
        (io.input.bits.memorySize === reservedDoubleword.get.?(3.U(3), 2.U(3))))
      when(io.input.bits.atomic) { reserved.foreach(_ := false.B) }
      state := (if parameter.enableTranslation then 4.U(stateBits) else initialState)
      if parameter.pmpEntries != 0 && !parameter.enableTranslation then
        when(!io.input.bits.instruction.fault & !inputSplit & denied) {
          updated.instruction.fault := true.B
          updated.instruction.cause := io.input.bits.store.?(7.U(64), 5.U(64))
          updated.instruction.tval := inputAddress
          state := 3.U(stateBits)
        }
      if fragments then when(inputSplit) { state := inputBlock.?((if parameter.enableTranslation then 4 else if parameter.pmpEntries != 0 then 7 else 6).U(stateBits), 4.U(stateBits)) }
      when(!io.input.bits.instruction.fault & misaligned & !inputSplit) {
        updated.instruction.fault := true.B
        updated.instruction.cause := io.input.bits.store.?(6.U(64), 4.U(64))
        updated.instruction.tval := inputAddress
        state := 3.U(stateBits)
      }
      when(io.input.bits.instruction.fault) { state := 3.U(stateBits) }
    }
    if fragments then
      when(preparing) {
        state := denied.?(3.U(stateBits), 1.U(stateBits))
        when(block & (state === 7.U(stateBits)) & !denied) {
          blockPermissions.foreach(p => when(offset.get === 0.U(offsetBits)) { p := pmpPermissions })
          state := finalFragment.?(6.U(stateBits), 7.U(stateBits))
          offset.get := finalFragment.?(0.U(offsetBits), nextOffset.get.asBits.bits(offsetBits - 1, 0).asUInt)
        }
        when(denied) {
          updated.instruction.fault := true.B
          updated.instruction.cause := current.store.?(7.U(64), 5.U(64))
          updated.instruction.tval := faultAddress
        }
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
      state := (if concurrent then split.?(2.U(stateBits), 0.U(stateBits)) else 2.U(stateBits))
      if concurrent then
        for n <- 0 until 2 do
          when(owner.get === n.U(1)) { contexts.get(n) := 2.U(2); address.foreach(_(n) := request.bits.address.asBits.bits(63, 3).asUInt) }
    }
    if concurrent then
      response.ready := pending.get.foldLeft[Referable[Bool]](false.B)(_ | _)
      val known = (0 until 2).map(n => pending.get(n) & (response.bits.tag === n.U(8))).reduce(_ | _)
      when(response.valid & response.ready & !known) { poisoned.get := true.B; reserved.foreach(_ := false.B) }
    for n <- packets.indices do
      val completed = packets(n)
      val identity = if concurrent then n.U(8) else completed.instruction.tag
      val matching = if concurrent then pending.get(n) & (response.bits.tag === identity) else true.B
      when(response.valid & response.ready & matching) {
        val value = if !parameter.enableMisaligned then response.bits.data else
          val fragment = Wire(UInt(64))
          fragment := response.bits.data
          for size <- 0 to 2 do
            val bits = 8 << size
            when(serviceSize === size.U(3)) { fragment := (0.B(64 - bits) ## response.bits.data.asBits.bits(bits - 1, 0)).asUInt }
          split.?((completed.value.asBits | (fragment << (offset.get.asBits.bits(2, 0) ## 0.B(3)).asUInt).asBits.bits(63, 0)).asUInt, response.bits.data)
        when(completed.load | completed.atomic) {
          completed.value := value
          for size <- 0 to 2 do
            val bits = 8 << size
            val low = value.asBits.bits(bits - 1, 0)
            val high = ((if parameter.floatingPointBits > bits then completed.fpWrite.get else false.B) | (!completed.unsignedLoad & low.bit(bits - 1))).?(((BigInt(1) << (64 - bits)) - 1).B(64 - bits), 0.B(64 - bits))
            when((!split | finalFragment) & (completed.memorySize === size.U(3))) { completed.value := (high ## low).asUInt }
        }
        when(response.bits.fault | poisoned.getOrElse(false.B) | (if concurrent then !response.bits.last else false.B) | (response.bits.tag =/= identity)) {
          completed.instruction.fault := true.B
          completed.instruction.cause := completed.store.?(7.U(64), 5.U(64))
          completed.instruction.tval := split.?(faultAddress, completed.address)
        }
        when(completed.atomic & (operation === 2.U(5)) &
          (response.bits.fault | (response.bits.tag =/= identity) | !response.bits.last | completed.instruction.fault |
            poisoned.getOrElse(false.B) | (if concurrent then killed.get(n) | io.cancel.get else false.B))) {
          reserved.foreach(_ := false.B)
        }
        if !concurrent then state := 3.U(stateBits)
        else
          when(response.bits.last) {
            contexts.get(n) := 3.U(2)
            when(split) { state := 3.U(stateBits) }
          }
        if fragments then
          when(split & !management & !finalFragment & !response.bits.fault & response.bits.last & (response.bits.tag === identity) &
            !completed.instruction.fault & !poisoned.getOrElse(false.B) &
            (if concurrent then !killed.get(n) & !io.cancel.get else true.B)) {
            offset.get := nextOffset.get.asBits.bits(offsetBits - 1, 0).asUInt
            state := zero.?(6.U(stateBits), 4.U(stateBits))
            contexts.foreach(_(n) := 1.U(2))
          }
      }
    when(io.output.valid & io.output.ready) { splitting.foreach(_ := false.B); offset.foreach(_ := 0.U(offsetBits)) }
    if !concurrent then
      when(io.output.valid & io.output.ready) { state := 0.U(stateBits) }
    else
      when(io.cancel.get) { reserved.foreach(_ := false.B) }
    io.reservation.foreach(port => when(port.invalidate) { reserved.get := false.B })
