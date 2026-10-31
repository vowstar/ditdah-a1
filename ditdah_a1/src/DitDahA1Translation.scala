// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

class TranslationEntry(asidBits: Int = 0) extends Bundle:
  val asid = Option.when(asidBits != 0)(Aligned(UInt(asidBits)))
  val vpn = Aligned(UInt(27))
  val pte = Aligned(UInt(64))
  val level = Aligned(UInt(2))

class DitDahA1TranslationIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val state = Flipped(new TranslationState)
  val ports = Flipped(Vec(2, new TranslationPort))
  val cancelInstruction = Flipped(Bool())
  val invalidate = Option.when(parameter.hasTranslationCache)(Flipped(Bool()))
  val maintenance = Option.when(parameter.preciseTranslationMaintenance)(Flipped(new TranslationMaintenance(parameter)))
  val pmp = Option.when(parameter.pmpEntries != 0)(Flipped(new PmpState(parameter)))
  val memory = Aligned(new MemoryPort(parameter))

@generator
object DitDahA1Translation extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1TranslationIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Translation"
  def architecture(parameter: DitDahA1Parameter) =
    require(parameter.enableTranslation, "Translation requires Sv39 supervisor mode")
    val io = summon[Interface[DitDahA1TranslationIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val state = RegInit(0.U(3))
    val owner = Reg(Bool())
    val next = RegInit(false.B)
    val request = Reg(new TranslationRequest)
    val sum = Reg(Bool())
    val mxr = Reg(Bool())
    val address = Reg(UInt(64))
    val level = Reg(UInt(2))
    val fault = Reg(Bool())
    val pageFault = Reg(Bool())
    val killed = RegInit(false.B)
    val held = Seq.fill(2)(RegInit(false.B))
    val heldResponse = Seq.fill(2)(Reg(new TranslationResponse))
    val tlb = Option.when(parameter.tlbEntries != 0)(Reg(Vec(parameter.tlbEntries, new TranslationEntry(parameter.asidBits))))
    val tlbValid = Option.when(tlb.isDefined)(RegInit(0.B(parameter.tlbEntries)))
    val replacementBits = if tlb.isDefined then Integer.numberOfTrailingZeros(parameter.tlbEntries) else 1
    val replacement = Option.when(tlb.isDefined)(RegInit(0.U(replacementBits)))
    val instructionTlb = Option.when(parameter.iTlbEntries != 0)(Reg(Vec(parameter.iTlbEntries, new TranslationEntry)))
    val dataTlb = Option.when(parameter.dTlbEntries != 0)(Reg(Vec(parameter.dTlbEntries, new TranslationEntry)))
    val capacities = Seq(parameter.tlbEntries, parameter.iTlbEntries, parameter.dTlbEntries)
    val banks = Seq(tlb, instructionTlb, dataTlb)
    val instructionValid = Option.when(instructionTlb.isDefined)(RegInit(0.B(parameter.iTlbEntries)))
    val dataValid = Option.when(dataTlb.isDefined)(RegInit(0.B(parameter.dTlbEntries)))
    val instructionReplacement = Option.when(instructionTlb.isDefined)(RegInit(0.U(Integer.numberOfTrailingZeros(parameter.iTlbEntries))))
    val dataReplacement = Option.when(dataTlb.isDefined)(RegInit(0.U(Integer.numberOfTrailingZeros(parameter.dTlbEntries))))
    val valid = Seq(tlbValid, instructionValid, dataValid)
    val positions = Seq(replacement, instructionReplacement, dataReplacement)
    val refillAllowed = Option.when(parameter.hasTranslationCache)(RegInit(false.B))
    val currentAsid = if parameter.asidBits == 0 then 0.U(1) else io.state.satp.asBits.bits(43 + parameter.asidBits, 44).asUInt
    val walkAsid = Option.when(parameter.asidBits != 0 && tlb.isDefined)(Reg(UInt(parameter.asidBits)))
    val globalMapping = Option.when(parameter.preciseTranslationMaintenance)(RegInit(false.B))
    val maintaining = io.invalidate.getOrElse(false.B) | io.maintenance.map(_.valid).getOrElse(false.B)
    val cancelled = killed | (io.cancelInstruction & !owner)
    val accessCause = request.fetch.?(1.U(64), request.write.?(7.U(64), 5.U(64)))
    val pageCause = request.fetch.?(12.U(64), request.write.?(15.U(64), 13.U(64)))
    def leafDenied(pte: Referable[Bits], access: Referable[TranslationRequest], accessSum: Referable[Bool],
      accessMxr: Referable[Bool])(using Arena, Context, Block, InstanceContext): Referable[Bool] =
      val permitted = access.fetch.?(pte.bit(3), access.write.?(pte.bit(2), pte.bit(1) | (accessMxr & pte.bit(3))))
      val user = (access.privilege === 0.U(2)).?(pte.bit(4), !pte.bit(4) | (accessSum & !access.fetch))
      !permitted | !user | !pte.bit(6) | (access.write & !pte.bit(7))
    def mapped(pte: Referable[Bits], pageLevel: Referable[UInt], va: Referable[UInt])
      (using Arena, Context, Block, InstanceContext): Referable[UInt] =
      (pageLevel === 2.U(2)).?((0.B(8) ## pte.bits(53, 28) ## va.asBits.bits(29, 0)).asUInt,
        (pageLevel === 1.U(2)).?((0.B(8) ## pte.bits(53, 19) ## va.asBits.bits(20, 0)).asUInt,
          (0.B(8) ## pte.bits(53, 10) ## va.asBits.bits(11, 0)).asUInt))
    def matches(left: Referable[UInt], right: Referable[UInt], pageLevel: Referable[UInt])(using Arena, Context, Block, InstanceContext): Referable[Bool] =
      (left.asBits.bits(26, 18) === right.asBits.bits(26, 18)) &
        ((pageLevel === 2.U(2)) | ((left.asBits.bits(17, 9) === right.asBits.bits(17, 9)) &
          ((pageLevel === 1.U(2)) | (left.asBits.bits(8, 0) === right.asBits.bits(8, 0)))))
    def update(bank: Int, vpn: Referable[UInt], pte: Referable[UInt], pageLevel: Referable[UInt], allocate: Referable[Bool], asid: Referable[UInt])
      (using Arena, Context, Block, InstanceContext): Unit =
      banks(bank).foreach { entries =>
        val bits = Integer.numberOfTrailingZeros(capacities(bank))
        val retained = (0 until capacities(bank)).reverse.map { n =>
          val selected = allocate & (positions(bank).get === n.U(bits))
          val sameSpace = entries(n).asid.map(_ === asid).getOrElse(true.B) | entries(n).pte.asBits.bit(5) | pte.asBits.bit(5)
          val overlap = sameSpace & (matches(entries(n).vpn, vpn, entries(n).level) | matches(entries(n).vpn, vpn, pageLevel))
          when(selected) {
            entries(n).vpn := vpn; entries(n).pte := pte; entries(n).level := pageLevel
            entries(n).asid.foreach(_ := asid)
          }
          (selected | (valid(bank).get.bit(n) & !overlap)).asBits
        }.reduce(_ ## _)
        valid(bank).get := retained
        when(allocate) { positions(bank).get := (positions(bank).get + 1.U(bits)).asBits.bits(bits - 1, 0).asUInt }
      }
    val available = (0 until 2).map { i =>
      !held(i) & !((state =/= 0.U(3)) & (owner === (i == 1).B)) &
        !maintaining & (if i == 0 then !io.cancelInstruction else true.B)
    }
    val lookups = (0 until 2).map { i =>
      val incoming = io.ports(i).request.bits
      val mode = io.state.satp.asBits.bits(63, 60).asUInt
      val paged = (incoming.privilege =/= 3.U(2)) & (mode =/= 0.U(4))
      val canonical = incoming.address.asBits.bits(63, 39) ===
        incoming.address.asBits.bit(38).?(((BigInt(1) << 25) - 1).B(25), 0.B(25))
      val invalid = paged & ((mode =/= 8.U(4)) | !canonical)
      val choices = Seq(i + 1, 0).flatMap(bank => banks(bank).toSeq.flatMap(entries =>
        (0 until capacities(bank)).map(n => (entries(n), valid(bank).get.bit(n)))))
      val hits = choices.map { (entry, active) => active &
        matches(entry.vpn, incoming.address.asBits.bits(38, 12).asUInt, entry.level) &
          (entry.asid.map(_ === currentAsid).getOrElse(true.B) | entry.pte.asBits.bit(5)) }
      val hit = hits.reduceOption(_ | _).getOrElse(false.B)
      val pte = choices.indices.reverse.foldLeft[Referable[UInt]](0.U(64))(
        (value, n) => hits(n).?(choices(n)._1.pte, value)).asBits
      val pageLevel = choices.indices.reverse.foldLeft[Referable[UInt]](0.U(2))(
        (value, n) => hits(n).?(choices(n)._1.level, value))
      val failed = invalid | (paged & hit & leafDenied(pte, incoming, io.state.sum, io.state.mxr))
      val result = Wire(new TranslationResponse)
      result.address := (paged & hit & !failed).?(mapped(pte, pageLevel, incoming.address), incoming.address)
      result.fault := failed
      result.cause := failed.?(incoming.fetch.?(12.U(64), incoming.write.?(15.U(64), 13.U(64))), 0.U(64))
      val promote = paged & !failed & !hits.take(capacities(i + 1)).reduceOption(_ | _).getOrElse(false.B) &
        hits.drop(capacities(i + 1)).reduceOption(_ | _).getOrElse(false.B)
      (!paged | invalid | hit, result, promote, pte.asUInt, pageLevel)
    }
    val misses = (0 until 2).map(i => io.ports(i).request.valid & available(i) & !lookups(i)._1)
    val selected = misses(1) & (!misses(0) | next)
    for i <- 0 until 2 do
      val port = io.ports(i)
      val fast = lookups(i)._1
      val fastResponse = port.request.valid & available(i) & fast
      val walked = (state === 4.U(3)) & (owner === (i == 1).B)
      port.request.ready := available(i) & (fast | ((state === 0.U(3)) & (selected === (i == 1).B)))
      port.response.valid := held(i) | walked | fastResponse
      port.response.bits :<= lookups(i)._2
      when(walked) {
        port.response.bits.address := address
        port.response.bits.fault := fault
        port.response.bits.cause := fault.?(pageFault.?(pageCause, accessCause), 0.U(64))
      }
      when(held(i)) { port.response.bits :<= heldResponse(i) }
      when(fastResponse & !port.response.ready) {
        held(i) := true.B
        heldResponse(i) :<= lookups(i)._2
      }
      when(held(i) & port.response.ready) { held(i) := false.B }
      when(port.request.valid & port.request.ready & lookups(i)._3 & !(io.memory.response.valid & io.memory.response.ready)) {
        update(i + 1, port.request.bits.address.asBits.bits(38, 12).asUInt, lookups(i)._4, lookups(i)._5, true.B, currentAsid)
      }
      when(port.request.valid & port.request.ready & !fast) {
        val incoming = port.request.bits
        owner := (i == 1).B
        request :<= incoming
        sum := io.state.sum
        mxr := io.state.mxr
        walkAsid.foreach(_ := currentAsid)
        globalMapping.foreach(_ := false.B)
        address := (0.B(8) ## io.state.satp.asBits.bits(43, 0) ## incoming.address.asBits.bits(38, 30) ## 0.B(3)).asUInt
        level := 2.U(2)
        fault := false.B
        pageFault := false.B
        killed := false.B
        refillAllowed.foreach(_ := true.B)
        state := 1.U(3)
      }
      when(walked & port.response.ready) {
        next := !owner
        state := 0.U(3)
      }
    val ordinary = parameter.memoryRegions.filter(r => r.readable && !r.device && r.size >= 8)
      .foldLeft[Referable[Bool]](false.B) { (permitted, region) =>
        permitted | ((address >= region.base.U(64)) & (address <= (region.base + region.size - 8).U(64)))
      }
    val protectedRead = if parameter.pmpEntries == 0 then true.B else
      val pmp = DitDahA1Pmp.instantiate(parameter)
      pmp.io.state :<= io.pmp.get
      pmp.io.address := address
      pmp.io.size := 3.U(3)
      pmp.io.write := false.B
      pmp.io.fetch := false.B
      pmp.io.atomic := false.B
      pmp.io.privilege := 1.U(2)
      pmp.io.allowed
    val allowed = ordinary & protectedRead &
      (address <= ((BigInt(1) << parameter.physicalAddressBits) - 8).U(64))
    val read = io.memory.request
    val response = io.memory.response
    read.valid := state === 2.U(3)
    read.bits.address := address
    read.bits.data := 0.U(64)
    read.bits.size := 3.U(3)
    read.bits.mask := 0.U(8)
    read.bits.tag := 0.U(8)
    read.bits.write := false.B
    read.bits.fetch := false.B
    read.bits.privileged := true.B
    read.bits.atomic := false.B
    read.bits.atomicOperation := 0.U(5)
    read.bits.cacheOperation := 0.U(2)
    read.bits.debug.foreach(_ := false.B)
    read.bits.scEligible := false.B
    read.bits.refillSize := 0.U(3)
    response.ready := state === 3.U(3)
    when(state === 1.U(3)) {
      state := 2.U(3)
      when(!allowed | cancelled) {
        address := request.address
        fault := !cancelled
        state := 4.U(3)
      }
    }
    when(read.valid & read.ready) { state := 3.U(3) }
    when(response.valid & response.ready) {
      address := request.address
      state := 4.U(3)
      when(!cancelled) {
        when(response.bits.fault | (response.bits.tag =/= 0.U(8))) {
          fault := true.B
        }.otherwise {
          val pte = response.bits.data.asBits
          val leaf = pte.bit(1) | pte.bit(3)
          val invalid = !pte.bit(0) | (!pte.bit(1) & pte.bit(2)) | (pte.bits(63, 54) =/= 0.B(10))
          val aligned = ((level =/= 2.U(2)) | (pte.bits(27, 10) === 0.B(18))) &
            ((level =/= 1.U(2)) | (pte.bits(18, 10) === 0.B(9)))
          val leafFault = leafDenied(pte, request, sum, mxr) | !aligned
          val pointerFault = (level === 0.U(2)) | pte.bit(4) | pte.bit(6) | pte.bit(7)
          when(invalid | leaf.?(leafFault, pointerFault)) {
            fault := true.B
            pageFault := true.B
          }.otherwise {
            when(leaf) {
              address := mapped(pte, level, request.address)
              if parameter.hasTranslationCache then
                when(refillAllowed.get & !maintaining) {
                  val vpn = request.address.asBits.bits(38, 12).asUInt
                  for bank <- banks.indices do
                    update(bank, vpn, (pte | globalMapping.getOrElse(false.B).?(32.B(64), 0.B(64))).asUInt,
                      level, (bank == 0).B | (owner === (bank == 2).B), walkAsid.getOrElse(currentAsid))
                }
            }.otherwise {
              globalMapping.foreach(_ := globalMapping.get | pte.bit(5))
              val vpn = (level === 2.U(2)).?(request.address.asBits.bits(29, 21), request.address.asBits.bits(20, 12))
              address := (0.B(8) ## pte.bits(53, 10) ## vpn ## 0.B(3)).asUInt
              level := (level - 1.U(2)).asBits.bits(1, 0).asUInt
              state := 1.U(3)
            }
          }
        }
      }
    }
    when(io.cancelInstruction & !owner & (state =/= 0.U(3))) { killed := true.B }
    io.maintenance.foreach { maintenance =>
      when(maintenance.valid) {
        val canonical = maintenance.address.asBits.bits(63, 39) ===
          maintenance.address.asBits.bit(38).?(((BigInt(1) << 25) - 1).B(25), 0.B(25))
        for bank <- banks.indices do banks(bank).foreach { entries =>
          valid(bank).get := (0 until capacities(bank)).reverse.map { n =>
            val addressMatches = !maintenance.addressValid | (canonical &
              matches(entries(n).vpn, maintenance.address.asBits.bits(38, 12).asUInt, entries(n).level))
            val asidMatches = !maintenance.asidValid | (!entries(n).pte.asBits.bit(5) &
              (entries(n).asid.getOrElse(currentAsid) === maintenance.asid))
            val discard = maintenance.fence.?(addressMatches & asidMatches, (bank != 0).B)
            (valid(bank).get.bit(n) & !discard).asBits
          }.reduce(_ ## _)
        }
        refillAllowed.get := false.B
      }
    }
    io.invalidate.foreach { invalidate =>
      when(invalidate) {
        for bank <- banks.indices if banks(bank).isDefined do
          valid(bank).get := 0.B(capacities(bank))
          positions(bank).get := 0.U(Integer.numberOfTrailingZeros(capacities(bank)))
        refillAllowed.get := false.B
      }
    }
