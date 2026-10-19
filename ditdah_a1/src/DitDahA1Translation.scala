// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

class TranslationEntry extends Bundle:
  val vpn = Aligned(UInt(27))
  val pte = Aligned(UInt(64))
  val level = Aligned(UInt(2))

class DitDahA1TranslationIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val state = Flipped(new TranslationState)
  val ports = Flipped(Vec(2, new TranslationPort))
  val cancelInstruction = Flipped(Bool())
  val invalidate = Option.when(parameter.tlbEntries != 0)(Flipped(Bool()))
  val pmp = Option.when(parameter.pmpEntries != 0)(Flipped(new PmpState(parameter)))
  val memory = Aligned(new MemoryPort)

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
    val tlb = Option.when(parameter.tlbEntries != 0)(Reg(Vec(parameter.tlbEntries, new TranslationEntry)))
    val tlbValid = Option.when(tlb.isDefined)(RegInit(0.B(parameter.tlbEntries)))
    val replacementBits = if tlb.isDefined then Integer.numberOfTrailingZeros(parameter.tlbEntries) else 1
    val replacement = Option.when(tlb.isDefined)(RegInit(0.U(replacementBits)))
    val refillAllowed = Option.when(tlb.isDefined)(RegInit(false.B))
    val cancelled = killed | (io.cancelInstruction & !owner)
    val instruction = io.ports(0).request.valid & !io.cancelInstruction
    val data = io.ports(1).request.valid
    val selected = data & (!instruction | next)
    val accessCause = request.fetch.?(1.U(64), request.write.?(7.U(64), 5.U(64)))
    val pageCause = request.fetch.?(12.U(64), request.write.?(15.U(64), 13.U(64)))
    def leafDenied(pte: Referable[Bits])(using Arena, Context, Block, InstanceContext): Referable[Bool] =
      val permitted = request.fetch.?(pte.bit(3), request.write.?(pte.bit(2), pte.bit(1) | (mxr & pte.bit(3))))
      val user = (request.privilege === 0.U(2)).?(pte.bit(4), !pte.bit(4) | (sum & !request.fetch))
      !permitted | !user | !pte.bit(6) | (request.write & !pte.bit(7))
    def mapped(pte: Referable[Bits], pageLevel: Referable[UInt])(using Arena, Context, Block, InstanceContext): Referable[UInt] =
      (pageLevel === 2.U(2)).?((0.B(8) ## pte.bits(53, 28) ## request.address.asBits.bits(29, 0)).asUInt,
        (pageLevel === 1.U(2)).?((0.B(8) ## pte.bits(53, 19) ## request.address.asBits.bits(20, 0)).asUInt,
          (0.B(8) ## pte.bits(53, 10) ## request.address.asBits.bits(11, 0)).asUInt))
    def matches(left: Referable[UInt], right: Referable[UInt], pageLevel: Referable[UInt])(using Arena, Context, Block, InstanceContext): Referable[Bool] =
      (left.asBits.bits(26, 18) === right.asBits.bits(26, 18)) &
        ((pageLevel === 2.U(2)) | ((left.asBits.bits(17, 9) === right.asBits.bits(17, 9)) &
          ((pageLevel === 1.U(2)) | (left.asBits.bits(8, 0) === right.asBits.bits(8, 0)))))
    for i <- 0 until 2 do
      val port = io.ports(i)
      port.request.ready := (state === 0.U(3)) & (selected === (i == 1).B) &
        (if i == 0 then !io.cancelInstruction else true.B)
      port.response.valid := (state === 4.U(3)) & (owner === (i == 1).B)
      port.response.bits.address := address
      port.response.bits.fault := fault
      port.response.bits.cause := fault.?(pageFault.?(pageCause, accessCause), 0.U(64))
      when(port.request.valid & port.request.ready) {
        val incoming = port.request.bits
        val mode = io.state.satp.asBits.bits(63, 60).asUInt
        val canonical = incoming.address.asBits.bits(63, 39) ===
          incoming.address.asBits.bit(38).?(((BigInt(1) << 25) - 1).B(25), 0.B(25))
        owner := (i == 1).B
        request :<= incoming
        sum := io.state.sum
        mxr := io.state.mxr
        address := incoming.address
        level := 2.U(2)
        fault := false.B
        pageFault := false.B
        killed := false.B
        refillAllowed.foreach(_ := true.B)
        state := 4.U(3)
        when((incoming.privilege =/= 3.U(2)) & (mode =/= 0.U(4))) {
          address := (0.B(8) ## io.state.satp.asBits.bits(43, 0) ## incoming.address.asBits.bits(38, 30) ## 0.B(3)).asUInt
          state := (if tlb.isDefined then 5 else 1).U(3)
          when((mode =/= 8.U(4)) | !canonical) {
            address := incoming.address
            fault := true.B
            pageFault := true.B
            state := 4.U(3)
          }
        }
      }
      when(port.response.valid & port.response.ready) {
        next := !owner
        state := 0.U(3)
      }
    tlb.foreach { entries =>
      val vpn = request.address.asBits.bits(38, 12).asUInt
      val hits = (0 until parameter.tlbEntries).map(i => tlbValid.get.bit(i) & matches(entries(i).vpn, vpn, entries(i).level))
      val hit = hits.reduce(_ | _) & !io.invalidate.get
      val pte = hits.indices.reverse.foldLeft[Referable[UInt]](0.U(64))((value, i) => hits(i).?(entries(i).pte, value)).asBits
      val pageLevel = hits.indices.reverse.foldLeft[Referable[UInt]](0.U(2))((value, i) => hits(i).?(entries(i).level, value))
      when(state === 5.U(3)) {
        state := 1.U(3)
        when(hit | cancelled) {
          address := cancelled.?(request.address, mapped(pte, pageLevel))
          fault := !cancelled & leafDenied(pte)
          pageFault := !cancelled & leafDenied(pte)
          state := 4.U(3)
          when(!cancelled & leafDenied(pte)) { address := request.address }
        }
      }
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
    read.bits.scEligible := false.B
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
          val leafFault = leafDenied(pte) | !aligned
          val pointerFault = (level === 0.U(2)) | pte.bit(4) | pte.bit(6) | pte.bit(7)
          when(invalid | leaf.?(leafFault, pointerFault)) {
            fault := true.B
            pageFault := true.B
          }.otherwise {
            when(leaf) {
              address := mapped(pte, level)
              tlb.foreach { entries =>
                when(refillAllowed.get & !io.invalidate.get) {
                  val vpn = request.address.asBits.bits(38, 12).asUInt
                  val retained = (0 until parameter.tlbEntries).reverse.map { i =>
                    val selected = replacement.get === i.U(replacementBits)
                    val overlap = matches(entries(i).vpn, vpn, entries(i).level) | matches(entries(i).vpn, vpn, level)
                    when(selected) {
                      entries(i).vpn := vpn
                      entries(i).pte := response.bits.data
                      entries(i).level := level
                    }
                    (selected | (tlbValid.get.bit(i) & !overlap)).asBits
                  }.reduce(_ ## _)
                  tlbValid.get := retained
                  replacement.get := (replacement.get + 1.U(replacementBits)).asBits.bits(replacementBits - 1, 0).asUInt
                }
              }
            }.otherwise {
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
    io.invalidate.foreach { invalidate =>
      when(invalidate) { tlbValid.get := 0.B(parameter.tlbEntries); replacement.get := 0.U(replacementBits); refillAllowed.get := false.B }
    }
