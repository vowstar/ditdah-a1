// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1TranslationIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val state = Flipped(new TranslationState)
  val ports = Flipped(Vec(2, new TranslationPort))
  val cancelInstruction = Flipped(Bool())
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
    val cancelled = killed | (io.cancelInstruction & !owner)
    val instruction = io.ports(0).request.valid & !io.cancelInstruction
    val data = io.ports(1).request.valid
    val selected = data & (!instruction | next)
    val accessCause = request.fetch.?(1.U(64), request.write.?(7.U(64), 5.U(64)))
    val pageCause = request.fetch.?(12.U(64), request.write.?(15.U(64), 13.U(64)))
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
        state := 4.U(3)
        when((incoming.privilege =/= 3.U(2)) & (mode =/= 0.U(4))) {
          address := (0.B(8) ## io.state.satp.asBits.bits(43, 0) ## incoming.address.asBits.bits(38, 30) ## 0.B(3)).asUInt
          state := 1.U(3)
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
          val permitted = request.fetch.?(pte.bit(3), request.write.?(pte.bit(2), pte.bit(1) | (mxr & pte.bit(3))))
          val user = (request.privilege === 0.U(2)).?(pte.bit(4), !pte.bit(4) | (sum & !request.fetch))
          val aligned = ((level =/= 2.U(2)) | (pte.bits(27, 10) === 0.B(18))) &
            ((level =/= 1.U(2)) | (pte.bits(18, 10) === 0.B(9)))
          val leafFault = !permitted | !user | !aligned | !pte.bit(6) | (request.write & !pte.bit(7))
          val pointerFault = (level === 0.U(2)) | pte.bit(4) | pte.bit(6) | pte.bit(7)
          when(invalid | leaf.?(leafFault, pointerFault)) {
            fault := true.B
            pageFault := true.B
          }.otherwise {
            when(leaf) {
              address := (0.B(8) ## pte.bits(53, 10) ## request.address.asBits.bits(11, 0)).asUInt
              when(level === 1.U(2)) { address := (0.B(8) ## pte.bits(53, 19) ## request.address.asBits.bits(20, 0)).asUInt }
              when(level === 2.U(2)) { address := (0.B(8) ## pte.bits(53, 28) ## request.address.asBits.bits(29, 0)).asUInt }
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
