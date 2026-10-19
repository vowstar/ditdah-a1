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
  val translation = Option.when(parameter.enableTranslation)(Aligned(new TranslationPort))
  val memory = Aligned(new MemoryPort)

@generator
object DitDahA1Lsu extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1LsuIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Lsu"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1LsuIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val stateBits = if parameter.enableTranslation then 3 else 2
    val state = RegInit(0.U(stateBits))
    val packet = Reg(new ResultPacket)
    val privileged = Option.when(parameter.enableUserMode && !parameter.enableTranslation)(Reg(Bool()))
    val privilege = Option.when(parameter.enableTranslation)(Reg(UInt(2)))
    val physicalAddress = Option.when(parameter.enableTranslation)(Reg(UInt(64)))
    val reserved = RegInit(false.B)
    val reservedWord = Reg(UInt(parameter.physicalAddressBits - 3))
    val scEligible = Reg(Bool())
    val reservedAddress = (0.B(64 - parameter.physicalAddressBits) ## reservedWord.asBits ## 0.B(3)).asUInt
    val inputOperation = io.input.bits.instruction.instruction.asBits.bits(31, 27).asUInt
    val operation = packet.instruction.instruction.asBits.bits(31, 27).asUInt
    val request = io.memory.request
    val response = io.memory.response
    val permitted = if parameter.pmpEntries == 0 then true.B else
      val pmp = DitDahA1Pmp.instantiate(parameter)
      pmp.io.state :<= io.pmp.get
      pmp.io.address := io.translation.map(_.response.bits.address).getOrElse(io.input.bits.address)
      pmp.io.size := (if parameter.enableTranslation then packet.memorySize else io.input.bits.memorySize)
      pmp.io.write := (if parameter.enableTranslation then packet.store else io.input.bits.store)
      pmp.io.fetch := false.B
      pmp.io.atomic := (if parameter.enableTranslation then packet.load & packet.store else io.input.bits.load & io.input.bits.store)
      pmp.io.privilege := privilege.getOrElse(io.privilege)
      pmp.io.allowed
    io.input.ready := (state === 0.U(stateBits)) & (io.input.bits.instruction.fault | !io.input.bits.store | io.storeAllowed)
    io.output.valid := state === 3.U(stateBits)
    io.output.bits :<= packet
    request.valid := state === 1.U(stateBits)
    request.bits.address := physicalAddress.getOrElse(packet.address)
    request.bits.data := packet.storeData
    request.bits.size := packet.memorySize
    request.bits.mask := 0.U(8)
    for size <- 0 to 3 do
      when(packet.store & (packet.memorySize === size.U(3))) { request.bits.mask := ((1 << (1 << size)) - 1).U(8) }
    request.bits.tag := packet.instruction.tag
    request.bits.write := packet.store
    request.bits.fetch := false.B
    request.bits.privileged := privilege.map(_ =/= 0.U(2)).getOrElse(privileged.getOrElse(true.B))
    request.bits.atomic := packet.atomic
    request.bits.atomicOperation := packet.atomic.?(operation, 0.U(5))
    request.bits.scEligible := scEligible
    response.ready := state === 2.U(stateBits)
    io.translation.foreach { t =>
      t.request.valid := state === 4.U(stateBits)
      t.request.bits.address := packet.address
      t.request.bits.privilege := privilege.get
      t.request.bits.fetch := false.B
      t.request.bits.write := packet.store
      t.response.ready := state === 5.U(stateBits)
      when(t.request.valid & t.request.ready) { state := 5.U(stateBits) }
      when(t.response.valid & t.response.ready) {
        physicalAddress.get := t.response.bits.address
        scEligible := scEligible & (t.response.bits.address === reservedAddress)
        packet.instruction.fault := t.response.bits.fault
        packet.instruction.cause := t.response.bits.fault.?(t.response.bits.cause, 0.U(64))
        packet.instruction.tval := t.response.bits.fault.?(packet.address, 0.U(64))
        state := 1.U(stateBits)
        when(!t.response.bits.fault & !permitted) {
          packet.instruction.fault := true.B
          packet.instruction.cause := packet.store.?(7.U(64), 5.U(64))
          packet.instruction.tval := packet.address
          state := 3.U(stateBits)
        }
        when(t.response.bits.fault) { state := 3.U(stateBits) }
      }
    }
    when(io.input.valid & io.input.ready) {
      privileged.foreach(_ := (io.privilege =/= 0.U(2)))
      privilege.foreach(_ := io.privilege)
      packet :<= io.input.bits
      scEligible := io.input.bits.atomic & (inputOperation === 3.U(5)) & reserved &
        (if parameter.enableTranslation then true.B else io.input.bits.address === reservedAddress) & (io.input.bits.memorySize === 3.U(3))
      when(io.input.bits.atomic) { reserved := false.B }
      state := (if parameter.enableTranslation then 4 else 1).U(stateBits)
      if parameter.pmpEntries != 0 && !parameter.enableTranslation then
        when(!io.input.bits.instruction.fault & !permitted) {
          packet.instruction.fault := true.B
          packet.instruction.cause := io.input.bits.store.?(7.U(64), 5.U(64))
          packet.instruction.tval := io.input.bits.address
          state := 3.U(stateBits)
        }
      val alignment = Wire(UInt(64))
      alignment := 7.U(64)
      for size <- 0 to 2 do
        when(io.input.bits.memorySize === size.U(3)) { alignment := ((1 << size) - 1).U(64) }
      when(!io.input.bits.instruction.fault & ((io.input.bits.address.asBits & alignment.asBits).asUInt =/= 0.U(64))) {
        packet.instruction.fault := true.B
        packet.instruction.cause := io.input.bits.store.?(6.U(64), 4.U(64))
        packet.instruction.tval := io.input.bits.address
        state := 3.U(stateBits)
      }
      when(io.input.bits.instruction.fault) { state := 3.U(stateBits) }
    }
    when(request.valid & request.ready) { state := 2.U(stateBits) }
    when(response.valid & response.ready) {
      when(packet.load | packet.atomic) {
        packet.value := response.bits.data
        for size <- 0 to 2 do
          val bits = 8 << size
          val low = response.bits.data.asBits.bits(bits - 1, 0)
          val high = (!packet.unsignedLoad & low.bit(bits - 1)).?(((BigInt(1) << (64 - bits)) - 1).B(64 - bits), 0.B(64 - bits))
          when(packet.memorySize === size.U(3)) { packet.value := (high ## low).asUInt }
      }
      when(response.bits.fault | (response.bits.tag =/= packet.instruction.tag)) {
        packet.instruction.fault := true.B
        packet.instruction.cause := packet.store.?(7.U(64), 5.U(64))
        packet.instruction.tval := packet.address
      }
      when(packet.atomic & (operation === 2.U(5)) & (packet.memorySize === 3.U(3)) &
        !response.bits.fault & (response.bits.tag === packet.instruction.tag)) {
        reserved := true.B
        reservedWord := physicalAddress.getOrElse(packet.address).asBits.bits(parameter.physicalAddressBits - 1, 3).asUInt
      }
      state := 3.U(stateBits)
    }
    when(io.output.valid & io.output.ready) { state := 0.U(stateBits) }
