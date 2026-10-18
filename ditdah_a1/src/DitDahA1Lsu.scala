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
  val input = Flipped(new Decoupled(new ResultPacket))
  val output = Aligned(new Decoupled(new ResultPacket))
  val storeAllowed = Flipped(Bool())
  val memory = Aligned(new MemoryPort)

@generator
object DitDahA1Lsu extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1LsuIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Lsu"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1LsuIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val state = RegInit(0.U(2))
    val packet = Reg(new ResultPacket)
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
      pmp.io.address := io.input.bits.address
      pmp.io.size := io.input.bits.memorySize
      pmp.io.write := io.input.bits.store
      pmp.io.fetch := false.B
      pmp.io.atomic := io.input.bits.load & io.input.bits.store
      pmp.io.allowed
    io.input.ready := (state === 0.U(2)) & (io.input.bits.instruction.fault | !io.input.bits.store | io.storeAllowed)
    io.output.valid := state === 3.U(2)
    io.output.bits :<= packet
    request.valid := state === 1.U(2)
    request.bits.address := packet.address
    request.bits.data := packet.storeData
    request.bits.size := packet.memorySize
    request.bits.mask := 0.U(8)
    for size <- 0 to 3 do
      when(packet.store & (packet.memorySize === size.U(3))) { request.bits.mask := ((1 << (1 << size)) - 1).U(8) }
    request.bits.tag := packet.instruction.tag
    request.bits.write := packet.store
    request.bits.fetch := false.B
    request.bits.atomic := packet.atomic
    request.bits.atomicOperation := packet.atomic.?(operation, 0.U(5))
    request.bits.scEligible := scEligible
    response.ready := state === 2.U(2)
    when(io.input.valid & io.input.ready) {
      packet :<= io.input.bits
      scEligible := io.input.bits.atomic & (inputOperation === 3.U(5)) & reserved &
        (io.input.bits.address === reservedAddress) & (io.input.bits.memorySize === 3.U(3))
      when(io.input.bits.atomic) { reserved := false.B }
      state := 1.U(2)
      if parameter.pmpEntries != 0 then
        when(!io.input.bits.instruction.fault & !permitted) {
          packet.instruction.fault := true.B
          packet.instruction.cause := io.input.bits.store.?(7.U(64), 5.U(64))
          packet.instruction.tval := io.input.bits.address
          state := 3.U(2)
        }
      val alignment = Wire(UInt(64))
      alignment := 7.U(64)
      for size <- 0 to 2 do
        when(io.input.bits.memorySize === size.U(3)) { alignment := ((1 << size) - 1).U(64) }
      when(!io.input.bits.instruction.fault & ((io.input.bits.address.asBits & alignment.asBits).asUInt =/= 0.U(64))) {
        packet.instruction.fault := true.B
        packet.instruction.cause := io.input.bits.store.?(6.U(64), 4.U(64))
        packet.instruction.tval := io.input.bits.address
        state := 3.U(2)
      }
      when(io.input.bits.instruction.fault) { state := 3.U(2) }
    }
    when(request.valid & request.ready) { state := 2.U(2) }
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
        reservedWord := packet.address.asBits.bits(parameter.physicalAddressBits - 1, 3).asUInt
      }
      state := 3.U(2)
    }
    when(io.output.valid & io.output.ready) { state := 0.U(2) }
