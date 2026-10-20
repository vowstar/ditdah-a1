// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1LocalInterruptsIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val timeTick = Flipped(Bool())
  val memory = Flipped(new MemoryPort)
  val interrupts = Aligned(Vec(parameter.hartCount, new InterruptBundle))

@generator
object DitDahA1LocalInterrupts extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1LocalInterruptsIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1LocalInterrupts"
  def architecture(parameter: DitDahA1Parameter) =
    parameter.validateFabric()
    require(parameter.localInterruptBase.nonEmpty, "Local interrupt base is required")
    val io = summon[Interface[DitDahA1LocalInterruptsIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val base = parameter.localInterruptBase.get
    val pending = RegInit(false.B)
    val response = Reg(new MemoryResponse)
    val time = RegInit(0.U(64))
    val software = Seq.fill(parameter.hartCount)(RegInit(false.B))
    val compare = Seq.fill(parameter.hartCount)(RegInit(((BigInt(1) << 64) - 1).U(64)))
    val memory = io.memory
    val request = memory.request.bits
    val accepted = memory.request.valid & memory.request.ready
    val permitted = !request.fetch & !request.atomic
    val write = accepted & permitted & request.write
    val word = (request.size === 2.U(3)) & (!request.write | (request.mask === 15.U(8)))
    val doubleword = (request.size === 3.U(3)) & (!request.write | (request.mask === 255.U(8)))
    val valid = Wire(Bool())
    val data = Wire(UInt(64))
    valid := false.B
    data := 0.U(64)
    memory.request.ready := !pending
    memory.response.valid := pending
    memory.response.bits :<= response
    when(io.timeTick) { time := (time + 1.U(64)).asBits.bits(63, 0).asUInt }
    for hart <- 0 until parameter.hartCount do
      val softwareAccess = (request.address === (base + 4 * hart).U(64)) & word
      val compareAccess = (request.address === (base + 0x4000 + 8 * hart).U(64)) & doubleword
      io.interrupts(hart).software := software(hart)
      io.interrupts(hart).timer := time >= compare(hart)
      io.interrupts(hart).external := false.B
      when(softwareAccess) { valid := permitted; data := software(hart).?(1.U(64), 0.U(64)) }
      when(compareAccess) { valid := permitted; data := compare(hart) }
      when(write & softwareAccess) { software(hart) := request.data.asBits.bit(0) }
      when(write & compareAccess) { compare(hart) := request.data }
    val timeAccess = (request.address === (base + 0xbff8).U(64)) & doubleword
    when(timeAccess) { valid := permitted; data := time }
    when(write & timeAccess) { time := request.data }
    when(memory.response.valid & memory.response.ready) { pending := false.B }
    when(accepted) {
      pending := true.B
      response.data := (valid & !request.write).?(data, 0.U(64))
      response.fault := !valid
      response.tag := request.tag
      response.last := true.B
    }
