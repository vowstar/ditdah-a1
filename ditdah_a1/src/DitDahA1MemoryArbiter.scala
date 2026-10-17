// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1MemoryArbiterIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val ports = Flipped(Vec(2 * parameter.hartCount, new MemoryPort))
  val downstream = Aligned(new MemoryPort)

@generator
object DitDahA1MemoryArbiter extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1MemoryArbiterIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1MemoryArbiter"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1MemoryArbiterIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val state = RegInit(0.U(2))
    val count = 2 * parameter.hartCount
    val bits = 32 - Integer.numberOfLeadingZeros(count - 1)
    val owner = Reg(UInt(bits))
    val next = RegInit(0.U(bits))
    val request = Reg(new MemoryRequest)
    val down = io.downstream
    val idle = state === 0.U(2)
    val valid = (0 until count).map(i => io.ports(i).request.valid)
    val following = (0 until count).map(i => valid(i) & (next <= i.U(bits)))
    val choices = Seq(valid, following).map { candidates =>
      candidates.zipWithIndex.reverse.foldLeft[Referable[UInt]](0.U(bits)) {
        case (selected, (present, index)) => present.?(index.U(bits), selected)
      }
    }
    val selected = following.reduce(_ | _).?(choices(1), choices(0))
    down.request.valid := state === 1.U(2)
    down.request.bits :<= request
    for i <- 0 until count do
      val port = io.ports(i)
      port.request.ready := idle & (selected === i.U(bits))
      port.response.valid := (state === 2.U(2)) & (owner === i.U(bits)) & down.response.valid
      port.response.bits :<= down.response.bits
      when(port.request.valid & port.request.ready) {
        request :<= port.request.bits
        owner := i.U(bits)
        state := 1.U(2)
      }
    down.response.ready := (state === 2.U(2)) & (0 until count).map { i =>
      (owner === i.U(bits)) & io.ports(i).response.ready
    }.reduce(_ | _)
    when(down.request.valid & down.request.ready) { state := 2.U(2) }
    when(down.response.valid & down.response.ready) {
      next := (owner === (count - 1).U(bits)).?(0.U(bits), (owner + 1.U(bits)).asBits.bits(bits - 1, 0).asUInt)
      state := 0.U(2)
    }
