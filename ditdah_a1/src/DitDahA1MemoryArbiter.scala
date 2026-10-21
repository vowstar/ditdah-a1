// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

class DitDahA1MemoryArbiterIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val ports = Flipped(Vec(2 * parameter.hartCount, new MemoryPort))
  val downstream = Aligned(new MemoryPort)
  val hartId = Aligned(UInt(4))

@generator
object DitDahA1MemoryArbiter extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1MemoryArbiterIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1MemoryArbiter"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1MemoryArbiterIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val owner = arbitrate((0 until 2 * parameter.hartCount).map(io.ports(_)), io.downstream)
    io.hartId := (if parameter.hartCount == 1 then 0.U(4) else owner.asBits.bits(32 - Integer.numberOfLeadingZeros(2 * parameter.hartCount - 1) - 1, 1).asUInt)

  def arbitrate(ports: Seq[Referable[MemoryPort]], down: Referable[MemoryPort])
    (using Arena, Context, Block, InstanceContext, ClockScope, ResetScope): Referable[UInt] =
    val state = RegInit(0.U(2))
    val count = ports.size
    val bits = 32 - Integer.numberOfLeadingZeros(count - 1)
    val owner = Reg(UInt(bits))
    val next = RegInit(0.U(bits))
    val request = Reg(new MemoryRequest)
    val idle = state === 0.U(2)
    val valid = (0 until count).map(i => ports(i).request.valid)
    val selected = select(valid, next)
    down.request.valid := state === 1.U(2)
    down.request.bits :<= request
    for i <- 0 until count do
      val port = ports(i)
      port.request.ready := idle & (selected === i.U(bits))
      port.response.valid := (state === 2.U(2)) & (owner === i.U(bits)) & down.response.valid
      port.response.bits :<= down.response.bits
      when(port.request.valid & port.request.ready) {
        request :<= port.request.bits
        owner := i.U(bits)
        state := 1.U(2)
      }
    down.response.ready := (state === 2.U(2)) & (0 until count).map { i =>
      (owner === i.U(bits)) & ports(i).response.ready
    }.reduce(_ | _)
    when(down.request.valid & down.request.ready) { state := 2.U(2) }
    when(down.response.valid & down.response.ready & down.response.bits.last) {
      next := (owner === (count - 1).U(bits)).?(0.U(bits), (owner + 1.U(bits)).asBits.bits(bits - 1, 0).asUInt)
      state := 0.U(2)
    }
    owner

  def select(valid: Seq[Referable[Bool]], next: Referable[UInt])
    (using Arena, Context, Block, InstanceContext): Referable[UInt] =
    val bits = 32 - Integer.numberOfLeadingZeros(valid.size - 1)
    val following = valid.indices.map(i => valid(i) & (next <= i.U(bits)))
    val choices = Seq(valid, following).map { candidates =>
      candidates.zipWithIndex.reverse.foldLeft[Referable[UInt]](0.U(bits)) {
        case (selected, (present, index)) => present.?(index.U(bits), selected)
      }
    }
    following.reduce(_ | _).?(choices(1), choices(0))
