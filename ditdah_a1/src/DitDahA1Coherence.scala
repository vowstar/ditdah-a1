// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1CoherenceIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val hartId = Flipped(UInt(4))
  val upstream = Flipped(new MemoryPort)
  val downstream = Aligned(new MemoryPort)
  val invalidate = Aligned(Vec(parameter.hartCount, new Decoupled(UInt(64))))

@generator
object DitDahA1Coherence extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1CoherenceIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Coherence"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1CoherenceIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val busy = RegInit(false.B)
    val pending = RegInit(0.B(parameter.hartCount))
    val up = io.upstream
    val down = io.downstream
    val needsInvalidate = up.request.bits.write & DitDahA1Memory.dataCacheable(parameter, up.request.bits.address, 1)
    val targets = (0 until parameter.hartCount).reverse.map(hart =>
      (up.request.bits.atomic | (io.hartId =/= hart.U(4))).asBits).reduce(_ ## _)
    val permitted = !needsInvalidate | (busy & (pending === 0.B(parameter.hartCount)))
    up.request.ready := down.request.ready & permitted
    down.request.valid := up.request.valid & permitted
    down.request.bits :<= up.request.bits
    up.response :<>= down.response
    for hart <- 0 until parameter.hartCount do
      io.invalidate(hart).valid := busy & pending.bit(hart)
      io.invalidate(hart).bits := up.request.bits.address
    val acknowledged = (0 until parameter.hartCount).reverse.map(hart =>
      (io.invalidate(hart).valid & io.invalidate(hart).ready).asBits).reduce(_ ## _)
    when(busy) { pending := pending & ~acknowledged }
    when(!busy & up.request.valid & needsInvalidate) {
      busy := true.B
      pending := targets
    }
    when(up.request.valid & up.request.ready) { busy := false.B }
