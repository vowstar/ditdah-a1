// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

class DitDahA1MemoryIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val upstream = Flipped(new MemoryPort)
  val downstream = Aligned(new MemoryPort)

@generator
object DitDahA1Memory extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1MemoryIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Memory"
  def executable(parameter: DitDahA1Parameter, address: Referable[UInt], bytes: Int)(using Arena, Context, Block, InstanceContext): Referable[Bool] =
    parameter.memoryRegions.filter(r => r.executable && !r.device && r.size >= bytes).foldLeft[Referable[Bool]](false.B) { (allowed, region) =>
      allowed | ((address >= region.base.U(64)) & (address <= (region.base + region.size - bytes).U(64)))
    }
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1MemoryIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val pending = RegInit(false.B)
    val localFault = RegInit(false.B)
    val tag = Reg(UInt(8))
    val up = io.upstream
    val down = io.downstream
    val request = up.request.bits
    val allowed = Wire(Bool())
    allowed := false.B
    val atomicShape = request.write & !request.fetch & (request.size === 3.U(3)) & (request.mask === 255.U(8))
    for size <- 0 to 3 do
      val bytes = 1 << size
      val aligned = if size == 0 then true.B else request.address.asBits.bits(size - 1, 0).asUInt === 0.U(size)
      val validMask = (request.mask =/= 0.U(8)) & ((request.mask.asBits & (255 ^ ((1 << bytes) - 1)).B(8)).asUInt === 0.U(8))
      when((request.size === size.U(3)) & aligned & (!request.write | validMask) & (!request.atomic | atomicShape)) {
        when(request.fetch & !request.write & !request.atomic) {
          allowed := executable(parameter, request.address, bytes)
        }
        for region <- parameter.memoryRegions do
          val inRegion = (request.address >= region.base.U(64)) & (request.address <= (region.base + region.size - bytes).U(64))
          when(inRegion & !request.fetch) {
            when(request.atomic) {
              if region.atomic && region.readable && region.writable && !region.device then allowed := true.B
            }.otherwise {
              when(request.write) {
                if region.writable then allowed := true.B
              }.otherwise {
                if region.readable then allowed := true.B
              }
            }
          }
      }
    up.request.ready := !pending & (!allowed | down.request.ready)
    down.request.valid := up.request.valid & !pending & allowed
    down.request.bits :<= request
    up.response.valid := pending & (localFault | down.response.valid)
    up.response.bits.data := localFault.?(0.U(64), down.response.bits.data)
    up.response.bits.fault := localFault | down.response.bits.fault
    up.response.bits.tag := localFault.?(tag, down.response.bits.tag)
    down.response.ready := pending & !localFault & up.response.ready
    when(up.request.valid & up.request.ready) { pending := true.B; localFault := !allowed; tag := request.tag }
    when(up.response.valid & up.response.ready) { pending := false.B }
