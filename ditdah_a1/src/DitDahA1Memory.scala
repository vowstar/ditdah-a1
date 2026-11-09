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
  val upstream = Flipped(new MemoryPort(parameter))
  val downstream = Aligned(new MemoryPort(parameter))

@generator
object DitDahA1Memory extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1MemoryIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Memory"
  def debugWindow(parameter: DitDahA1Parameter, address: Referable[UInt], size: Referable[UInt])
    (using Arena, Context, Block, InstanceContext): Referable[Bool] =
    if !parameter.enableDebugMemory then false.B else
      val base = parameter.debugBase.get
      (0 to 6).map(n => (size === n.U(3)) & (address >= base.U(64)) &
        (address <= (base + 4096 - (1 << n)).U(64))).reduce(_ | _)
  def executable(parameter: DitDahA1Parameter, address: Referable[UInt], bytes: Int)(using Arena, Context, Block, InstanceContext): Referable[Bool] =
    parameter.memoryRegions.filter(r => r.executable && !r.device && r.size >= bytes).foldLeft[Referable[Bool]](false.B) { (allowed, region) =>
      allowed | ((address >= region.base.U(64)) & (address <= (region.base + region.size - bytes).U(64)))
    }
  def dataCacheable(parameter: DitDahA1Parameter, address: Referable[UInt], bytes: Int)(using Arena, Context, Block, InstanceContext): Referable[Bool] =
    parameter.memoryRegions.filter(r => r.readable && r.dataCacheable && !r.device && r.size >= bytes).foldLeft[Referable[Bool]](false.B) { (selected, region) =>
      selected | ((address >= region.base.U(64)) & (address <= (region.base + region.size - bytes).U(64)))
    }
  def managementPermitted(parameter: DitDahA1Parameter, request: Referable[MemoryRequest])(using Arena, Context, Block, InstanceContext): Referable[Bool] =
    val region = parameter.blockMemoryRegions.filter(r => (r.readable || r.writable) && (!r.writable || r.readable) && r.size >= 64)
      .foldLeft[Referable[Bool]](false.B) { (allowed, r) =>
        allowed | ((request.address >= r.base.U(64)) & (request.address <= (r.base + r.size - 64).U(64)))
      }
    parameter.enableZicbom.B & region & !request.write & !request.fetch & !request.atomic &
      (request.size === 3.U(3)) & (request.mask === 0.U(8)) & (request.address.asBits.bits(5, 0) === 0.B(6))

  def permitted(parameter: DitDahA1Parameter, request: Referable[MemoryRequest])(using Arena, Context, Block, InstanceContext): Referable[Bool] =
    val allowed = Wire(Bool())
    allowed := false.B
    val operation = request.atomicOperation
    val lr = operation === 2.U(5)
    val writeAtomic = (DitDahA1Isa.atomicOperations :+ 3).map(op => operation === op.U(5)).reduce(_ | _)
    val atomicMask = (request.size === 2.U(3)).?(15.U(8), 255.U(8))
    val atomicShape = parameter.enableA.B & !request.fetch & ((request.size === 2.U(3)) | (request.size === 3.U(3))) &
      ((lr & !request.write) | (writeAtomic & request.write & (request.mask === atomicMask)))
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
    if parameter.enableBurstRefill then
      when(request.fetch & !request.write & !request.atomic & (request.size === 6.U(3)) &
        (request.address.asBits.bits(5, 0) === 0.B(6))) { allowed := executable(parameter, request.address, 64) }
    if parameter.enableDataBurstRefill then
      when(!request.fetch & !request.write & !request.atomic & (request.size === 6.U(3)) &
        (request.address.asBits.bits(5, 0) === 0.B(6))) { allowed := dataCacheable(parameter, request.address, 64) }
    when(request.cacheOperation === 3.U(2)) { allowed := managementPermitted(parameter, request) }
    allowed
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
    val allowed = permitted(parameter, request)
    up.request.ready := !pending & (!allowed | down.request.ready)
    down.request.valid := up.request.valid & !pending & allowed
    down.request.bits :<= request
    up.response.valid := pending & (localFault | down.response.valid)
    up.response.bits.data := localFault.?(0.U(64), down.response.bits.data)
    up.response.bits.fault := localFault | down.response.bits.fault
    up.response.bits.tag := localFault.?(tag, down.response.bits.tag)
    up.response.bits.last := localFault | down.response.bits.last
    down.response.ready := pending & !localFault & up.response.ready
    when(up.request.valid & up.request.ready) { pending := true.B; localFault := !allowed; tag := request.tag }
    when(up.response.valid & up.response.ready & up.response.bits.last) { pending := false.B }
