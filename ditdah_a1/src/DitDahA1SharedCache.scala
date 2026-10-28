// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1SharedCacheIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val upstream = Flipped(new AxiBundle(parameter))
  val downstream = Aligned(new AxiBundle(parameter))

@generator
object DitDahA1SharedCache extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1SharedCacheIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1SharedCache"
  def architecture(parameter: DitDahA1Parameter) =
    parameter.validateSharedCache()
    require(parameter.l2CacheBytes != 0, "Shared cache requires nonzero capacity")
    val io = summon[Interface[DitDahA1SharedCacheIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val up = io.upstream
    val down = io.downstream
    val capacityBits = Integer.numberOfTrailingZeros(parameter.l2CacheBytes)
    val beatBits = Integer.numberOfTrailingZeros(parameter.axiDataBits / 8)
    val rowBits = capacityBits - beatBits
    val rows = parameter.l2CacheBytes / (parameter.axiDataBits / 8)
    val sectors = 64 / (parameter.axiDataBits / 8)
    val state = RegInit(0.U(3))
    val address = Reg(new AxiAddress(parameter))
    val beat = RegInit(0.U(8))
    val failed = RegInit(false.B)
    val valid = RegInit(0.B(rows))
    val writing = RegInit(false.B)
    val awDone = RegInit(false.B)
    val wDone = RegInit(false.B)
    val idle = state === 0.U(3)
    val readAccepted = up.ar.valid & up.ar.ready
    val writeAccepted = up.aw.valid & up.aw.ready
    val dataAccepted = up.w.valid & up.w.ready
    val set = address.addr.asBits.bits(capacityBits - 1, 6).asUInt
    val row = address.addr.asBits.bits(capacityBits - 1, beatBits).asUInt
    val tag = address.addr.asBits.bits(parameter.physicalAddressBits - 1, capacityBits).asUInt
    val shift = if beatBits == 6 then set else (set.asBits ## 0.B(6 - beatBits)).asUInt
    val lineMask = (((1 << sectors) - 1).U(rows) << shift).asBits.bits(rows - 1, 0)
    val rowMask = (1.U(rows) << row).asBits.bits(rows - 1, 0)
    val requested = (address.len === 0.U(8)).?(rowMask, lineMask)
    val aligned = Wire(Bool())
    val permitted = Wire(Bool())
    aligned := false.B
    permitted := false.B
    for size <- 0 to beatBits do
      when(address.size === size.U(3)) {
        aligned := (if size == 0 then true.B else address.addr.asBits.bits(size - 1, 0) === 0.B(size))
        for region <- parameter.memoryRegions.filter(r => !r.device && r.size >= (1 << size)) do
          val permission = address.prot.asBits.bit(2).?(region.executable.B, (region.readable && region.dataCacheable).B)
          val end = (address.len === 0.U(8)).?((region.base + region.size - (1 << size)).U(64),
            (region.base + region.size - region.size.min(BigInt(64))).U(64))
          val span = (address.len === 0.U(8)) | (region.size >= 64).B
          when(permission & span & (address.addr >= region.base.U(64)) & (address.addr <= end)) { permitted := true.B }
      }
    val scalar = (address.len === 0.U(8)) & (address.size <= beatBits.U(3)) & aligned
    val line = (address.len === (sectors - 1).U(8)) & (address.size === beatBits.U(3)) &
      (address.addr.asBits.bits(5, 0) === 0.B(6))
    val cacheable = !address.lock & address.cache.asBits.bit(1) &
      (address.cache.asBits.bit(2) | address.cache.asBits.bit(3)) &
      (address.burst === 1.U(2)) & (scalar | line) & permitted
    val allocate = cacheable & address.cache.asBits.bit(2) & (address.size === beatBits.U(3))
    val responseAccepted = (state === 3.U(3)) & down.r.valid & up.r.ready
    val responseFault = (down.r.bits.id =/= address.id) | (down.r.bits.resp =/= 0.U(2)) |
      (down.r.bits.last =/= (beat === address.len))
    val publish = responseAccepted & down.r.bits.last & !failed & !responseFault & allocate
    val readNext = (state === 4.U(3)) & up.r.ready & (beat =/= address.len)
    val currentRow = (row + beat).asBits.bits(rowBits - 1, 0).asUInt
    val readRow = readAccepted.?(up.ar.bits.addr.asBits.bits(capacityBits - 1, beatBits).asUInt,
      readNext.?((currentRow + 1.U(1)).asBits.bits(rowBits - 1, 0).asUInt, currentRow))
    val data = StorageArray("sharedData", rows, parameter.axiDataBits, readRow,
      currentRow, down.r.bits.data, responseAccepted & allocate & !failed & !responseFault,
      readAccepted | (state === 1.U(3)) | (state === 4.U(3)), io.clock)
    val storedTag = StorageArray("sharedTags", parameter.l2CacheBytes / 64, parameter.physicalAddressBits - capacityBits,
      up.ar.bits.addr.asBits.bits(capacityBits - 1, 6).asUInt, set, tag, publish, readAccepted, io.clock)
    val hit = cacheable & (storedTag === tag) & ((valid & requested) === requested)
    up.ar.ready := idle & !writing & !up.aw.valid & !up.w.valid
    down.ar.valid := state === 2.U(3)
    down.ar.bits :<= address
    up.r.valid := (state === 4.U(3)) | ((state === 3.U(3)) & down.r.valid)
    up.r.bits :<= down.r.bits
    when(state === 4.U(3)) {
      up.r.bits.data := data
      up.r.bits.id := address.id
      up.r.bits.resp := 0.U(2)
      up.r.bits.last := beat === address.len
    }
    down.r.ready := (state === 3.U(3)) & up.r.ready
    down.aw.valid := up.aw.valid & idle & !awDone
    down.aw.bits :<= up.aw.bits
    up.aw.ready := down.aw.ready & idle & !awDone
    down.w.valid := up.w.valid & idle & !wDone
    down.w.bits :<= up.w.bits
    up.w.ready := down.w.ready & idle & !wDone
    up.b.valid := down.b.valid & awDone & wDone
    up.b.bits :<= down.b.bits
    down.b.ready := up.b.ready & awDone & wDone
    when(readAccepted) { address :<= up.ar.bits; beat := 0.U(8); failed := false.B; state := 1.U(3) }
    when(state === 1.U(3)) {
      state := hit.?(4.U(3), 2.U(3))
      when((!hit & allocate) | address.lock) { valid := valid & ~lineMask }
    }
    when(down.ar.valid & down.ar.ready) { state := 3.U(3) }
    when(responseAccepted) {
      beat := (beat + 1.U(1)).asBits.bits(7, 0).asUInt
      failed := failed | responseFault
      when(publish) { valid := valid | requested }
      when(down.r.bits.last) { state := 0.U(3) }
    }
    when((state === 4.U(3)) & up.r.ready) {
      beat := (beat + 1.U(1)).asBits.bits(7, 0).asUInt
      when(beat === address.len) { state := 0.U(3) }
    }
    when(writeAccepted) {
      writing := true.B; awDone := true.B
      val writeSet = up.aw.bits.addr.asBits.bits(capacityBits - 1, 6).asUInt
      val writeShift = if beatBits == 6 then writeSet else (writeSet.asBits ## 0.B(6 - beatBits)).asUInt
      val mask = (((1 << sectors) - 1).U(rows) << writeShift).asBits.bits(rows - 1, 0)
      valid := (up.aw.bits.len === 0.U(8)).?(valid & ~mask, 0.B(rows))
    }
    when(dataAccepted) { writing := true.B; when(up.w.bits.last) { wDone := true.B } }
    when(up.b.valid & up.b.ready) { writing := false.B; awDone := false.B; wDone := false.B }
