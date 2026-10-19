// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1DataCacheIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val upstream = Flipped(new MemoryPort)
  val downstream = Aligned(new MemoryPort)
  val invalidate = Flipped(new Decoupled(UInt(64)))

class DitDahA1DataCacheProbe(parameter: DitDahA1Parameter) extends DVBundle[DitDahA1Parameter, DitDahA1Layers](parameter):
  private def dv = layers("DV")
  val sampleValid = ProbeRead(Bool(), dv)
  val sampleAddress = ProbeRead(UInt(64), dv)
  val sampleData = ProbeRead(UInt(64), dv)
  val sampleTag = ProbeRead(UInt(8), dv)

@generator
object DitDahA1DataCache extends Generator[DitDahA1Parameter, DitDahA1Layers, DitDahA1DataCacheIO, DitDahA1DataCacheProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1DataCache"
  def architecture(parameter: DitDahA1Parameter) =
    require(parameter.dCacheBytes == 8192, "Data cache requires 8192 bytes")
    val io = summon[Interface[DitDahA1DataCacheIO]]
    val probe = summon[ProbeInterface[DitDahA1DataCacheProbe]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val indexBits = Integer.numberOfTrailingZeros(parameter.dCacheBytes) - 6
    val words = parameter.dCacheBytes / 8
    val tagBits = parameter.physicalAddressBits - indexBits - 6
    val state = RegInit(0.U(3))
    val request = Reg(new MemoryRequest)
    val data = Reg(UInt(64))
    val fault = Reg(Bool())
    val valid = RegInit(0.B(words))
    val invalidated = RegInit(false.B)
    val sameTag = Reg(Bool())
    val up = io.upstream
    val down = io.downstream
    val index = request.address.asBits.bits(indexBits + 5, 6).asUInt
    val word = request.address.asBits.bits(indexBits + 5, 3).asUInt
    val mask = (1.U(words) << word).asBits.bits(words - 1, 0)
    val lineShift = (index.asBits ## 0.B(3)).asUInt
    val lineMask = (255.U(words) << lineShift).asBits.bits(words - 1, 0)
    val invalidateIndex = io.invalidate.bits.asBits.bits(indexBits + 5, 6).asUInt
    val invalidateShift = (invalidateIndex.asBits ## 0.B(3)).asUInt
    val invalidateMask = (255.U(words) << invalidateShift).asBits.bits(words - 1, 0)
    val collision = io.invalidate.valid & (invalidateIndex === index)
    val eligible = !request.write & !request.fetch & !request.atomic & (request.size === 3.U(3)) &
      DitDahA1Memory.permitted(parameter, request) & DitDahA1Memory.dataCacheable(parameter, request.address, 8)
    val responseFault = down.response.bits.fault | (down.response.bits.tag =/= request.tag)
    val filling = (state === 3.U(3)) & down.response.valid & !responseFault & eligible & !invalidated & !collision
    val reading = up.request.valid & up.request.ready
    val tag = request.address.asBits.bits(parameter.physicalAddressBits - 1, indexBits + 6).asUInt
    val wordRead = StorageArray("data", words, 64,
      up.request.bits.address.asBits.bits(indexBits + 5, 3).asUInt, word,
      down.response.bits.data, filling, reading, io.clock)
    val tagRead = StorageArray("dataTags", words / 8, tagBits,
      up.request.bits.address.asBits.bits(indexBits + 5, 6).asUInt, index,
      tag, filling, reading, io.clock)
    val hit = (valid.asUInt >> word).asBits.bit(0) & (tagRead === tag) & !collision & !invalidated
    io.invalidate.ready := true.B
    up.request.ready := state === 0.U(3)
    up.response.valid := state === 4.U(3)
    up.response.bits.data := data
    up.response.bits.fault := fault
    up.response.bits.tag := request.tag
    down.request.valid := state === 2.U(3)
    down.request.bits :<= request
    down.response.ready := state === 3.U(3)
    when(reading) {
      request :<= up.request.bits
      invalidated := io.invalidate.valid &
        (invalidateIndex === up.request.bits.address.asBits.bits(indexBits + 5, 6).asUInt)
      state := 1.U(3)
    }
    when(state === 1.U(3)) {
      sameTag := tagRead === tag
      when(eligible & hit) { data := wordRead; fault := false.B; state := 4.U(3) }
        .otherwise { state := 2.U(3) }
    }
    when(down.request.valid & down.request.ready) { state := 3.U(3) }
    when(down.response.valid & down.response.ready) {
      data := down.response.bits.data
      fault := responseFault
      state := 4.U(3)
    }
    val allocated = sameTag.?(valid, valid & ~lineMask) | mask
    val nextValid = filling.?(allocated, valid)
    when(filling | io.invalidate.valid) { valid := io.invalidate.valid.?(nextValid & ~invalidateMask, nextValid) }
    when(up.response.valid & up.response.ready) { state := 0.U(3) }
    when(io.invalidate.valid) {
      // Invalidation may conservatively evict a different tag at this index.
      when((state =/= 0.U(3)) & (invalidateIndex === index)) { invalidated := true.B }
    }
    layer("DV"):
      val sampleValid = Wire(Bool())
      val sampleAddress = Wire(UInt(64))
      val sampleData = Wire(UInt(64))
      val sampleTag = Wire(UInt(8))
      sampleValid := (state === 1.U(3)) & eligible & hit
      sampleAddress := request.address
      sampleData := wordRead
      sampleTag := request.tag
      probe.sampleValid <== sampleValid
      probe.sampleAddress <== sampleAddress
      probe.sampleData <== sampleData
      probe.sampleTag <== sampleTag
