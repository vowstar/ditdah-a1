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
  val sampleSize = ProbeRead(UInt(3), dv)
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
    val storeHit = Reg(Bool())
    val expanded = RegInit(false.B)
    val line = Option.when(parameter.enableDataBurstRefill)(RegInit(false.B))
    val beat = Option.when(parameter.enableDataBurstRefill)(RegInit(0.U(3)))
    val lineActive = line.getOrElse(false.B)
    val lastWord = beat.map(_ === 7.U(3)).getOrElse(false.B)
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
    val refill = Wire(new MemoryRequest)
    refill :<= request
    refill.address := (request.address.asBits.bits(63, 3) ## 0.B(3)).asUInt
    refill.size := 3.U(3)
    refill.refillSize := 3.U(3)
    if parameter.enableDataBurstRefill then
      when(lineActive) {
        refill.address := (request.address.asBits.bits(63, 6) ## 0.B(6)).asUInt
        refill.size := 6.U(3)
        refill.refillSize := 6.U(3)
      }
    val cacheable = !request.fetch & !request.atomic & (request.size <= 3.U(3)) &
      DitDahA1Memory.permitted(parameter, request) &
        DitDahA1Memory.dataCacheable(parameter, (request.address.asBits.bits(63, 3) ## 0.B(3)).asUInt, 8)
    val eligible = !request.write & cacheable
    val widening = eligible & (request.size < 3.U(3)) &
      ((request.refillSize === 3.U(3)) | (request.refillSize === 6.U(3))) & DitDahA1Memory.permitted(parameter, refill)
    val lineCandidate = if parameter.enableDataBurstRefill then eligible & (request.refillSize === 6.U(3)) &
      DitDahA1Memory.dataCacheable(parameter, (request.address.asBits.bits(63, 6) ## 0.B(6)).asUInt, 64) else false.B
    val responseFault = down.response.bits.fault | (down.response.bits.tag =/= request.tag)
    val lineFault = responseFault | (down.response.bits.last =/= lastWord)
    val wordFilling = (state === 3.U(3)) & down.response.valid & !responseFault & !lineActive & !fault & eligible &
      ((request.size === 3.U(3)) | expanded) & !invalidated & !collision
    val lineFilling = (state === 3.U(3)) & down.response.valid & lineActive & !lineFault & !fault & !invalidated & !collision
    val publish = lineFilling & lastWord & down.response.bits.last
    val storeComplete = (state === 3.U(3)) & down.response.valid & request.write
    val storeUpdating = storeComplete & storeHit & !responseFault & !invalidated & !collision
    val storeFailed = storeComplete & responseFault
    val filling = wordFilling | lineFilling | storeUpdating
    val reading = up.request.valid & up.request.ready
    val tag = request.address.asBits.bits(parameter.physicalAddressBits - 1, indexBits + 6).asUInt
    val writeWord = beat.map(b => lineActive.?((index.asBits ## b.asBits).asUInt, word)).getOrElse(word)
    val shift = (request.address.asBits.bits(2, 0) ## 0.B(3)).asUInt
    val byteMask = (0 until 8).reverse.map(byte => request.mask.asBits.bit(byte).?(255.B(8), 0.B(8))).reduce(_ ## _)
    val storeMask = (byteMask.asUInt << shift).asBits.bits(63, 0)
    val storeData = ((data.asBits & ~storeMask) | ((request.data << shift).asBits.bits(63, 0) & storeMask)).asUInt
    val wordRead = StorageArray("data", words, 64,
      up.request.bits.address.asBits.bits(indexBits + 5, 3).asUInt, writeWord,
      storeUpdating.?(storeData, down.response.bits.data), filling, reading, io.clock)
    val tagRead = StorageArray("dataTags", words / 8, tagBits,
      up.request.bits.address.asBits.bits(indexBits + 5, 6).asUInt, index,
      tag, wordFilling | publish, reading, io.clock)
    val hit = (valid.asUInt >> word).asBits.bit(0) & (tagRead === tag) & !collision & !invalidated
    val readMask = Wire(UInt(64))
    readMask := ((BigInt(1) << 64) - 1).U(64)
    for size <- 0 to 2 do
      when(request.size === size.U(3)) { readMask := ((BigInt(1) << (8 << size)) - 1).U(64) }
    val hitData = ((wordRead >> shift).asBits & readMask.asBits).asUInt
    val refillData = ((down.response.bits.data >> shift).asBits & readMask.asBits).asUInt
    val hitResponse = (state === 1.U(3)) & eligible & hit
    val startLine = (state === 1.U(3)) & !hitResponse & lineCandidate
    io.invalidate.ready := true.B
    up.request.ready := (state === 0.U(3)) | (up.response.valid & up.response.ready)
    up.response.valid := (state === 4.U(3)) | hitResponse
    up.response.bits.data := hitResponse.?(hitData, data)
    up.response.bits.fault := !hitResponse & fault
    up.response.bits.tag := request.tag
    up.response.bits.last := true.B
    down.request.valid := state === 2.U(3)
    down.request.bits :<= request
    when(expanded | lineActive) { down.request.bits :<= refill }
    when(fault) { down.request.bits.refillSize := 0.U(3) }
    down.response.ready := (state === 3.U(3)) | (if parameter.enableDataBurstRefill then state === 5.U(3) else false.B)
    when(state === 1.U(3)) {
      sameTag := tagRead === tag
      storeHit := request.write & cacheable & hit
      when(request.write) { data := wordRead }
      when(eligible & hit) { data := hitData; fault := false.B; state := 4.U(3) }
        .otherwise { expanded := widening & !lineCandidate; line.foreach(_ := lineCandidate); state := 2.U(3) }
    }
    when(down.request.valid & down.request.ready) { state := 3.U(3) }
    when(down.response.valid & down.response.ready) {
      when(lineActive) {
        if parameter.enableDataBurstRefill then
          fault := fault | lineFault | invalidated | collision
          when((state === 3.U(3)) & (beat.get === request.address.asBits.bits(5, 3).asUInt)) { data := refillData }
          when(down.response.bits.last) {
            line.get := false.B
            when((state === 5.U(3)) | lineFault | fault | invalidated | collision) { fault := true.B; state := 2.U(3) }
              .otherwise { state := 4.U(3) }
          }.otherwise {
            when(state === 3.U(3)) {
              when(lastWord) { state := 5.U(3) }
                .otherwise { beat.get := (beat.get + 1.U(3)).asBits.bits(2, 0).asUInt }
            }
          }
      }.otherwise {
        when(expanded & responseFault) { expanded := false.B; fault := true.B; state := 2.U(3) }
          .otherwise {
            data := expanded.?(refillData, down.response.bits.data)
            fault := responseFault
            state := 4.U(3)
          }
      }
    }
    val allocated = sameTag.?(valid, valid & ~lineMask) | mask
    val nextValid = (startLine | storeFailed).?(valid & ~lineMask, publish.?(valid | lineMask, wordFilling.?(allocated, valid)))
    when(startLine | storeFailed | publish | wordFilling | io.invalidate.valid) { valid := io.invalidate.valid.?(nextValid & ~invalidateMask, nextValid) }
    when(up.response.valid & up.response.ready) { state := 0.U(3) }
    when(io.invalidate.valid) {
      // Invalidation may conservatively evict a different tag at this index.
      when((state =/= 0.U(3)) & (invalidateIndex === index)) { invalidated := true.B }
    }
    when(reading) {
      request :<= up.request.bits
      invalidated := io.invalidate.valid &
        (invalidateIndex === up.request.bits.address.asBits.bits(indexBits + 5, 6).asUInt)
      expanded := false.B
      line.foreach(_ := false.B)
      beat.foreach(_ := 0.U(3))
      fault := false.B
      state := 1.U(3)
    }
    layer("DV"):
      val sampleValid = Wire(Bool())
      val sampleAddress = Wire(UInt(64))
      val sampleData = Wire(UInt(64))
      val sampleSize = Wire(UInt(3))
      val sampleTag = Wire(UInt(8))
      sampleValid := hitResponse
      sampleAddress := request.address
      sampleData := hitData
      sampleSize := request.size
      sampleTag := request.tag
      probe.sampleValid <== sampleValid
      probe.sampleAddress <== sampleAddress
      probe.sampleData <== sampleData
      probe.sampleSize <== sampleSize
      probe.sampleTag <== sampleTag
