// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

class DitDahA1DataCacheIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val upstream = Flipped(new MemoryPort)
  val downstream = Aligned(new MemoryPort)
  val probe = Flipped(new CacheProbePort)

class DataCacheContext(parameter: DitDahA1Parameter) extends Bundle:
  val request = Aligned(new MemoryRequest)
  val fault = Aligned(Bool())
  val invalidated = Aligned(Bool())
  val sameTag = Aligned(Bool())
  val expanded = Aligned(Bool())
  val data = Option.when(parameter.enableDataBurstRefill)(Aligned(UInt(64)))
  val line = Option.when(parameter.enableDataBurstRefill)(Aligned(Bool()))
  val beat = Option.when(parameter.enableDataBurstRefill)(Aligned(UInt(3)))
  val draining = Option.when(parameter.enableDataBurstRefill)(Aligned(Bool()))
  val releasing = Option.when(parameter.dCacheWriteback)(Aligned(Bool()))
  val victim = Option.when(parameter.dCacheWriteback)(Aligned(UInt(64)))

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
    val acquiring = Option.when(parameter.dCacheWriteback)(Reg(Bool()))
    val releasing = Option.when(parameter.dCacheWriteback)(Reg(Bool()))
    val victim = Option.when(parameter.dCacheWriteback)(Reg(UInt(64)))
    val storedDirty = Option.when(parameter.dCacheWriteback)(Reg(UInt(8)))
    val dirtyLines = Option.when(parameter.dCacheWriteback)(RegInit(0.B(words / 8)))
    val probeState = Option.when(parameter.dCacheWriteback)(RegInit(0.U(3)))
    val probeRequest = Option.when(parameter.dCacheWriteback)(Reg(new CacheProbeRequest))
    val probeWord = Option.when(parameter.dCacheWriteback)(Reg(UInt(3)))
    val probeData = Option.when(parameter.dCacheWriteback)(Reg(UInt(64)))
    val probeMask = Option.when(parameter.dCacheWriteback)(Reg(UInt(8)))
    val probeMatch = Option.when(parameter.dCacheWriteback)(Reg(Bool()))
    val probeActive = probeState.map(_ =/= 0.U(3)).getOrElse(false.B)
    val releaseActive = releasing.getOrElse(false.B)
    val acquireActive = acquiring.getOrElse(false.B)
    val expanded = RegInit(false.B)
    val line = Option.when(parameter.enableDataBurstRefill)(RegInit(false.B))
    val beat = Option.when(parameter.enableDataBurstRefill)(RegInit(0.U(3)))
    val lineActive = line.getOrElse(false.B)
    val lastWord = beat.map(_ === 7.U(3)).getOrElse(false.B)
    val up = io.upstream
    val down = io.downstream
    val concurrent = parameter.loadQueueEntries == 2
    val parked = Option.when(concurrent)(Reg(new DataCacheContext(parameter)))
    val parkedValid = Option.when(concurrent)(RegInit(false.B))
    val offered = Option.when(concurrent)(RegInit(false.B))
    val offerTag = Option.when(concurrent)(Reg(UInt(8)))
    val poisoned = Option.when(concurrent)(RegInit(false.B))
    val waiting = (state === 3.U(3)) | (if parameter.enableDataBurstRefill then state === 5.U(3) else false.B)
    val currentMatch = down.response.bits.tag === request.tag
    val capture = if concurrent then (state === 2.U(3)) & !offered.get & !poisoned.get else
      down.request.valid & down.request.ready
    val index = request.address.asBits.bits(indexBits + 5, 6).asUInt
    val word = request.address.asBits.bits(indexBits + 5, 3).asUInt
    val mask = (1.U(words) << word).asBits.bits(words - 1, 0)
    val lineShift = (index.asBits ## 0.B(3)).asUInt
    val lineMask = (255.U(words) << lineShift).asBits.bits(words - 1, 0)
    val probeAccepted = io.probe.request.valid & io.probe.request.ready
    val probeCompleted = io.probe.response.valid & io.probe.response.ready
    val invalidating = Wire(Bool())
    invalidating := probeAccepted & io.probe.request.bits.invalidate
    if parameter.dCacheWriteback then invalidating := probeCompleted & io.probe.response.bits.last & probeMatch.get & probeRequest.get.invalidate
    val probeAddress = probeRequest.map(_.address).getOrElse(io.probe.request.bits.address)
    val invalidateIndex = probeAddress.asBits.bits(indexBits + 5, 6).asUInt
    val invalidateShift = (invalidateIndex.asBits ## 0.B(3)).asUInt
    val invalidateMask = (255.U(words) << invalidateShift).asBits.bits(words - 1, 0)
    val collision = invalidating & (invalidateIndex === index)
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
    val cacheable = (request.cacheOperation === 0.U(2)) & !request.fetch & !request.atomic & (request.size <= 3.U(3)) &
      DitDahA1Memory.permitted(parameter, request) &
        DitDahA1Memory.dataCacheable(parameter, (request.address.asBits.bits(63, 3) ## 0.B(3)).asUInt, 8)
    val eligible = !request.write & cacheable
    val widening = eligible & (request.size < 3.U(3)) &
      ((request.refillSize === 3.U(3)) | (request.refillSize === 6.U(3))) & DitDahA1Memory.permitted(parameter, refill)
    val lineCandidate = if parameter.enableDataBurstRefill then eligible & (request.refillSize === 6.U(3)) &
      DitDahA1Memory.dataCacheable(parameter, (request.address.asBits.bits(63, 6) ## 0.B(6)).asUInt, 64) else false.B
    val responseFault = down.response.bits.fault | (down.response.bits.tag =/= request.tag) | poisoned.getOrElse(false.B)
    val lineFault = responseFault | (down.response.bits.last =/= lastWord)
    val responding = down.response.valid & down.response.ready & (if concurrent then currentMatch else true.B)
    val wordFilling = (state === 3.U(3)) & responding & !releaseActive & !responseFault & !lineActive & !fault & eligible &
      ((request.size === 3.U(3)) | expanded) & !invalidated & !collision
    val lineFilling = (state === 3.U(3)) & responding & !releaseActive & lineActive & !lineFault & !fault & !invalidated & !collision
    val publish = lineFilling & lastWord & down.response.bits.last
    val storeComplete = (state === 3.U(3)) & responding & !releaseActive & request.write
    val storeUpdating = storeComplete & storeHit & !responseFault & !fault & !invalidated & !collision
    val storeFailed = if parameter.dCacheWriteback then false.B else storeComplete & responseFault
    val filling = wordFilling | lineFilling | storeUpdating
    val reading = up.request.valid & up.request.ready
    val tag = request.address.asBits.bits(parameter.physicalAddressBits - 1, indexBits + 6).asUInt
    val writeWord = beat.map(b => lineActive.?((index.asBits ## b.asBits).asUInt, word)).getOrElse(word)
    val shift = (request.address.asBits.bits(2, 0) ## 0.B(3)).asUInt
    val byteMask = (0 until 8).reverse.map(byte => request.mask.asBits.bit(byte).?(255.B(8), 0.B(8))).reduce(_ ## _)
    val storeMask = (byteMask.asUInt << shift).asBits.bits(63, 0)
    val storeData = ((data.asBits & ~storeMask) | ((request.data << shift).asBits.bits(63, 0) & storeMask)).asUInt
    val probeReading = probeState.map(_ === 2.U(3)).getOrElse(false.B)
    val probeSector = probeWord.map(w => (invalidateIndex.asBits ## w.asBits).asUInt).getOrElse(word)
    val readWord = probeReading.?(probeSector, up.request.bits.address.asBits.bits(indexBits + 5, 3).asUInt)
    val wordRead = StorageArray("data", words, 64,
      readWord, writeWord, storeUpdating.?(storeData, down.response.bits.data), filling, reading | probeReading, io.clock)
    val probeIndex = io.probe.request.bits.address.asBits.bits(indexBits + 5, 6).asUInt
    val probeTagReading = if parameter.dCacheWriteback then probeAccepted else false.B
    val tagRead = StorageArray("dataTags", words / 8, tagBits,
      probeTagReading.?(probeIndex, up.request.bits.address.asBits.bits(indexBits + 5, 6).asUInt), index,
      tag, wordFilling | publish, reading | probeTagReading, io.clock)
    val dirtyRead = Option.when(parameter.dCacheWriteback) {
      val clearing = probeCompleted & (io.probe.response.bits.mask =/= 0.U(8))
      val accessMask = (request.mask << request.address.asBits.bits(2, 0).asUInt).asBits.bits(7, 0).asUInt
      StorageArray("dataDirty", words, 8, readWord, clearing.?(probeSector, writeWord),
        (storeUpdating & acquireActive).?((storedDirty.get.asBits | accessMask.asBits).asUInt, 0.U(8)),
        filling | clearing, reading | probeReading, io.clock)
    }
    val hit = (valid.asUInt >> word).asBits.bit(0) & (tagRead === tag) & !collision & !invalidated
    val readMask = Wire(UInt(64))
    readMask := ((BigInt(1) << 64) - 1).U(64)
    for size <- 0 to 2 do
      when(request.size === size.U(3)) { readMask := ((BigInt(1) << (8 << size)) - 1).U(64) }
    val hitData = ((wordRead >> shift).asBits & readMask.asBits).asUInt
    val refillData = ((down.response.bits.data >> shift).asBits & readMask.asBits).asUInt
    val hitResponse = (state === 1.U(3)) & eligible & hit
    val needsRelease = dirtyLines.map(d => eligible & !hit & (d.asUInt >> index).asBits.bit(0) &
      (lineCandidate | (tagRead =/= tag))).getOrElse(false.B)
    val startLine = (state === 1.U(3)) & !hitResponse & lineCandidate & !needsRelease
    if parameter.dCacheWriteback then
      val ps = probeState.get
      val pw = probeWord.get
      val probeLineMask = (255.U(words) << invalidateShift).asBits.bits(words - 1, 0)
      val dirtyLine = (dirtyLines.get.asUInt >> invalidateIndex).asBits.bit(0)
      io.probe.request.ready := (ps === 0.U(3)) & !down.response.valid
      io.probe.response.valid := ps === 4.U(3)
      io.probe.response.bits.data := probeData.get
      io.probe.response.bits.mask := probeMask.get
      io.probe.response.bits.word := pw
      io.probe.response.bits.last := !probeMatch.get | !dirtyLine | (pw === 7.U(3))
      when(probeAccepted) { probeRequest.get :<= io.probe.request.bits; ps := 1.U(3) }
      when(ps === 1.U(3)) {
        val matching = (tagRead === probeAddress.asBits.bits(63, indexBits + 6).asUInt) & ((valid & probeLineMask) =/= 0.B(words))
        probeMatch.get := matching
        pw := 0.U(3)
        probeData.get := 0.U(64)
        probeMask.get := 0.U(8)
        ps := (matching & dirtyLine).?(2.U(3), 4.U(3))
      }
      when(ps === 2.U(3)) { ps := 3.U(3) }
      when(ps === 3.U(3)) {
        probeData.get := wordRead
        probeMask.get := (valid.asUInt >> probeSector).asBits.bit(0).?(dirtyRead.get, 0.U(8))
        ps := 4.U(3)
      }
      when(probeCompleted) {
        when(io.probe.response.bits.last) { ps := 0.U(3) }
          .otherwise { pw := (pw + 1.U(3)).asBits.bits(2, 0).asUInt; ps := 2.U(3) }
      }
      val bit = (1.U(words / 8) << index).asBits.bits(words / 8 - 1, 0)
      val probeBit = (1.U(words / 8) << invalidateIndex).asBits.bits(words / 8 - 1, 0)
      when(storeUpdating & acquireActive) { dirtyLines.get := dirtyLines.get | bit }
      when(probeCompleted & io.probe.response.bits.last & probeMatch.get) { dirtyLines.get := dirtyLines.get & ~probeBit }
    else
      val probePending = RegInit(false.B)
      io.probe.request.ready := !probePending | io.probe.response.ready
      io.probe.response.valid := probePending
      io.probe.response.bits.data := 0.U(64)
      io.probe.response.bits.mask := 0.U(8)
      io.probe.response.bits.word := 0.U(3)
      io.probe.response.bits.last := true.B
      when(probeCompleted) { probePending := false.B }
      when(probeAccepted) { probePending := true.B }
    up.request.ready := ((state === 0.U(3)) | (up.response.valid & up.response.ready)) &
      (if parameter.dCacheWriteback then !probeActive & !io.probe.request.valid else true.B)
    up.response.valid := (state === 4.U(3)) | hitResponse
    up.response.bits.data := hitResponse.?(hitData, data)
    up.response.bits.fault := !hitResponse & fault
    up.response.bits.tag := request.tag
    up.response.bits.last := true.B
    val transmit = if !concurrent then request else
      val selected = Wire(new MemoryRequest)
      selected :<= request
      when(offered.get & parkedValid.get & (offerTag.get === parked.get.request.tag)) { selected :<= parked.get.request }
      selected
    def transmitFlag(active: Referable[Bool], saved: Referable[DataCacheContext] => Referable[Bool])
      (using Arena, Context, Block, InstanceContext): Referable[Bool] =
      if !concurrent then active else
        (offered.get & parkedValid.get & (offerTag.get === parked.get.request.tag)).?(saved(parked.get), active)
    val transmitExpanded = transmitFlag(expanded, _.expanded)
    val transmitLine = transmitFlag(lineActive, _.line.getOrElse(false.B))
    val transmitRelease = transmitFlag(releaseActive, _.releasing.getOrElse(false.B))
    val transmitFault = transmitFlag(fault, _.fault)
    val transmitVictim = if !parameter.dCacheWriteback then 0.U(64) else if !concurrent then victim.get else
      (offered.get & parkedValid.get & (offerTag.get === parked.get.request.tag)).?(parked.get.victim.get, victim.get)
    down.request.valid := offered.getOrElse(state === 2.U(3))
    down.request.bits :<= transmit
    when(transmitExpanded | transmitLine) {
      down.request.bits.address := (transmit.address.asBits.bits(63, 3) ## 0.B(3)).asUInt
      down.request.bits.size := 3.U(3); down.request.bits.refillSize := 3.U(3)
    }
    when(transmitLine) {
      down.request.bits.address := (transmit.address.asBits.bits(63, 6) ## 0.B(6)).asUInt
      down.request.bits.size := 6.U(3); down.request.bits.refillSize := 6.U(3)
    }
    acquiring.foreach(a => when(a & !transmitRelease) { down.request.bits.cacheOperation := 1.U(2) })
    if parameter.dCacheWriteback then
      when(transmitRelease) {
        down.request.bits.cacheOperation := 2.U(2)
        down.request.bits.address := transmitVictim
        down.request.bits.data := 0.U(64)
        down.request.bits.mask := 0.U(8)
        down.request.bits.size := 3.U(3)
        down.request.bits.write := false.B
        down.request.bits.fetch := false.B
        down.request.bits.atomic := false.B
        down.request.bits.atomicOperation := 0.U(5)
        down.request.bits.scEligible := false.B
        down.request.bits.refillSize := 0.U(3)
      }
    when(transmitFault) { down.request.bits.refillSize := 0.U(3) }
    down.response.ready := ((state === 3.U(3)) | (if parameter.enableDataBurstRefill then state === 5.U(3) else false.B)) & !probeActive
    when(state === 1.U(3)) {
      sameTag := tagRead === tag
      storeHit := request.write & cacheable & hit
      acquiring.foreach(_ := request.write & cacheable & hit)
      releasing.foreach(_ := needsRelease)
      storedDirty.foreach(_ := dirtyRead.get)
      victim.foreach(_ := (tagRead.asBits ## index.asBits ## 0.B(6)).asUInt)
      when(request.write) { data := wordRead }
      when(eligible & hit) { data := hitData; fault := false.B; state := 4.U(3) }
        .otherwise { expanded := widening & !lineCandidate; line.foreach(_ := lineCandidate); state := 2.U(3) }
    }
    when(capture) { state := 3.U(3); when(releaseActive) { fault := false.B } }
    when(responding) {
      when(releaseActive) {
        if parameter.dCacheWriteback then
          fault := fault | responseFault | !down.response.bits.last
          when(down.response.bits.last) {
            state := 2.U(3)
            when(!fault & !responseFault & !(dirtyLines.get.asUInt >> index).asBits.bit(0)) {
              releasing.get := false.B; invalidated := false.B; sameTag := false.B; fault := false.B
            }
          }
      }.otherwise { when(lineActive) {
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
        when(acquireActive & !responseFault & (invalidated | collision)) {
          acquiring.foreach(_ := false.B); storeHit := false.B; state := 2.U(3)
        }.otherwise { when(expanded & responseFault) { expanded := false.B; fault := true.B; state := 2.U(3) }
          .otherwise {
            data := expanded.?(refillData, down.response.bits.data)
            fault := responseFault
            state := 4.U(3)
          }
        } }
      }
    }
    val allocated = sameTag.?(valid, valid & ~lineMask) | mask
    val nextValid = (startLine | storeFailed).?(valid & ~lineMask, publish.?(valid | lineMask, wordFilling.?(allocated, valid)))
    when(startLine | storeFailed | publish | wordFilling | invalidating) { valid := invalidating.?(nextValid & ~invalidateMask, nextValid) }
    when(up.response.valid & up.response.ready) { state := 0.U(3) }
    when(invalidating) {
      when((state =/= 0.U(3)) & (invalidateIndex === index)) { invalidated := true.B }
    }
    when(reading) {
      request :<= up.request.bits
      invalidated := invalidating &
        (invalidateIndex === up.request.bits.address.asBits.bits(indexBits + 5, 6).asUInt)
      expanded := false.B
      line.foreach(_ := false.B)
      beat.foreach(_ := 0.U(3))
      fault := false.B
      acquiring.foreach(_ := false.B)
      releasing.foreach(_ := false.B)
      state := 1.U(3)
    }
    if concurrent then
      val extra = parked.get
      val extraIndex = extra.request.address.asBits.bits(indexBits + 5, 6).asUInt
      val extraCollision = invalidating & (invalidateIndex === extraIndex)
      val extraMatch = parkedValid.get & (down.response.bits.tag === extra.request.tag)
      val unknown = !currentMatch & !extraMatch
      def ordinary(value: Referable[MemoryRequest])(using Arena, Context, Block, InstanceContext): Referable[Bool] =
        val device = parameter.memoryRegions.filter(_.device).foldLeft[Referable[Bool]](false.B) { (selected, region) =>
          selected | ((value.address >= region.base.U(64)) & (value.address < (region.base + region.size).U(64)))
        }
        !value.write & !value.atomic & !value.fetch & (value.cacheOperation === 0.U(2)) & (value.size <= 3.U(3)) & !device
      val park = waiting & !parkedValid.get & !down.response.valid & ordinary(request) & ordinary(up.request.bits) &
        (up.request.bits.tag =/= request.tag) & (up.request.bits.address.asBits.bits(indexBits + 5, 6).asUInt =/= index)
      val switch = waiting & down.response.valid & extraMatch & !currentMatch
      val restore = up.response.valid & up.response.ready & parkedValid.get
      def saveContext()(using Arena, Context, Block, InstanceContext): Unit =
        extra.request :<= request
        extra.request.data := 0.U(64); extra.request.mask := 0.U(8)
        extra.request.write := false.B; extra.request.atomic := false.B; extra.request.fetch := false.B
        extra.request.atomicOperation := 0.U(5); extra.request.cacheOperation := 0.U(2); extra.request.scEligible := false.B
        extra.fault := fault; extra.invalidated := invalidated | collision; extra.sameTag := sameTag; extra.expanded := expanded
        extra.data.foreach(_ := data); extra.line.foreach(_ := line.get); extra.beat.foreach(_ := beat.get)
        extra.draining.foreach(_ := state === 5.U(3))
        extra.releasing.foreach(_ := releasing.get); extra.victim.foreach(_ := victim.get)
      def restoreContext()(using Arena, Context, Block, InstanceContext): Unit =
        request :<= extra.request
        fault := extra.fault; invalidated := extra.invalidated | extraCollision; sameTag := extra.sameTag; expanded := extra.expanded
        extra.data.foreach(value => data := value); extra.line.foreach(value => line.get := value); extra.beat.foreach(value => beat.get := value)
        state := extra.draining.map(_.?(5.U(3), 3.U(3))).getOrElse(3.U(3))
        storeHit := false.B; acquiring.foreach(_ := false.B)
        extra.releasing.foreach(value => releasing.get := value); extra.victim.foreach(value => victim.get := value)
      up.request.ready := (((state === 0.U(3)) | (up.response.valid & up.response.ready)) & !parkedValid.get | park) &
        !poisoned.get & (if parameter.dCacheWriteback then !probeActive & !io.probe.request.valid else true.B)
      down.response.ready := (waiting & !probeActive & currentMatch) | (unknown & (waiting | parkedValid.get))
      when(capture) { offered.get := true.B; offerTag.get := request.tag }
      when(down.request.valid & down.request.ready) { offered.get := false.B }
      when(reading & park) { saveContext(); parkedValid.get := true.B }
      when(switch) { saveContext(); restoreContext() }
      when(restore) { restoreContext(); parkedValid.get := false.B }
      when(parkedValid.get & extraCollision & !switch & !restore) { extra.invalidated := true.B }
      when(down.response.valid & down.response.ready & unknown) { poisoned.get := true.B }
      when(((state === 2.U(3)) | (responding & down.response.bits.last)) & poisoned.get) {
        fault := true.B; data := 0.U(64); state := 4.U(3); expanded := false.B; line.foreach(_ := false.B)
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
