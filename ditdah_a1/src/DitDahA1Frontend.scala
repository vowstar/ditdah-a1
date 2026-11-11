// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

@generator
object DitDahA1Frontend extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1FrontendIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Frontend"
  def architecture(parameter: DitDahA1Parameter) =
    parameter.validateFrontend()
    val io = summon[Interface[DitDahA1FrontendIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val pc = RegInit(parameter.resetVector.U(64))
    val requestPc = Wire(UInt(64))
    requestPc := pc
    val tag = RegInit(0.U(8))
    val fetch = DitDahA1Fetch.instantiate(parameter)
    if parameter.pmpEntries != 0 then fetch.io.pmp.get :<= io.pmp.get
    fetch.io.clock := io.clock
    fetch.io.reset := io.reset
    fetch.io.privilege := io.privilege
    fetch.io.debugMode.foreach(_ := io.debugMode.get)
    if parameter.enableTranslation then io.translation.get :<>= fetch.io.translation.get
    fetch.io.request.valid := !io.redirect & !io.halt
    fetch.io.request.bits.pc := requestPc
    fetch.io.request.bits.tag := tag
    fetch.io.cancel := io.redirect
    if parameter.iCacheBytes != 0 then fetch.io.invalidate.get := io.invalidate.get
    io.memory :<>= fetch.io.memory
    val width = parameter.issueWidth
    val words = parameter.fetchWords
    val capacity = parameter.frontendCapacity
    val countBits = 32 - Integer.numberOfLeadingZeros(capacity + words)
    val queued = RegInit(0.U(countBits))
    val buffer = Reg(Vec(capacity, new FetchPacket))
    val held = RegInit(0.U(32 - Integer.numberOfLeadingZeros(width)))
    val pending = RegInit(false.B)
    val pendingPc = Reg(UInt(64))
    val reserved = Reg(UInt(parameter.fetchCountBits))
    val faultPending = RegInit(false.B)
    val flush = io.redirect | io.invalidate.getOrElse(false.B)
    val entries = parameter.branchPredictorEntries
    val indexBits = if entries == 0 then 0 else Integer.numberOfTrailingZeros(entries)
    val alignBits = if parameter.enableC then 1 else 2
    val predictor = io.prediction.map { update =>
      val valid = RegInit(0.B(entries))
      val tags = Reg(Vec(entries, UInt(64 - alignBits - indexBits)))
      val targets = Reg(Vec(entries, UInt(64)))
      val counters = Reg(Vec(entries, UInt(2)))
      val conditional = Reg(Vec(entries, Bool()))
      val index = update.pc.asBits.bits(indexBits + alignBits - 1, alignBits).asUInt
      val tag = update.pc.asBits.bits(63, indexBits + alignBits).asUInt
      val hit = (valid.asUInt >> index).asBits.bit(0) & (tags.ref(index) === tag) & (conditional.ref(index) === update.conditional)
      val counter = counters.ref(index)
      val increment = (counter === 3.U(2)).?(counter, (counter + 1.U(2)).asBits.bits(1, 0).asUInt)
      val decrement = (counter === 0.U(2)).?(counter, (counter - 1.U(2)).asBits.bits(1, 0).asUInt)
      when(update.valid & !update.clear) {
        valid := valid | (1.U(entries) << index).asBits.bits(entries - 1, 0)
        tags.ref(index) := tag
        targets.ref(index) := update.nextPc
        counters.ref(index) := hit.?(update.taken.?(increment, decrement), update.taken.?(2.U(2), 1.U(2)))
        conditional.ref(index) := update.conditional
      }
      when(update.clear) { valid := 0.B(entries) }
      (valid, tags, targets, counters, conditional)
    }
    val returned = fetch.io.output.valid & !flush
    val fetched = fetch.io.output.bits
    val incoming = Wire(Vec(words, new FetchPacket))
    for i <- 0 until words do
      incoming(i).pc := (fetched.pc + (4 * i).U(64)).asBits.bits(63, 0).asUInt
      incoming(i).tag := (fetched.tag + i.U(8)).asBits.bits(7, 0).asUInt
      incoming(i).predictedTaken := false.B
      incoming(i).predictedPc.get := 0.U(64)
      incoming(i).instruction := (if i == 0 then fetched.instruction else fetched.following.get(i - 1))
      incoming(i).length := (if parameter.enableC then fetched.length else 4.U(3))
      incoming(i).fault := (if i == 0 then fetched.fault else false.B)
      incoming(i).cause := (if i == 0 then fetched.cause else 0.U(64))
      incoming(i).tval := (if i == 0 then fetched.tval else 0.U(64))
    val returnedCount = Wire(UInt(parameter.fetchCountBits))
    returnedCount := returned.?(fetched.count.getOrElse(1.U(1)), 0.U(parameter.fetchCountBits))
    val predicted = Wire(Bool())
    predicted := false.B
    if parameter.enableBranchPrediction then
      for i <- (0 until words).reverse do
        val insn = if parameter.enableC then (incoming(i).length === 2.U(3)).?(DitDahA1Compressed(incoming(i).instruction, parameter), incoming(i).instruction.asBits) else incoming(i).instruction.asBits
        val jump = insn.bits(6, 0) === 0x6f.B(7)
        val branch = (insn.bits(6, 0) === 0x63.B(7)) &
          ((insn.bits(14, 12) === 0.B(3)) | (insn.bits(14, 12) === 1.B(3)) | insn.bit(14))
        val indirect = (insn.bits(6, 0) === 0x67.B(7)) & (insn.bits(14, 12) === 0.B(3))
        val direction = Wire(Bool())
        val indirectHit = Wire(Bool())
        direction := insn.bit(31)
        indirectHit := false.B
        val branchOffset = (insn.bit(31).?(((BigInt(1) << 51) - 1).B(51), 0.B(51)) ## insn.bits(31, 31) ## insn.bits(7, 7) ## insn.bits(30, 25) ## insn.bits(11, 8) ## 0.B(1)).asUInt
        val jumpOffset = (insn.bit(31).?(((BigInt(1) << 43) - 1).B(43), 0.B(43)) ## insn.bits(31, 31) ## insn.bits(19, 12) ## insn.bits(20, 20) ## insn.bits(30, 21) ## 0.B(1)).asUInt
        val target = Wire(UInt(64))
        target := (incoming(i).pc + jump.?(jumpOffset, branchOffset)).asBits.bits(63, 0).asUInt
        predictor.foreach { (valid, tags, targets, counters, conditional) =>
          val index = incoming(i).pc.asBits.bits(indexBits + alignBits - 1, alignBits).asUInt
          val hit = (valid.asUInt >> index).asBits.bit(0) &
            (tags.ref(index) === incoming(i).pc.asBits.bits(63, indexBits + alignBits).asUInt)
          val learnedDirection = (0 until entries).map(n =>
            (index === n.U(indexBits)) & counters(n).asBits.bit(1)).reduce(_ | _)
          direction := (hit & conditional.ref(index)).?(learnedDirection, insn.bit(31))
          indirectHit := indirect & hit & !conditional.ref(index)
          when(indirectHit) { target := targets.ref(index) }
        }
        val taken = jump | (branch & direction) | indirectHit
        incoming(i).predictedTaken := taken & !fetched.fault
        if entries != 0 then incoming(i).predictedPc.get := (taken & !fetched.fault).?(target, 0.U(64))
        when(returned & !fetched.fault & (i.U < fetched.count.getOrElse(1.U(1))) & taken) {
          predicted := true.B
          returnedCount := (i + 1).U(parameter.fetchCountBits)
          requestPc := target
        }
    val available = (queued + returnedCount).asBits.bits(countBits - 1, 0).asUInt
    val view = Wire(Vec(capacity + words, new FetchPacket))
    for i <- 0 until capacity + words do
      view(i) :<= incoming.ref((i.U(countBits) - queued).asBits.bits(countBits - 1, 0).asUInt)
      if i < capacity then when(i.U(countBits) < queued) { view(i) :<= buffer(i) }
    val offered = (held =/= 0.U).?(held, (available >= width.U).?(width.U, available))
      .asBits.bits(31 - Integer.numberOfLeadingZeros(width), 0).asUInt
    val take = (io.output.valid & io.output.ready).?(offered, 0.U(countBits))
    val remaining = (available - take).asBits.bits(countBits - 1, 0).asUInt
    io.output.valid := (available =/= 0.U) & !flush
    io.output.bits.count := offered
    for i <- 0 until width do io.output.bits.packets(i) :<= view(i)
    fetch.io.output.ready := !flush
    val expected = if words == 1 then 1.U(parameter.fetchCountBits) else
      (words.U(parameter.fetchCountBits) - requestPc.asBits.bits(Integer.numberOfTrailingZeros(words) + 1, 2).asUInt)
        .asBits.bits(parameter.fetchCountBits - 1, 0).asUInt
    val owned = remaining + (pending & !returned).?(reserved, 0.U(parameter.fetchCountBits))
    val queuedFault = (0 until capacity).map(i => (i.U(countBits) < queued) & buffer(i).fault).reduce(_ | _)
    fetch.io.request.valid := !flush & !io.halt & !faultPending & !queuedFault & !(returned & fetched.fault) &
      (owned + expected <= capacity.U)
    when(!flush) {
      queued := remaining
      held := (io.output.valid & !io.output.ready).?(offered, 0.U)
      for i <- 0 until capacity do
        when(i.U(countBits) < remaining) { buffer(i) :<= view.ref((take + i.U(countBits)).asBits.bits(countBits - 1, 0).asUInt) }
    }
    when(io.output.valid & io.output.ready) {
      for i <- 0 until width do
        when((i.U < offered) & view(i).fault) { faultPending := true.B }
    }
    when(returned) {
      pending := false.B
      if parameter.enableC then pc := (fetched.pc + fetched.length).asBits.bits(63, 0).asUInt
      when(returnedCount < reserved) { pc := (fetched.pc + (returnedCount << 2)).asBits.bits(63, 0).asUInt }
      when(predicted) { pc := requestPc }
    }
    when(fetch.io.request.valid & fetch.io.request.ready) {
      pending := true.B
      pendingPc := requestPc
      reserved := expected
      pc := (if parameter.enableC then requestPc else (requestPc + (expected << 2)).asBits.bits(63, 0).asUInt)
      tag := (tag + expected).asBits.bits(7, 0).asUInt
    }
    when(flush) {
      pc := (queued =/= 0.U).?(buffer(0).pc, pending.?(pendingPc, pc))
      queued := 0.U
      held := 0.U
      pending := false.B
    }
    when(io.redirect) { pc := io.redirectPc; faultPending := false.B }
