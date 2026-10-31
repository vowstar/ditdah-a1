// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.mlir.scalalib.capi.ir.Block

class DitDahA1InstructionCacheIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val upstream = Flipped(new InstructionCachePort(parameter))
  val downstream = Aligned(new MemoryPort(parameter))
  val cancel = Flipped(Bool())
  val invalidate = Flipped(Bool())
  val checkAddress = Aligned(UInt(64))
  val checkSize = Aligned(UInt(3))
  val allowed = Flipped(Bool())

@generator
object DitDahA1InstructionCache extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1InstructionCacheIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1InstructionCache"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1InstructionCacheIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val indexBits = Integer.numberOfTrailingZeros(parameter.iCacheBytes) - 6
    val lines = parameter.iCacheBytes / 64
    val tagBits = parameter.physicalAddressBits - indexBits - 6
    val banks = parameter.fetchWords
    val bankBits = Integer.numberOfTrailingZeros(banks)
    val state = RegInit(0.U(3))
    val address = Reg(UInt(64))
    val tag = Reg(UInt(8))
    val privileged = Option.when(parameter.enableUserMode)(Reg(Bool()))
    val debugOrigin = Option.when(parameter.enableDebugMemory)(Reg(Bool()))
    val data = Reg(UInt(32 * banks))
    val count = Option.when(banks > 1)(Reg(UInt(parameter.fetchCountBits)))
    val wide = Option.when(banks > 1)(Reg(Bool()))
    val fault = Reg(Bool())
    val valid = RegInit(0.B(lines))
    val word = Reg(UInt(4))
    val bypass = Reg(Bool())
    val halfword = Option.when(parameter.enableC)(Reg(Bool()))
    def parcel(value: Referable[UInt])(using Block) = if parameter.enableC then
      (halfword.get & address.asBits.bit(1)).?((0.B(16) ## value.asBits.bits(31, 16)).asUInt, value)
      else value
    val killed = RegInit(false.B)
    val upperWord = Option.when(parameter.enableBurstRefill)(Reg(UInt(32)))
    val terminal = Option.when(parameter.enableBurstRefill)(Reg(Bool()))
    val up = io.upstream
    val down = io.downstream
    val index = address.asBits.bits(indexBits + 5, 6).asUInt
    val mask = (1.U(lines) << index).asBits.bits(lines - 1, 0)
    val demandWord = address.asBits.bits(5, 2).asUInt
    val burst = if parameter.enableBurstRefill then !bypass else false.B
    val refillWord = if parameter.enableBurstRefill then 0.U(4) else word
    val candidate = bypass.?(address, (address.asBits.bits(63, 6) ## refillWord.asBits ## 0.B(2)).asUInt)
    val abort = killed | io.cancel | io.invalidate
    up.response.bits.tag := tag
    up.response.bits.last := true.B
    io.checkAddress := candidate
    val narrow = if parameter.enableC then (bypass & halfword.get).?(1.U(3), 2.U(3)) else 2.U(3)
    io.checkSize := burst.?(6.U(3), narrow)
    down.request.valid := state === 3.U(3)
    down.request.bits.address := candidate
    down.request.bits.data := 0.U(64)
    down.request.bits.size := io.checkSize
    down.request.bits.mask := 0.U(8)
    down.request.bits.tag := tag
    down.request.bits.write := false.B
    down.request.bits.fetch := true.B
    down.request.bits.privileged := privileged.getOrElse(true.B)
    down.request.bits.atomic := false.B
    down.request.bits.atomicOperation := 0.U(5)
    down.request.bits.cacheOperation := 0.U(2)
    down.request.bits.scEligible := false.B
    down.request.bits.refillSize := 0.U(3)
    down.request.bits.debug.foreach(_ := debugOrigin.get)
    down.response.ready := state === 4.U(3)
    val reading = up.request.valid & up.request.ready
    val responseFault = down.response.bits.fault | (down.response.bits.tag =/= tag)
    val received = down.response.valid & down.response.ready
    val lineFault = fault | responseFault | (down.response.bits.last =/= (word === 14.U(4)))
    val filling = if parameter.enableBurstRefill then
      !bypass & !abort & (((state === 6.U(3)) & !fault) | (received & !lineFault))
    else received & !responseFault & !bypass & !abort
    val writeData = upperWord.map(value => (state === 6.U(3)).?(value, down.response.bits.data.asBits.bits(31, 0).asUInt))
      .getOrElse(down.response.bits.data.asBits.bits(31, 0).asUInt)
    val complete = word === 15.U(4)

    val wordReads = (0 until banks).map { bank =>
      val selected = if banks == 1 then true.B else up.request.bits.address.asBits.bits(bankBits + 1, 2).asUInt === bank.U(bankBits)
      val writing = if banks == 1 then filling else filling & (word.asBits.bits(bankBits - 1, 0).asUInt === bank.U(bankBits))
      val writeWord = if banks == 1 then word else word.asBits.bits(3, bankBits).asUInt
      val full = if banks == 1 then false.B else up.request.bits.size === (bankBits + 2).U(3)
      StorageArray("instructions", parameter.iCacheBytes / (4 * banks), 32,
        up.request.bits.address.asBits.bits(indexBits + 5, bankBits + 2).asUInt,
        (index.asBits ## writeWord.asBits).asUInt, writeData, writing, reading & (full | selected), io.clock)
    }
    val wordRead = if banks == 1 then wordReads.head else
      val block = wordReads.reverse.map(_.asBits).reduce(_ ## _).asUInt
      val shift = (address.asBits.bits(bankBits + 1, 2) ## 0.B(5)).asUInt
      val suffix = (block >> shift).asBits.bits(32 * banks - 1, 0).asUInt
      wide.get.?(suffix, suffix.asBits.bits(31, 0).asUInt)
    val lookupCount = if banks == 1 then 1.U(1) else wide.get.?(
      (banks.U(parameter.fetchCountBits) - address.asBits.bits(bankBits + 1, 2).asUInt).asBits.bits(parameter.fetchCountBits - 1, 0).asUInt,
      1.U(parameter.fetchCountBits))
    val tagRead = StorageArray("tags", lines, tagBits,
      up.request.bits.address.asBits.bits(indexBits + 5, 6).asUInt, index,
      address.asBits.bits(parameter.physicalAddressBits - 1, indexBits + 6).asUInt, filling & complete, reading, io.clock)
    val hit = !DitDahA1Memory.debugWindow(parameter, address, 0.U(3)) & (valid.asUInt >> index).asBits.bit(0) &
      (tagRead === address.asBits.bits(parameter.physicalAddressBits - 1, indexBits + 6).asUInt)
    val lookupHit = (state === 1.U(3)) & hit & !abort
    up.response.valid := lookupHit | (state === 5.U(3))
    up.response.bits.data := lookupHit.?(parcel(wordRead), data)
    up.response.bits.fault := !lookupHit & fault
    up.response.bits.count.foreach(_ := lookupHit.?(lookupCount, count.get))
    up.request.ready := !io.cancel & !io.invalidate & ((state === 0.U(3)) | (!killed & up.response.valid & up.response.ready))

    when(state === 1.U(3)) {
      when(abort) { state := 5.U(3) }.otherwise {
        when(hit) {
          data := parcel(wordRead)
          count.foreach(_ := lookupCount)
          state := up.response.ready.?(0.U(3), 5.U(3))
        }.otherwise {
          valid := valid & ~mask
          state := 2.U(3)
        }
      }
    }
    when(state === 2.U(3)) {
      when(abort) { state := 5.U(3) }.otherwise {
        when(io.allowed) { state := 3.U(3) }.otherwise {
          if parameter.enableBurstRefill then
            when(bypass) { fault := true.B; state := 5.U(3) }.otherwise { bypass := true.B }
          else
            when(bypass | ((word === demandWord) & !halfword.getOrElse(false.B))) { fault := true.B; state := 5.U(3) }.otherwise {
              bypass := true.B
            }
        }
      }
    }
    when(down.request.valid & down.request.ready) { state := 4.U(3) }
    when(received & !burst) {
      when(abort) { state := 5.U(3) }.otherwise {
        when(responseFault) {
          when(bypass | ((word === demandWord) & !halfword.getOrElse(false.B))) { fault := true.B; state := 5.U(3) }.otherwise {
            bypass := true.B
            state := 2.U(3)
          }
        }.otherwise {
          when(bypass | (word === demandWord)) { data := bypass.?(down.response.bits.data.asBits.bits(31, 0).asUInt, parcel(down.response.bits.data.asBits.bits(31, 0).asUInt)) }
          when(bypass) { state := 5.U(3) }.otherwise {
            when(complete) { valid := valid | mask; state := 5.U(3) }.otherwise {
              word := (word + 1.U(4)).asBits.bits(3, 0).asUInt
              state := 2.U(3)
            }
          }
        }
      }
    }
    if parameter.enableBurstRefill then
      when(received & burst) {
        upperWord.get := down.response.bits.data.asBits.bits(63, 32).asUInt
        terminal.get := down.response.bits.last
        fault := lineFault
        when(word =/= 15.U(4)) { word := (word + 1.U(4)).asBits.bits(3, 0).asUInt }
        when((word === demandWord) & !abort & !lineFault) { data := parcel(down.response.bits.data.asBits.bits(31, 0).asUInt) }
        state := 6.U(3)
      }
      when(state === 6.U(3)) {
        when((word === demandWord) & !abort & !fault) { data := parcel(upperWord.get) }
        state := 4.U(3)
        when(word =/= 15.U(4)) { word := (word + 1.U(4)).asBits.bits(3, 0).asUInt }
        when(terminal.get) {
          state := 5.U(3)
          when(!abort) {
            when(fault) { bypass := true.B; fault := false.B; state := 2.U(3) }
              .otherwise { valid := valid | mask }
          }
        }
      }
    when(up.response.valid & up.response.ready) { state := 0.U(3) }
    when((io.cancel | io.invalidate) & (state =/= 0.U(3))) { killed := true.B }
    when(io.invalidate) { valid := 0.B(lines) }
    when(reading) {
      privileged.foreach(_ := up.request.bits.privileged)
      debugOrigin.foreach(_ := up.request.bits.debug.get)
      address := up.request.bits.address
      tag := up.request.bits.tag
      data := 0.U(32 * banks)
      count.foreach(_ := 1.U(parameter.fetchCountBits))
      wide.foreach(_ := up.request.bits.size === (bankBits + 2).U(3))
      fault := false.B
      word := 0.U(4)
      bypass := DitDahA1Memory.debugWindow(parameter, up.request.bits.address, up.request.bits.size)
      halfword.foreach(_ := up.request.bits.size === 1.U(3))
      killed := false.B
      state := 1.U(3)
    }
