// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

class DitDahA1JtagDtmIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val tck = Flipped(Clock())
  val reset = Flipped(Reset())
  val trstN = Flipped(Bool())
  val tms = Flipped(Bool())
  val tdi = Flipped(Bool())
  val tdo = Aligned(Bool())
  val tdoEnable = Aligned(Bool())
  val dmi = Aligned(new DmiPort)

@generator
object DitDahA1JtagDtm extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1JtagDtmIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1JtagDtm"
  def architecture(parameter: DitDahA1Parameter) =
    require(parameter.jtagIdcode.nonEmpty, "JTAG transport requires an explicit IDCODE")
    val io = summon[Interface[DitDahA1JtagDtmIO]]
    val reset = Wire(new DebugReset.Signal)
    reset.value := (io.reset.asBool | !io.trstN).asReset
    val tapReset = DebugReset.release(io.tck, reset.value)
    given ClockScope = ClockScope.posedge(io.tck)
    given ResetScope = ResetScope.asyncActiveHigh(tapReset)
    val state = RegInit(0.U(4))
    val irShift = RegInit(1.B(5))
    val drShift = RegInit(0.B(41))
    val ir = ClockScope.negedge(io.tck) {
      val value = RegInit(1.U(5))
      when(state === 0.U(4)) { value := 1.U(5) }
      when(state === 15.U(4)) { value := irShift.asUInt }
      value
    }
    val transitions = Seq((1, 0), (1, 2), (3, 9), (4, 5), (4, 5), (6, 8), (6, 7), (4, 8),
      (1, 2), (10, 0), (11, 12), (11, 12), (13, 15), (13, 14), (11, 15), (1, 2))
    for ((low, high), index) <- transitions.zipWithIndex do
      when(state === index.U(4)) { state := io.tms.?(high.U(4), low.U(4)) }
    when(state === 10.U(4)) { irShift := 1.B(5) }
    when(state === 11.U(4)) { irShift := io.tdi.asBits ## irShift.bits(4, 1) }
    val sticky = RegInit(0.U(2))
    val waiting = RegInit(false.B)
    val responseData = RegInit(0.U(32))
    val address = RegInit(0.U(7))
    val dtmcs = 0.B(17) ## 1.B(3) ## sticky.asBits ## 7.B(6) ## 1.B(4)
    io.dmi.response.ready := true.B
    val completing = io.dmi.response.valid & waiting
    val completionStatus = (io.dmi.response.bits.status === 1.U(2)).?(2.U(2), io.dmi.response.bits.status)
    val captureStatus = (sticky =/= 0.U(2)).?(sticky, (waiting & !completing).?(3.U(2),
      completing.?(completionStatus, 0.U(2))))
    when(completing) {
      waiting := false.B
      responseData := io.dmi.response.bits.data
      when((sticky === 0.U(2)) & (completionStatus =/= 0.U(2))) { sticky := completionStatus }
    }
    when(state === 3.U(4)) {
      drShift := 0.B(41)
      when(ir === 1.U(5)) { drShift := parameter.jtagIdcode.get.B(41) }
      when(ir === 16.U(5)) { drShift := 0.B(9) ## dtmcs }
      when(ir === 17.U(5)) {
        drShift := address.asBits ## completing.?(io.dmi.response.bits.data, responseData).asBits ## captureStatus.asBits
        when(captureStatus =/= 0.U(2)) { sticky := captureStatus.asBits.bit(1).?(captureStatus, 2.U(2)) }
      }
    }
    when(state === 4.U(4)) {
      drShift := 0.B(40) ## io.tdi.asBits
      when((ir === 1.U(5)) | (ir === 16.U(5))) { drShift := 0.B(9) ## io.tdi.asBits ## drShift.bits(31, 1) }
      when(ir === 17.U(5)) { drShift := io.tdi.asBits ## drShift.bits(40, 1) }
    }
    val operation = drShift.bits(1, 0).asUInt
    val attempt = (state === 8.U(4)) & (ir === 17.U(5)) & (sticky === 0.U(2)) &
      ((operation === 1.U(2)) | (operation === 2.U(2)))
    io.dmi.request.valid := attempt & !waiting & io.dmi.request.ready
    io.dmi.request.bits.address := drShift.bits(40, 34).asUInt
    io.dmi.request.bits.data := drShift.bits(33, 2).asUInt
    io.dmi.request.bits.op := operation
    when(attempt) {
      when(waiting | !io.dmi.request.ready) { sticky := 3.U(2) }
      when(io.dmi.request.valid) {
        waiting := true.B
        address := drShift.bits(40, 34).asUInt
      }
    }
    when((state === 8.U(4)) & (ir === 16.U(5)) & drShift.bit(16)) { sticky := 0.U(2) }
    when((state === 0.U(4)) | ((state === 8.U(4)) & (ir === 16.U(5)) & drShift.bit(17))) {
      waiting := false.B
      sticky := 0.U(2)
      responseData := 0.U(32)
      address := 0.U(7)
    }
    val tdo = ClockScope.negedge(io.tck) {
      val value = RegInit(false.B)
      value := (state === 11.U(4)).?(irShift.bit(0), (state === 4.U(4)) & drShift.bit(0))
      value
    }
    io.tdo := tdo
    io.tdoEnable := (state === 4.U(4)) | (state === 11.U(4))
