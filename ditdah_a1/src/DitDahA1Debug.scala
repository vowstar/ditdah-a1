// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

class DmiRequest extends Bundle:
  val address = Aligned(UInt(7))
  val data = Aligned(UInt(32))
  val op = Aligned(UInt(2))
class DmiResponse extends Bundle:
  val data = Aligned(UInt(32))
  val status = Aligned(UInt(2))
class DmiPort extends Bundle:
  val request = Aligned(new Decoupled(new DmiRequest))
  val response = Flipped(new Decoupled(new DmiResponse))
class JtagPort extends Bundle:
  val tck = Flipped(Clock())
  val trstN = Flipped(Bool())
  val tms = Flipped(Bool())
  val tdi = Flipped(Bool())
  val tdo = Aligned(Bool())
  val tdoEnable = Aligned(Bool())
class DitDahA1JtagDtmIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val tck = Flipped(Clock())
  val reset = Flipped(Reset())
  val trstN = Flipped(Bool())
  val tms = Flipped(Bool())
  val tdi = Flipped(Bool())
  val tdo = Aligned(Bool())
  val tdoEnable = Aligned(Bool())
  val dmi = Aligned(new DmiPort)
class DitDahA1DmiBridgeIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val tck = Flipped(Clock())
  val reset = Flipped(Reset())
  val upstream = Flipped(new DmiPort)
  val downstream = Aligned(new DmiPort)

private[a1] object DebugReset:
  class Signal extends Bundle:
    val value = Aligned(Reset())
  def release(clock: Ref[Clock], reset: Ref[Reset])(using Arena, Context, Block, InstanceContext) =
    given ClockScope = ClockScope.posedge(clock)
    given ResetScope = ResetScope.asyncActiveHigh(reset)
    val meta = RegInit(true.B)
    val held = RegInit(true.B)
    meta := false.B
    held := meta
    val released = Wire(new Signal)
    released.value := held.asReset
    released.value

@generator
object DitDahA1DmiBridge extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1DmiBridgeIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1DmiBridge"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1DmiBridgeIO]]
    val tapReset = DebugReset.release(io.tck, io.reset)
    val systemReset = DebugReset.release(io.clock, io.reset)
    val acknowledged = Wire(Bool())
    val responsePayload = Wire(Bits(34))
    val (requestToggle, requestPayload) = ClockScope.posedge(io.tck) {
      ResetScope.asyncActiveHigh(tapReset) {
        val toggle = RegInit(false.B)
        val payload = RegInit(0.B(41))
        val busy = RegInit(false.B)
        val ackMeta = RegInit(false.B)
        val ackSync = RegInit(false.B)
        ackMeta := acknowledged
        ackSync := ackMeta
        io.upstream.request.ready := !busy & !tapReset.asBool
        io.upstream.response.valid := busy & (ackSync === toggle)
        io.upstream.response.bits.data := responsePayload.bits(33, 2).asUInt
        io.upstream.response.bits.status := responsePayload.bits(1, 0).asUInt
        when(io.upstream.request.valid & io.upstream.request.ready) {
          payload := io.upstream.request.bits.address.asBits ## io.upstream.request.bits.data.asBits ## io.upstream.request.bits.op.asBits
          toggle := !toggle
          busy := true.B
        }
        when(io.upstream.response.valid & io.upstream.response.ready) { busy := false.B }
        (toggle, payload)
      }
    }
    ClockScope.posedge(io.clock) {
      ResetScope.asyncActiveHigh(systemReset) {
        val requestMeta = RegInit(false.B)
        val requestSync = RegInit(false.B)
        val ack = RegInit(false.B)
        val response = RegInit(0.B(34))
        val waiting = RegInit(false.B)
        requestMeta := requestToggle
        requestSync := requestMeta
        acknowledged := ack
        responsePayload := response
        io.downstream.request.valid := (requestSync =/= ack) & !waiting
        io.downstream.request.bits.address := requestPayload.bits(40, 34).asUInt
        io.downstream.request.bits.data := requestPayload.bits(33, 2).asUInt
        io.downstream.request.bits.op := requestPayload.bits(1, 0).asUInt
        val accepted = io.downstream.request.valid & io.downstream.request.ready
        io.downstream.response.ready := waiting | accepted
        when(accepted) { waiting := true.B }
        when(io.downstream.response.valid & io.downstream.response.ready) {
          response := io.downstream.response.bits.data.asBits ## io.downstream.response.bits.status.asBits
          ack := requestSync
          waiting := false.B
        }
      }
    }

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
