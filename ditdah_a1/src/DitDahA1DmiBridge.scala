// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

class DitDahA1DmiBridgeIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val tck = Flipped(Clock())
  val reset = Flipped(Reset())
  val upstream = Flipped(new DmiPort)
  val downstream = Aligned(new DmiPort)

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
