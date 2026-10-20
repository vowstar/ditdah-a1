// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1UnitLayers(parameter: DitDahA1Parameter) extends LayerInterface(parameter):
  def layers = Seq.empty
class DitDahA1UnitProbe(parameter: DitDahA1Parameter) extends DVBundle[DitDahA1Parameter, DitDahA1UnitLayers](parameter)
class DitDahA1Layers(parameter: DitDahA1Parameter) extends LayerInterface(parameter):
  def layers = Seq(Layer("DV"))

class Decoupled[T <: Data](gen: T) extends Bundle:
  val ready = Flipped(Bool())
  val valid = Aligned(Bool())
  val bits = Aligned(gen)

class AxiAddress(parameter: DitDahA1Parameter) extends Bundle:
  val addr = Aligned(UInt(parameter.physicalAddressBits))
  val id = Aligned(UInt(parameter.axiIdBits))
  val len = Aligned(UInt(8))
  val size = Aligned(UInt(3))
  val burst = Aligned(UInt(2))
  val lock = Aligned(Bool())
  val cache = Aligned(UInt(4))
  val prot = Aligned(UInt(3))
  val qos = Aligned(UInt(4))
class AxiWrite(parameter: DitDahA1Parameter) extends Bundle:
  val data = Aligned(UInt(parameter.axiDataBits))
  val strb = Aligned(UInt(parameter.axiDataBits / 8))
  val last = Aligned(Bool())
class AxiRead(parameter: DitDahA1Parameter) extends Bundle:
  val data = Aligned(UInt(parameter.axiDataBits))
  val resp = Aligned(UInt(2))
  val id = Aligned(UInt(parameter.axiIdBits))
  val last = Aligned(Bool())
class AxiResponse(parameter: DitDahA1Parameter) extends Bundle:
  val resp = Aligned(UInt(2))
  val id = Aligned(UInt(parameter.axiIdBits))
class AxiBundle(parameter: DitDahA1Parameter) extends Bundle:
  val aw = Aligned(new Decoupled(new AxiAddress(parameter)))
  val w = Aligned(new Decoupled(new AxiWrite(parameter)))
  val b = Flipped(new Decoupled(new AxiResponse(parameter)))
  val ar = Aligned(new Decoupled(new AxiAddress(parameter)))
  val r = Flipped(new Decoupled(new AxiRead(parameter)))

class MemoryRequest extends Bundle:
  val address = Aligned(UInt(64))
  val data = Aligned(UInt(64))
  val size = Aligned(UInt(3))
  val mask = Aligned(UInt(8))
  val tag = Aligned(UInt(8))
  val write = Aligned(Bool())
  val fetch = Aligned(Bool())
  val privileged = Aligned(Bool())
  val atomic = Aligned(Bool())
  val atomicOperation = Aligned(UInt(5))
  val scEligible = Aligned(Bool())
class MemoryResponse(dataBits: Int = 64, countBits: Int = 0) extends Bundle:
  val data = Aligned(UInt(dataBits))
  val fault = Aligned(Bool())
  val tag = Aligned(UInt(8))
  val last = Aligned(Bool())
  val count = Option.when(countBits > 0)(Aligned(UInt(countBits)))
class MemoryPort extends Bundle:
  val request = Aligned(new Decoupled(new MemoryRequest))
  val response = Flipped(new Decoupled(new MemoryResponse))
class InstructionCachePort(parameter: DitDahA1Parameter) extends Bundle:
  val request = Aligned(new Decoupled(new MemoryRequest))
  val response = Flipped(new Decoupled(new MemoryResponse(math.max(64, 32 * parameter.fetchWords),
    if parameter.fetchWords > 1 then parameter.fetchCountBits else 0)))

class TranslationState extends Bundle:
  val satp = Aligned(UInt(64))
  val sum = Aligned(Bool())
  val mxr = Aligned(Bool())
class TranslationRequest extends Bundle:
  val address = Aligned(UInt(64))
  val privilege = Aligned(UInt(2))
  val fetch = Aligned(Bool())
  val write = Aligned(Bool())
class TranslationResponse extends Bundle:
  val address = Aligned(UInt(64))
  val fault = Aligned(Bool())
  val cause = Aligned(UInt(64))
class TranslationPort extends Bundle:
  val request = Aligned(new Decoupled(new TranslationRequest))
  val response = Flipped(new Decoupled(new TranslationResponse))

class PmpState(parameter: DitDahA1Parameter) extends Bundle:
  val config = Aligned(UInt(parameter.pmpEntries * 8))
  val address = Aligned(UInt(parameter.pmpEntries * (parameter.physicalAddressBits - 2)))

class FetchRequest extends Bundle:
  val pc = Aligned(UInt(64))
  val tag = Aligned(UInt(8))
class FetchPacket(words: Int = 1) extends Bundle:
  val pc = Aligned(UInt(64))
  val tag = Aligned(UInt(8))
  val instruction = Aligned(UInt(32))
  val length = Aligned(UInt(3))
  val fault = Aligned(Bool())
  val cause = Aligned(UInt(64))
  val tval = Aligned(UInt(64))
  val count = Option.when(words > 1)(Aligned(UInt(32 - Integer.numberOfLeadingZeros(words))))
  val following = Option.when(words > 1)(Aligned(Vec(words - 1, UInt(32))))
class InstructionGroup(width: Int) extends Bundle:
  val count = Aligned(UInt(32 - Integer.numberOfLeadingZeros(width)))
  val packets = Aligned(Vec(width, new FetchPacket))
class DecodedPacket extends Bundle:
  val instruction = Aligned(new FetchPacket)
  val operation = Aligned(UInt(DitDahA1Isa.operationBits))
  val rs1 = Aligned(UInt(5))
  val rs2 = Aligned(UInt(5))
  val usesRs1 = Aligned(Bool())
  val usesRs2 = Aligned(Bool())
  val writesRd = Aligned(Bool())
  val serializing = Aligned(Bool())
  val rd = Aligned(UInt(5))
  val immediate = Aligned(UInt(64))
class IssuedPacket extends Bundle:
  val decoded = Aligned(new DecodedPacket)
  val operand1 = Aligned(UInt(64))
  val operand2 = Aligned(UInt(64))
class ResultPacket extends Bundle:
  val instruction = Aligned(new FetchPacket)
  val rd = Aligned(UInt(5))
  val rdWrite = Aligned(Bool())
  val value = Aligned(UInt(64))
  val nextPc = Aligned(UInt(64))
  val load = Aligned(Bool())
  val store = Aligned(Bool())
  val atomic = Aligned(Bool())
  val memorySize = Aligned(UInt(3))
  val unsignedLoad = Aligned(Bool())
  val address = Aligned(UInt(64))
  val storeData = Aligned(UInt(64))
  val csrWrite = Aligned(Bool())
  val csrAddress = Aligned(UInt(12))
  val csrData = Aligned(UInt(64))
  val mret = Aligned(Bool())
  val sret = Aligned(Bool())
  val fenceI = Aligned(Bool())
  val sfenceVma = Aligned(Bool())
  val wfi = Aligned(Bool())
class StatusBundle extends Bundle:
  val trap = Aligned(Bool())
  val busy = Aligned(Bool())
  val sleep = Aligned(Bool())
class InterruptBundle extends Bundle:
  val software = Aligned(Bool())
  val timer = Aligned(Bool())
  val external = Aligned(Bool())
class DitDahA1IO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val timeTick = Option.when(parameter.localInterruptBase.nonEmpty)(Flipped(Bool()))
  val interrupts = Option.when(parameter.enableInterrupts)(Flipped(Vec(parameter.hartCount, new InterruptBundle)))
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val axi = Aligned(new AxiBundle(parameter))
  val status = Aligned(new StatusBundle)
class DitDahA1SystemProbe(parameter: DitDahA1Parameter) extends DVBundle[DitDahA1Parameter, DitDahA1Layers](parameter)
class DitDahA1Probe(parameter: DitDahA1Parameter) extends DVBundle[DitDahA1Parameter, DitDahA1Layers](parameter):
  private def dv = layers("DV")
  val valid = ProbeRead(Bool(), dv)
  val count = ProbeRead(UInt(parameter.issueCountBits), dv)
  val issueCount = ProbeRead(UInt(parameter.issueCountBits), dv)
  val order = ProbeRead(UInt(64), dv)
  val pc = ProbeRead(UInt(parameter.issueWidth * 64), dv)
  val instruction = ProbeRead(UInt(parameter.issueWidth * 32), dv)
  val nextPc = ProbeRead(UInt(parameter.issueWidth * 64), dv)
  val rd = ProbeRead(UInt(parameter.issueWidth * 5), dv)
  val rdWrite = ProbeRead(UInt(parameter.issueWidth * 1), dv)
  val value = ProbeRead(UInt(parameter.issueWidth * 64), dv)
  val trap = ProbeRead(UInt(parameter.issueWidth * 1), dv)
  val cause = ProbeRead(UInt(parameter.issueWidth * 64), dv)
  val tval = ProbeRead(UInt(parameter.issueWidth * 64), dv)
  val pipelineOccupancy = ProbeRead(UInt(parameter.pipelineOccupancyBits), dv)
  val pipelineStall = ProbeRead(Bool(), dv)

class DitDahA1CoreIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val hartId = Flipped(UInt(4))
  val interrupts = Option.when(parameter.enableInterrupts)(Flipped(new InterruptBundle))
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val instruction = Aligned(new MemoryPort)
  val data = Aligned(new MemoryPort)
  val status = Aligned(new StatusBundle)

class DitDahA1FrontendIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val translation = Option.when(parameter.enableTranslation)(Aligned(new TranslationPort))
  val privilege = Flipped(UInt(2))
  val pmp = Option.when(parameter.pmpEntries != 0)(Flipped(new PmpState(parameter)))
  val invalidate = Option.when(parameter.iCacheBytes != 0)(Flipped(Bool()))
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val redirect = Flipped(Bool())
  val halt = Flipped(Bool())
  val redirectPc = Flipped(UInt(64))
  val output = Aligned(new Decoupled(new InstructionGroup(parameter.issueWidth)))
  val memory = Aligned(new MemoryPort)

class DitDahA1MemoryFabricIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val invalidate = Option.when(parameter.dCacheBytes != 0)(Aligned(Vec(parameter.hartCount, new Decoupled(UInt(64)))))
  val timeTick = Option.when(parameter.localInterruptBase.nonEmpty)(Flipped(Bool()))
  val localInterrupts = Option.when(parameter.localInterruptBase.nonEmpty)(Aligned(Vec(parameter.hartCount, new InterruptBundle)))
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val instruction = Flipped(Vec(parameter.hartCount, new MemoryPort))
  val data = Flipped(Vec(parameter.hartCount, new MemoryPort))
  val axi = Aligned(new AxiBundle(parameter))

class DitDahA1BackendIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val translation = Option.when(parameter.enableTranslation)(Aligned(new TranslationPort))
  val translationState = Option.when(parameter.enableTranslation)(Aligned(new TranslationState))
  val invalidateTranslation = Option.when(parameter.enableTranslation && parameter.tlbEntries != 0)(Aligned(Bool()))
  val privilege = Aligned(UInt(2))
  val hartId = Flipped(UInt(4))
  val interrupts = Option.when(parameter.enableInterrupts)(Flipped(new InterruptBundle))
  val pmp = Option.when(parameter.pmpEntries != 0)(Aligned(new PmpState(parameter)))
  val invalidate = Option.when(parameter.iCacheBytes != 0)(Aligned(Bool()))
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val instruction = Flipped(new Decoupled(new InstructionGroup(parameter.issueWidth)))
  val redirect = Aligned(Bool())
  val redirectPc = Aligned(UInt(64))
  val data = Aligned(new MemoryPort)
  val status = Aligned(new StatusBundle)
