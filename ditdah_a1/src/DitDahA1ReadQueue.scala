// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1ReadQueueIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val ports = Flipped(Vec(2 * parameter.hartCount, new MemoryPort))
  val ar = Aligned(new Decoupled(new AxiAddress(parameter)))
  val r = Flipped(new Decoupled(new AxiRead(parameter)))
  val empty = Aligned(Bool())

@generator
object DitDahA1ReadQueue extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1ReadQueueIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1ReadQueue"
  def architecture(parameter: DitDahA1Parameter) =
    require(parameter.hartCount > 1, "Concurrent reads require multiple harts")
    val io = summon[Interface[DitDahA1ReadQueueIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val count = 2 * parameter.hartCount
    val ownerBits = 32 - Integer.numberOfLeadingZeros(count - 1)
    val state = Seq.fill(2)(RegInit(0.U(3)))
    val owner = Seq.fill(2)(Reg(UInt(ownerBits)))
    val request = Seq.fill(2)(Reg(new MemoryRequest))
    val data = Seq.fill(2)(Reg(UInt(64)))
    val fault = Seq.fill(2)(RegInit(false.B))
    val next = RegInit(0.U(ownerBits))
    val free = state.map(_ === 0.U(3))
    val waiting = state.map(_ === 3.U(3))
    val hart = owner.map(_.asBits.bits(ownerBits - 1, 1).asUInt)
    val available = (0 until count).map { i =>
      !(0 until 2).map(n => !free(n) & (hart(n) === (i / 2).U(parameter.axiIdBits))).reduce(_ | _)
    }
    val valid = (0 until count).map(i => io.ports(i).request.valid & available(i))
    val selected = DitDahA1MemoryArbiter.select(valid, next)
    val captured = Wire(new MemoryRequest)
    captured :<= io.ports(0).request.bits
    for i <- 1 until count do
      when(selected === i.U(ownerBits)) { captured :<= io.ports(i).request.bits }
    val accept = valid.reduce(_ | _) & free.reduce(_ | _)
    val slot = !free(0)
    io.empty := free.reduce(_ & _)
    for i <- 0 until count do
      val port = io.ports(i)
      port.request.ready := available(i) & free.reduce(_ | _) & (selected === i.U(ownerBits))
      port.response.valid := false.B
      port.response.bits.data := 0.U(64)
      port.response.bits.fault := false.B
      port.response.bits.tag := 0.U(8)
      port.response.bits.last := true.B
      for n <- 0 until 2 do
        when((state(n) === 4.U(3)) & (owner(n) === i.U(ownerBits))) {
          port.response.valid := true.B
          port.response.bits.data := data(n)
          port.response.bits.fault := fault(n)
          port.response.bits.tag := request(n).tag
          when(port.response.ready) { state(n) := 0.U(3) }
        }
    val addressActive = state.map(_ === 2.U(3)).reduce(_ | _)
    val addressSlot = state(1) === 2.U(3)
    val addressRequest = Wire(new MemoryRequest)
    addressRequest :<= request(0)
    when(addressSlot) { addressRequest :<= request(1) }
    DitDahA1Axi.address(parameter, io.ar.bits, addressRequest, addressSlot.?(hart(1), hart(0)))
    io.ar.valid := addressActive
    val matches = (0 until 2).map(n => waiting(n) & (io.r.bits.id === hart(n)))
    val responseSlot = matches(1) | (!matches.reduce(_ | _) & !waiting(0))
    io.r.ready := waiting.reduce(_ | _)
    for n <- 0 until 2 do
      val ordinary = parameter.memoryRegions.filter(!_.device).foldLeft[Referable[Bool]](false.B) { (allowed, region) =>
        allowed | ((request(n).address >= region.base.U(64)) & (request(n).address < (region.base + region.size).U(64)))
      }
      val permitted = !request(n).write & !request(n).atomic & (request(n).size <= 3.U(3)) &
        ordinary & DitDahA1Memory.permitted(parameter, request(n))
      when((state(n) === 1.U(3)) & !permitted) {
        data(n) := 0.U(64)
        fault(n) := true.B
        state(n) := 4.U(3)
      }
      when(!addressActive & (state(n) === 1.U(3)) & permitted &
        (if n == 0 then true.B else state(0) =/= 1.U(3))) { state(n) := 2.U(3) }
      when(io.ar.valid & io.ar.ready & (addressSlot === (n == 1).B)) { state(n) := 3.U(3) }
      val laneBits = Integer.numberOfTrailingZeros(parameter.axiDataBits / 8)
      val shift = (request(n).address.asBits.bits(laneBits - 1, 0) ## 0.B(3)).asUInt
      when(io.r.valid & io.r.ready & (responseSlot === (n == 1).B)) {
        data(n) := DitDahA1Axi.readData(request(n).size, io.r.bits.data, shift)
        fault(n) := fault(n) | (io.r.bits.resp =/= 0.U(2)) | !matches(n) | !io.r.bits.last
        when(io.r.bits.last) { state(n) := 4.U(3) }
      }
      when(accept & (slot === (n == 1).B)) {
        request(n) :<= captured
        owner(n) := selected
        fault(n) := false.B
        state(n) := 1.U(3)
      }
    when(accept) {
      next := (selected === (count - 1).U(ownerBits)).?(0.U(ownerBits),
        (selected + 1.U(ownerBits)).asBits.bits(ownerBits - 1, 0).asUInt)
    }
