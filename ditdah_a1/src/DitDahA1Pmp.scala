// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1PmpIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val state = Flipped(new PmpState(parameter))
  val address = Flipped(UInt(64))
  val size = Flipped(UInt(3))
  val write = Flipped(Bool())
  val fetch = Flipped(Bool())
  val atomic = Flipped(Bool())
  val allowed = Aligned(Bool())

@generator
object DitDahA1Pmp extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1PmpIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Pmp"
  def architecture(parameter: DitDahA1Parameter) =
    parameter.validateProtection()
    val io = summon[Interface[DitDahA1PmpIO]]
    val width = parameter.physicalAddressBits - 2
    val start = (0.B(1) ## io.address.asBits).asUInt
    val end = Wire(UInt(65))
    end := start
    for size <- 0 to 3 do
      when(io.size === size.U(3)) { end := (start + (1 << size).U(65)).asBits.bits(64, 0).asUInt }
    val addresses = (0 until parameter.pmpEntries).map { index =>
      (0.B(64 - width) ## io.state.address.asBits.bits((index + 1) * width - 1, index * width)).asUInt
    }
    val points = addresses.map(encoded => (encoded.asBits.bits(61, 0) ## 0.B(2)).asUInt)
    val allowed = Wire(Bool())
    allowed := true.B
    for index <- (0 until parameter.pmpEntries).reverse do
      val config = io.state.config.asBits.bits(index * 8 + 7, index * 8)
      val mode = config.bits(4, 3).asUInt
      val encoded = addresses(index)
      val point = points(index)
      val mask = ((encoded.asBits ^ (encoded + 1.U(64)).asBits.bits(63, 0)).bits(61, 0) ## 3.B(2)).asUInt
      val napotBase = (point.asBits & (mask.asBits ^ ((BigInt(1) << 64) - 1).B(64))).asUInt
      val base = Wire(UInt(65))
      val limit = Wire(UInt(65))
      base := 0.U(65)
      limit := 0.U(65)
      when(mode === 1.U(2)) {
        if index > 0 then base := points(index - 1)
        limit := point
      }
      when(mode === 2.U(2)) { base := point; limit := (point + 4.U(64)).asBits.bits(64, 0).asUInt }
      when(mode === 3.U(2)) {
        base := napotBase
        limit := (napotBase + mask + 1.U(65)).asBits.bits(64, 0).asUInt
      }
      val permission = io.atomic.?(config.bit(0) & config.bit(1), io.fetch.?(config.bit(2), io.write.?(config.bit(1), config.bit(0))))
      when((mode =/= 0.U(2)) & (limit > base) & (start < limit) & (end > base)) {
        allowed := (start >= base) & (end <= limit) & (!config.bit(7) | permission)
      }
    io.allowed := allowed & (io.size <= 3.U(3)) & (end <= (BigInt(1) << parameter.physicalAddressBits).U(65))
