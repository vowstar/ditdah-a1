// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

object DitDahA1ParameterCheck:
  private def rejects(body: => Unit): Unit =
    var rejected = false
    try body
    catch case _: IllegalArgumentException => rejected = true
    assert(rejected, "Invalid configuration was accepted")

  def run(): Unit =
    val baseline = DitDahA1Parameter()
    val highAddress = baseline.copy(resetAddress = (BigInt(1) << 40) + 2)
    val encoded = upickle.default.write(highAddress)
    assert(upickle.default.read[DitDahA1Parameter](encoded) == highAddress)
    assert(DitDahA1Config.parameter(ujson.read(encoded)) == highAddress)
    assert(DitDahA1Config.parameter(DitDahA1Config.document(highAddress)) == highAddress)
    assert(DitDahA1Config.document(highAddress)("target")("xlen").num == 64)
    assert(baseline.copy(hartCount = 8).productName == "DitDah-A1")
    assert(DitDahA1Config.document(baseline)("target")("isa").str == "RV64GCB")
    assert(baseline.copy(l2CacheBytes = 0).l2CacheBytes == 0)
    assert(baseline.copy(virtualAddressBits = 48).virtualAddressBits == 48)
    rejects { baseline.copy(resetAddress = -1); () }
    rejects { baseline.copy(resetAddress = 1); () }
    rejects { baseline.copy(resetAddress = BigInt(1) << 56); () }
    rejects { baseline.copy(virtualAddressBits = 32); () }
    rejects { baseline.copy(hartCount = 0); () }
    rejects { baseline.copy(hartCount = 9); () }
    rejects { baseline.copy(iCacheBytes = 12288); () }
    rejects { baseline.copy(l2CacheBytes = 65536); () }
    rejects { baseline.copy(axiDataBits = 96); () }
    rejects { baseline.copy(pmpEntries = 65); () }
    rejects { DitDahA1Config.parameter(ujson.Obj("unused" -> 1)); () }
    println("Configuration contracts passed")
