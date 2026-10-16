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
    val highAddress = baseline.copy(resetVector = (BigInt(1) << 40) + 2)
    val encoded = upickle.default.write(highAddress)
    assert(upickle.default.read[DitDahA1Parameter](encoded) == highAddress)
    assert(DitDahA1Config.parameter(ujson.read(encoded)) == highAddress)
    assert(DitDahA1Config.parameter(DitDahA1Config.document(highAddress)) == highAddress)
    assert(DitDahA1Config.document(highAddress)("target")("xlen").num == 64)
    assert(baseline.copy(hartCount = 8).productName == "DitDah-A1")
    assert(DitDahA1Config.document(baseline)("target")("isa").str == "RV64GCB")
    assert(baseline.copy(l2CacheBytes = 0).l2CacheBytes == 0)
    assert(baseline.copy(virtualAddressBits = 48).virtualAddressBits == 48)
    rejects { baseline.copy(resetVector = -1); () }
    rejects { baseline.copy(resetVector = 1); () }
    rejects { baseline.copy(resetVector = BigInt(1) << 56); () }
    rejects { baseline.copy(virtualAddressBits = 32); () }
    rejects { baseline.copy(hartCount = 0); () }
    rejects { baseline.copy(hartCount = 9); () }
    rejects { baseline.copy(iCacheBytes = 12288); () }
    rejects { baseline.copy(l2CacheBytes = 65536); () }
    rejects { baseline.copy(axiDataBits = 96); () }
    rejects { baseline.copy(pmpEntries = 65); () }
    rejects { DitDahA1Config.parameter(ujson.Obj("unused" -> 1)); () }
    val rtl = DitDahA1Parameter.uncached
    rtl.validateRtl()
    rtl.copy(axiDataBits = 64).validateRtl()
    rtl.copy(issueWidth = 2).validateFrontend()
    rejects { rtl.copy(resetVector = 2).validateFrontend() }
    rtl.copy(axiDataBits = 256).validateCore()
    rtl.copy(iCacheBytes = 8192).validateCore()
    rejects { rtl.copy(issueWidth = 2).validateCore() }
    rejects { rtl.copy(resetVector = 2).validateCore() }
    rejects { baseline.validateRtl() }
    rejects { rtl.copy(issueWidth = 2).validateRtl() }
    rejects { rtl.copy(resetVector = 2).validateRtl() }
    rejects { rtl.copy(axiDataBits = 256).validateRtl() }
    rejects { rtl.copy(memoryRegions = Seq(MemoryRegion(), MemoryRegion())).validateRtl() }
    rejects { MemoryRegion(device = true); () }
    assert(DitDahA1Config.parameter(ujson.Obj("resetAddress" -> "4")).resetVector == 4)
    rejects { DitDahA1Config.parameter(ujson.Obj("resetAddress" -> 4, "resetVector" -> 8)); () }
    assert(DitDahA1Config.document(rtl)("parameters")("resetVector").str == "0")
    assert(DitDahA1Config.document(rtl)("parameters")("memoryRegions")(0)("readable").bool)
    assert(DitDahA1Config.document(rtl)("implementation")("maxInflight").num == 5)
    rejects { DitDahA1Config.parameter(ujson.Obj("memoryRegions" -> ujson.Arr(ujson.Obj("execute" -> false)))); () }
    rejects { rtl.copy(hartCount = 2).validateRtl() }
    rejects { rtl.copy(virtualAddressBits = 39).validateRtl() }
    rejects { rtl.copy(pmpEntries = 1).validateRtl() }
    rejects { rtl.copy(iCacheBytes = 8192).validateRtl() }
    rejects { rtl.copy(memoryRegions = Seq.empty).validateRtl() }
    rejects { rtl.copy(memoryRegions = Seq(MemoryRegion(executable = false))).validateRtl() }
    rejects { rtl.copy(memoryRegions = Seq(MemoryRegion(base = (BigInt(1) << 56) - 8, size = 16))); () }
    println("Configuration contracts passed")
