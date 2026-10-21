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
    for count <- 1 to 16 do
      val selected = baseline.copy(hartCount = count)
      assert(DitDahA1Config.parameter(DitDahA1Config.document(selected)) == selected)
      assert(selected.axiIdBits == (if count <= 2 then 1 else if count <= 4 then 2 else if count <= 8 then 3 else 4))
    assert(DitDahA1Config.document(baseline)("target")("maxHartCount").num == 16)
    assert(!DitDahA1Config.document(baseline.copy(pmpEntries = 64))("implementation").obj.contains("pmpEntries"))
    assert(DitDahA1Config.document(baseline)("target")("isa").str == "RV64GCB")
    assert(baseline.copy(l2CacheBytes = 0).l2CacheBytes == 0)
    assert(baseline.copy(virtualAddressBits = 48).virtualAddressBits == 48)
    rejects { baseline.copy(resetVector = -1); () }
    rejects { baseline.copy(resetVector = 1); () }
    rejects { baseline.copy(resetVector = BigInt(1) << 56); () }
    rejects { baseline.copy(virtualAddressBits = 32); () }
    rejects { baseline.copy(hartCount = 0); () }
    rejects { baseline.copy(hartCount = 17); () }
    rejects { baseline.copy(iCacheBytes = 12288); () }
    rejects { baseline.copy(l2CacheBytes = 65536); () }
    rejects { baseline.copy(axiDataBits = 96); () }
    rejects { baseline.copy(pmpEntries = 65); () }
    rejects { DitDahA1Config.parameter(ujson.Obj("unused" -> 1)); () }
    val rtl = DitDahA1Parameter.uncached
    rejects { rtl.copy(enableBurstRefill = true).validateFrontend() }
    rtl.copy(enableBurstRefill = true).validateBackend()
    rtl.copy(enableBurstRefill = true).validateFabric()
    val burst = rtl.copy(iCacheBytes = 8192, enableBurstRefill = true)
    burst.validateRtl()
    assert(DitDahA1Config.parameter(DitDahA1Config.document(burst)) == burst)
    rejects { rtl.copy(dCacheRefillBytes = 16); () }
    rejects { rtl.copy(dCacheRefillBytes = 64).validateRtl() }
    rtl.copy(dCacheRefillBytes = 64).validateFrontend()
    rtl.copy(dCacheRefillBytes = 64).validateBackend()
    rtl.copy(dCacheRefillBytes = 64).validateFabric()
    for bytes <- Seq(8, 64); instruction <- Seq(false, true) do
      val data = rtl.copy(dCacheBytes = 8192, dCacheRefillBytes = bytes,
        iCacheBytes = if instruction then 8192 else 0, enableBurstRefill = instruction)
      data.validateRtl()
      assert(DitDahA1Config.parameter(DitDahA1Config.document(data)) == data)
      assert(DitDahA1Config.document(data)("implementation")("dCacheRefillBytes").num == bytes)
    for count <- 1 to 16 do rtl.copy(hartCount = count).validateRtl()
    assert(!rtl.enableInterrupts)
    assert(!rtl.enableUserMode)
    val user = rtl.copy(enableUserMode = true)
    user.validateRtl()
    assert(DitDahA1Config.parameter(DitDahA1Config.document(user)) == user)
    assert(DitDahA1Config.document(user)("implementation")("privilege").str == "MU")
    val supervisor = user.copy(enableSupervisorMode = true, enableInterrupts = true)
    supervisor.validateRtl()
    assert(DitDahA1Config.parameter(DitDahA1Config.document(supervisor)) == supervisor)
    assert(DitDahA1Config.document(supervisor)("implementation")("privilege").str == "MSU")
    assert(DitDahA1Config.document(supervisor)("implementation")("instructions").arr.exists(_.str == "sret"))
    assert(!DitDahA1Config.document(user)("implementation")("instructions").arr.exists(_.str == "sret"))
    rejects { supervisor.copy(enableUserMode = false).validateRtl() }
    rejects { supervisor.copy(enableInterrupts = false).validateRtl() }
    val paged = supervisor.copy(virtualAddressBits = 39)
    paged.validateRtl()
    assert(paged.enableTranslation && !supervisor.enableTranslation)
    assert(DitDahA1Config.parameter(DitDahA1Config.document(paged)) == paged)
    assert(DitDahA1Config.document(paged)("implementation")("translation").str == "Sv39/Svade")
    assert(DitDahA1Config.document(paged)("implementation")("instructions").arr.exists(_.str == "sfence.vma"))
    for entries <- Seq(0, 2, 4) do
      val cached = paged.copy(tlbEntries = entries)
      cached.validateCore()
      assert(DitDahA1Config.parameter(DitDahA1Config.document(cached)) == cached)
      assert(DitDahA1Config.document(cached)("implementation")("tlbEntries").num == entries)
    rejects { paged.copy(tlbEntries = 1); () }
    rejects { paged.copy(tlbEntries = 8); () }
    rejects { supervisor.copy(tlbEntries = 2).validateCore() }
    supervisor.copy(tlbEntries = 2).validateFrontend()
    supervisor.copy(tlbEntries = 2).validateBackend()
    supervisor.copy(tlbEntries = 2).validateFabric()
    rejects { paged.copy(enableSupervisorMode = false).validateRtl() }
    rejects { paged.copy(enableSupervisorMode = false).validateCore() }
    rejects { paged.copy(enableSupervisorMode = false).validateFrontend() }
    rejects { paged.copy(enableSupervisorMode = false).validateBackend() }
    rejects { paged.copy(virtualAddressBits = 48).validateRtl() }
    rejects { paged.copy(virtualAddressBits = 48).validateCore() }
    val device = MemoryRegion(base = 0x2000000, size = 65536, executable = false, device = true)
    val platform = rtl.copy(enableInterrupts = true, localInterruptBase = Some(device.base), memoryRegions = rtl.memoryRegions :+ device)
    platform.validateRtl()
    assert(DitDahA1Config.parameter(DitDahA1Config.document(platform)) == platform)
    rejects { platform.copy(enableInterrupts = false).validateFabric() }
    rejects { platform.copy(localInterruptBase = Some(device.base + 4)).validateFabric() }
    rejects { platform.copy(localInterruptBase = Some(-65536)).validateFabric() }
    rejects { platform.copy(localInterruptBase = Some(BigInt(1) << 56)).validateFabric() }
    rejects { platform.copy(memoryRegions = rtl.memoryRegions).validateFabric() }
    rejects { platform.copy(memoryRegions = rtl.memoryRegions :+ device.copy(readable = false)).validateFabric() }
    rejects { platform.copy(memoryRegions = rtl.memoryRegions :+ device.copy(writable = false)).validateFabric() }
    rejects { platform.copy(memoryRegions = rtl.memoryRegions :+ device.copy(size = 32768)).validateFabric() }
    platform.copy(localInterruptBase = Some(-1)).validateCore()
    for entries <- Seq(0, 16) do
      val enabled = rtl.copy(enableInterrupts = true, pmpEntries = entries)
      enabled.validateRtl()
      assert(DitDahA1Config.parameter(DitDahA1Config.document(enabled)) == enabled)
    rtl.copy(axiDataBits = 64).validateRtl()
    for width <- 1 to 3 do
      val cached = rtl.copy(issueWidth = width, iCacheBytes = 8192)
      cached.validateFrontend()
      cached.validateBackend()
      cached.validateCore()
      cached.validateRtl()
      val predicted = cached.copy(enableBranchPrediction = true)
      predicted.validateRtl()
      assert(DitDahA1Config.parameter(DitDahA1Config.document(predicted)) == predicted)
      assert(cached.fetchWords == Seq(1, 2, 4)(width - 1))
      assert((1 << cached.fetchCountBits) > cached.fetchWords)
      assert(cached.copy(iCacheBytes = 0).fetchWords == 1)
    rejects { rtl.copy(issueWidth = 0); () }
    rejects { rtl.copy(issueWidth = 4); () }
    rejects { rtl.copy(resetVector = 2).validateFrontend() }
    rtl.copy(resetVector = 2, axiDataBits = 512, iCacheBytes = 8192).validateBackend()
    rtl.copy(axiDataBits = 256).validateCore()
    rtl.copy(iCacheBytes = 8192).validateCore()
    rejects { rtl.copy(resetVector = 2).validateCore() }
    rejects { baseline.validateRtl() }
    rejects { rtl.copy(resetVector = 2).validateRtl() }
    for width <- Seq(64, 128, 256, 512) do rtl.copy(axiDataBits = width).validateRtl()
    rejects { rtl.copy(memoryRegions = Seq(MemoryRegion(), MemoryRegion())).validateRtl() }
    rejects { MemoryRegion(device = true); () }
    assert(!MemoryRegion().atomic)
    val atomic = rtl.copy(memoryRegions = Seq(MemoryRegion(atomic = true)))
    assert(DitDahA1Config.parameter(DitDahA1Config.document(atomic)) == atomic)
    rejects { MemoryRegion(atomic = true, readable = false); () }
    rejects { MemoryRegion(atomic = true, writable = false); () }
    rejects { MemoryRegion(atomic = true, device = true, executable = false); () }
    assert(DitDahA1Config.parameter(ujson.Obj("resetAddress" -> "4")).resetVector == 4)
    rejects { DitDahA1Config.parameter(ujson.Obj("resetAddress" -> 4, "resetVector" -> 8)); () }
    assert(DitDahA1Config.document(rtl)("parameters")("resetVector").str == "0")
    assert(DitDahA1Config.document(rtl)("parameters")("memoryRegions")(0)("readable").bool)
    assert(DitDahA1Config.document(rtl)("implementation")("maxInflight").num == 7)
    assert(DitDahA1Config.document(rtl.copy(iCacheBytes = 8192))("implementation")("maxInflight").num == 8)
    assert(DitDahA1Config.document(rtl)("implementation")("pipelineStages").num == 8)
    rejects { DitDahA1Config.parameter(ujson.Obj("memoryRegions" -> ujson.Arr(ujson.Obj("execute" -> false)))); () }
    rejects { rtl.copy(virtualAddressBits = 39).validateRtl() }
    rtl.copy(pmpEntries = 16).validateRtl()
    rejects { rtl.copy(pmpEntries = 1); () }
    rejects { rtl.copy(pmpEntries = 64).validateRtl() }
    rejects { rtl.copy(pmpEntries = 64).validateFrontend() }
    rejects { rtl.copy(pmpEntries = 64).validateBackend() }
    for bytes <- Seq(0, 8192, 16384, 32768, 65536) do rtl.copy(iCacheBytes = bytes).validateRtl()
    rtl.copy(dCacheBytes = 8192).validateRtl()
    rejects { rtl.copy(dCacheBytes = 16384).validateRtl() }
    rejects { MemoryRegion(device = true, executable = false, dataCacheable = true); () }
    assert(DitDahA1Config.parameter(DitDahA1Config.document(rtl.copy(memoryRegions = Seq(MemoryRegion(dataCacheable = true))))).memoryRegions.head.dataCacheable)
    rejects { rtl.copy(l2CacheBytes = 131072).validateRtl() }
    rejects { rtl.copy(memoryRegions = Seq.empty).validateRtl() }
    rejects { rtl.copy(memoryRegions = Seq(MemoryRegion(executable = false))).validateRtl() }
    rejects { rtl.copy(memoryRegions = Seq(MemoryRegion(base = (BigInt(1) << 56) - 8, size = 16))); () }
    println("Configuration contracts passed")
