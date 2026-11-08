// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.Parameter

@upickle.implicits.serializeDefaults(true)
case class DitDahA1Parameter(
  resetVector: BigInt = BigInt(0),
  hartCount: Int = 1,
  fabricReadSlots: Option[Int] = None,
  physicalAddressBits: Int = 56,
  virtualAddressBits: Int = 39,
  tlbEntries: Int = 0,
  iTlbEntries: Int = 0,
  dTlbEntries: Int = 0,
  asidBits: Int = 0,
  iCacheBytes: Int = 32768,
  dCacheBytes: Int = 32768,
  dCacheWays: Int = 1,
  dCacheRefillBytes: Int = 8,
  dCacheWriteback: Boolean = false,
  l2CacheBytes: Int = 262144,
  axiDataBits: Int = 128,
  pmpEntries: Int = 16,
  issueWidth: Int = 1,
  loadQueueEntries: Int = 1,
  enableM: Boolean = true,
  enableA: Boolean = true,
  enableMisaligned: Boolean = false,
  enableC: Boolean = false,
  floatingPointBits: Int = 0,
  enableZba: Boolean = false,
  enableZbb: Boolean = false,
  enableZbs: Boolean = false,
  enableZicond: Boolean = false,
  enableZimop: Boolean = false,
  enableZcb: Boolean = false,
  enableZcmop: Boolean = false,
  enableZfa: Boolean = false,
  enableZfhmin: Boolean = false,
  enableCounters: Boolean = false,
  hpmCounters: Int = 0,
  enableSstc: Boolean = false,
  enableInterrupts: Boolean = false,
  enableUserMode: Boolean = false,
  enableSupervisorMode: Boolean = false,
  enableBurstRefill: Boolean = false,
  enableBranchPrediction: Boolean = false,
  branchPredictorEntries: Int = 0,
  enableTrace: Boolean = false,
  enableJtag: Boolean = false,
  jtagIdcode: Option[Long] = None,
  debugBase: Option[BigInt] = None,
  localInterruptBase: Option[BigInt] = None,
  memoryRegions: Seq[MemoryRegion] = Seq(MemoryRegion())
) extends Parameter:
  private def powerOfTwo(value: Int): Boolean = value > 0 && (value & (value - 1)) == 0

  require(hartCount >= 1 && hartCount <= 16, "hartCount must be between 1 and 16")
  require(jtagIdcode.forall(id => id > 0 && id <= 0xffffffffL && (id & 1) == 1), "JTAG IDCODE must be an odd unsigned 32-bit value")
  debugBase.foreach { base =>
    require(base >= 0 && (base & 4095) == 0 && base + 4096 <= (BigInt(1) << physicalAddressBits), "Debug window must be a physical aligned page")
    require(memoryRegions.forall(r => base + 4096 <= r.base || base >= r.base + r.size), "Debug window must not overlap ordinary memory")
  }
  require(fabricReadSlots.forall(n => n >= 0 && n <= 4), "fabricReadSlots must be between zero and four")
  require(physicalAddressBits >= 32 && physicalAddressBits <= 56, "physicalAddressBits must be between 32 and 56")
  require(Set(0, 39, 48).contains(virtualAddressBits), "virtualAddressBits must select Bare, Sv39 or Sv48")
  require(Set(0, 2, 4).contains(tlbEntries), "tlbEntries must be zero, two or four")
  require(Set(0, 2, 4).contains(iTlbEntries), "iTlbEntries must be zero, two or four")
  require(Set(0, 2, 4).contains(dTlbEntries), "dTlbEntries must be zero, two or four")
  require(Set(0, 4).contains(asidBits), "asidBits must be zero or four")
  require(resetVector >= 0 && resetVector < (BigInt(1) << physicalAddressBits), "resetVector must fit the physical address space")
  require((resetVector & 1) == 0, "resetVector must be halfword aligned")
  require(iCacheBytes == 0 || (powerOfTwo(iCacheBytes) && iCacheBytes >= 8192 && iCacheBytes <= 65536), "iCacheBytes must be a power of two between 8192 and 65536")
  require(dCacheBytes == 0 || (powerOfTwo(dCacheBytes) && dCacheBytes >= 8192 && dCacheBytes <= 65536), "dCacheBytes must be a power of two between 8192 and 65536")
  require(Set(1, 2).contains(dCacheWays), "dCacheWays must be one or two")
  require(Set(8, 64).contains(dCacheRefillBytes), "dCacheRefillBytes must be eight or sixty-four")
  require(l2CacheBytes == 0 || (powerOfTwo(l2CacheBytes) && l2CacheBytes >= 131072 && l2CacheBytes <= 8388608), "l2CacheBytes must be zero or a power of two between 131072 and 8388608")
  require(Set(64, 128, 256, 512).contains(axiDataBits), "axiDataBits must be 64, 128, 256, or 512")
  require(Set(0, 16, 64).contains(pmpEntries), "pmpEntries must be 0, 16 or 64")

  require(Set(1, 2).contains(loadQueueEntries), "loadQueueEntries must be one or two")
  require(hpmCounters >= 0 && hpmCounters <= 29, "hpmCounters must be between zero and 29")
  require(Set(0, 32, 64).contains(floatingPointBits), "floatingPointBits must be zero, 32 or 64")
  require(!(enableZcb || enableZcmop) || enableC, "Compressed extensions require C")
  require(!(enableZfa || enableZfhmin) || floatingPointBits != 0, "Floating extensions require F")
  require(issueWidth >= 1 && issueWidth <= 3, "issueWidth must be between 1 and 3")
  require(Set(0, 8, 16).contains(branchPredictorEntries), "branchPredictorEntries must be zero, eight or sixteen")
  memoryRegions.foreach(r => require(r.base + r.size <= (BigInt(1) << physicalAddressBits), "Memory region exceeds physical address space"))
  memoryRegions.sortBy(_.base).sliding(2).filter(_.size == 2).foreach { pair =>
    require(pair.head.base + pair.head.size <= pair.last.base, "Memory regions must not overlap")
  }

  def validateFrontend(): Unit =
    validateProtection()
    validatePrediction()
    require(!enableBurstRefill || iCacheBytes != 0, "Burst refill requires an instruction cache")
    require((resetVector & (if enableC then 1 else 3)) == 0, "Frontend resetVector must satisfy IALIGN")

  def validateBackend(): Unit =
    require(asidBits == 0 || enableTranslation, "ASID requires Sv39")
    validateProtection()
    validatePrediction()
    validateCounters()

  def validateCounters(): Unit =
    require(hpmCounters == 0 || (enableCounters && enableInterrupts), "HPM counters require counters and interrupts")
    require(!enableSstc || (enableCounters && enableSupervisorMode && enableInterrupts), "Sstc requires counters, supervisor mode and interrupts")

  def validatePrediction(): Unit =
    require(branchPredictorEntries == 0 || enableBranchPrediction, "Dynamic prediction requires branch prediction")

  def validateCore(): Unit =
    require(Set(0, 39).contains(virtualAddressBits), "RTL supports Bare or Sv39 addressing")
    require(!hasTranslationCache || enableTranslation, "Translation cache requires Sv39")
    validateFrontend()
    validateBackend()

  def validateProtection(): Unit =
    require(virtualAddressBits != 39 || enableSupervisorMode, "Sv39 requires supervisor mode")
    require(pmpEntries == 0 || pmpEntries == 16, "RTL supports zero or sixteen PMP entries")
    require(!enableSupervisorMode || (enableUserMode && enableInterrupts), "Supervisor mode requires user mode and interrupts")

  def validateRtl(): Unit =
    require(!enableJtag || (debugBase.nonEmpty && jtagIdcode.nonEmpty), "JTAG requires a debug window and explicit IDCODE")
    validateCore()
    validateFabric()
    validateDataCache()
    require(!enableDataBurstRefill || dCacheBytes != 0, "Data burst refill requires a data cache")
    validateSharedCache()
    require(memoryRegions.exists(r => r.executable && resetVector >= r.base && resetVector + (if enableC then 2 else 4) <= r.base + r.size), "Reset vector must be in executable memory")

  def resolvedFabricReadSlots: Int = fabricReadSlots.getOrElse(if hartCount > 1 then 2 else 0)

  def validateDataCache(): Unit =
    require(dCacheBytes != 0 || dCacheWays == 1, "Associativity requires a data cache")

  def validateSharedCache(): Unit =
    require(l2CacheBytes == 0 || l2CacheBytes == 131072, "RTL supports zero or 131072 shared cache bytes")

  def validateReadSlots(): Unit =
    require(resolvedFabricReadSlots >= (if hartCount == 1 then 0 else 1) &&
      resolvedFabricReadSlots <= (loadQueueEntries + 1) * hartCount,
      "Read slots must fit the instruction and data clients")

  def validateFabric(): Unit =
    validateReadSlots()
    require(!dCacheWriteback || dCacheBytes != 0, "Writeback requires a data cache")
    localInterruptBase.foreach { base =>
      require(enableInterrupts, "Local interrupt sources require machine interrupts")
      require(base >= 0 && (base & 65535) == 0 && base + 65536 <= (BigInt(1) << physicalAddressBits), "Local interrupt window must be aligned and fit the physical address space")
      require(memoryRegions.exists(r => r.device && r.readable && r.writable && !r.executable && !r.atomic &&
        r.base <= base && base + 65536 <= r.base + r.size), "Local interrupts require a readable writable device region")
    }

  def enableTranslation: Boolean = virtualAddressBits == 39 && enableSupervisorMode
  def enableDebugMemory: Boolean = enableJtag && debugBase.nonEmpty
  def preciseTranslationMaintenance: Boolean = hasTranslationCache && (asidBits != 0 || iTlbEntries != 0 || dTlbEntries != 0)
  def hasTranslationCache: Boolean = tlbEntries != 0 || iTlbEntries != 0 || dTlbEntries != 0
  def enableDataBurstRefill: Boolean = dCacheRefillBytes == 64
  def enableLineRefill: Boolean = enableBurstRefill || enableDataBurstRefill

  val xlen: Int = 64
  val axiIdBits: Int = math.max(1, 32 - Integer.numberOfLeadingZeros(math.max(hartCount, resolvedFabricReadSlots) - 1))
  val registerCount: Int = 32
  val pipelineStages: Int = 8
  val cacheLineBytes: Int = 64
  val fetchWords: Int = if iCacheBytes == 0 || enableC then 1 else 1 << (32 - Integer.numberOfLeadingZeros(issueWidth - 1))
  val fetchCountBits: Int = 32 - Integer.numberOfLeadingZeros(fetchWords)
  val frontendCapacity: Int = if iCacheBytes == 0 || enableC then issueWidth else 2 * math.max(1, fetchWords - 1)
  val issueCountBits: Int = 32 - Integer.numberOfLeadingZeros(issueWidth)
  val backendCapacity: Int = (5 + loadQueueEntries) * issueWidth
  val pipelineOccupancyBits: Int = 32 - Integer.numberOfLeadingZeros(backendCapacity)
  val maxInflight: Int = backendCapacity + frontendCapacity
  val productName: String = "DitDah-A1"

given upickle.default.ReadWriter[DitDahA1Parameter] = upickle.default.macroRW

object DitDahA1Parameter:
  def uncached: DitDahA1Parameter = DitDahA1Parameter(
    virtualAddressBits = 0, iCacheBytes = 0, dCacheBytes = 0,
    l2CacheBytes = 0, pmpEntries = 0
  )
