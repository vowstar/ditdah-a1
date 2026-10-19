// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.Parameter

@upickle.implicits.serializeDefaults(true)
case class DitDahA1Parameter(
  resetVector: BigInt = BigInt(0),
  hartCount: Int = 1,
  physicalAddressBits: Int = 56,
  virtualAddressBits: Int = 39,
  tlbEntries: Int = 0,
  iCacheBytes: Int = 32768,
  dCacheBytes: Int = 32768,
  l2CacheBytes: Int = 262144,
  axiDataBits: Int = 128,
  pmpEntries: Int = 16,
  issueWidth: Int = 1,
  enableInterrupts: Boolean = false,
  enableUserMode: Boolean = false,
  enableSupervisorMode: Boolean = false,
  enableTrace: Boolean = false,
  localInterruptBase: Option[BigInt] = None,
  memoryRegions: Seq[MemoryRegion] = Seq(MemoryRegion())
) extends Parameter:
  private def powerOfTwo(value: Int): Boolean = value > 0 && (value & (value - 1)) == 0

  require(hartCount >= 1 && hartCount <= 16, "hartCount must be between 1 and 16")
  require(physicalAddressBits >= 32 && physicalAddressBits <= 56, "physicalAddressBits must be between 32 and 56")
  require(Set(0, 39, 48).contains(virtualAddressBits), "virtualAddressBits must select Bare, Sv39 or Sv48")
  require(Set(0, 2, 4).contains(tlbEntries), "tlbEntries must be zero, two or four")
  require(resetVector >= 0 && resetVector < (BigInt(1) << physicalAddressBits), "resetVector must fit the physical address space")
  require((resetVector & 1) == 0, "resetVector must be halfword aligned")
  require(iCacheBytes == 0 || (powerOfTwo(iCacheBytes) && iCacheBytes >= 8192 && iCacheBytes <= 65536), "iCacheBytes must be a power of two between 8192 and 65536")
  require(dCacheBytes == 0 || (powerOfTwo(dCacheBytes) && dCacheBytes >= 8192 && dCacheBytes <= 65536), "dCacheBytes must be a power of two between 8192 and 65536")
  require(l2CacheBytes == 0 || (powerOfTwo(l2CacheBytes) && l2CacheBytes >= 131072 && l2CacheBytes <= 8388608), "l2CacheBytes must be zero or a power of two between 131072 and 8388608")
  require(Set(64, 128, 256, 512).contains(axiDataBits), "axiDataBits must be 64, 128, 256, or 512")
  require(Set(0, 16, 64).contains(pmpEntries), "pmpEntries must be 0, 16 or 64")

  require(Set(1, 2).contains(issueWidth), "issueWidth must be 1 or 2")
  memoryRegions.foreach(r => require(r.base + r.size <= (BigInt(1) << physicalAddressBits), "Memory region exceeds physical address space"))
  memoryRegions.sortBy(_.base).sliding(2).filter(_.size == 2).foreach { pair =>
    require(pair.head.base + pair.head.size <= pair.last.base, "Memory regions must not overlap")
  }

  def validateFrontend(): Unit =
    validateProtection()
    require((resetVector & 3) == 0, "Frontend requires a word-aligned resetVector")

  def validateBackend(): Unit =
    validateProtection()
    require(issueWidth == 1, "Backend supports single issue")

  def validateCore(): Unit =
    require(Set(0, 39).contains(virtualAddressBits), "RTL supports Bare or Sv39 addressing")
    require(tlbEntries == 0 || enableTranslation, "Translation cache requires Sv39")
    validateFrontend()
    validateBackend()

  def validateProtection(): Unit =
    require(virtualAddressBits != 39 || enableSupervisorMode, "Sv39 requires supervisor mode")
    require(pmpEntries == 0 || pmpEntries == 16, "RTL supports zero or sixteen PMP entries")
    require(!enableSupervisorMode || (enableUserMode && enableInterrupts), "Supervisor mode requires user mode and interrupts")

  def validateRtl(): Unit =
    validateCore()
    validateFabric()
    require(dCacheBytes == 0 || dCacheBytes == 8192, "RTL supports zero or 8192 data cache bytes")
    require(l2CacheBytes == 0, "RTL does not support a shared cache")
    require(memoryRegions.exists(r => r.executable && resetVector >= r.base && resetVector + 4 <= r.base + r.size), "Reset vector must be in executable memory")

  def validateFabric(): Unit = localInterruptBase.foreach { base =>
    require(enableInterrupts, "Local interrupt sources require machine interrupts")
    require(base >= 0 && (base & 65535) == 0 && base + 65536 <= (BigInt(1) << physicalAddressBits), "Local interrupt window must be aligned and fit the physical address space")
    require(memoryRegions.exists(r => r.device && r.readable && r.writable && !r.executable && !r.atomic &&
      r.base <= base && base + 65536 <= r.base + r.size), "Local interrupts require a readable writable device region")
  }

  def enableTranslation: Boolean = virtualAddressBits == 39 && enableSupervisorMode

  val xlen: Int = 64
  val axiIdBits: Int = math.max(1, 32 - Integer.numberOfLeadingZeros(hartCount - 1))
  val registerCount: Int = 32
  val pipelineStages: Int = 8
  val cacheLineBytes: Int = 64
  val maxInflight: Int = 5
  val productName: String = "DitDah-A1"

given upickle.default.ReadWriter[DitDahA1Parameter] = upickle.default.macroRW

object DitDahA1Parameter:
  def uncached: DitDahA1Parameter = DitDahA1Parameter(
    virtualAddressBits = 0, iCacheBytes = 0, dCacheBytes = 0,
    l2CacheBytes = 0, pmpEntries = 0
  )
