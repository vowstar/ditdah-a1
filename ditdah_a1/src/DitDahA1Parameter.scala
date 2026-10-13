// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.Parameter

case class DitDahA1Parameter(
  resetAddress: BigInt = BigInt(0),
  hartCount: Int = 1,
  physicalAddressBits: Int = 56,
  virtualAddressBits: Int = 39,
  iCacheBytes: Int = 32768,
  dCacheBytes: Int = 32768,
  l2CacheBytes: Int = 262144,
  axiDataBits: Int = 128,
  pmpEntries: Int = 16
) extends Parameter:
  private def powerOfTwo(value: Int): Boolean = value > 0 && (value & (value - 1)) == 0

  require(hartCount >= 1 && hartCount <= 8, "hartCount must be between 1 and 8")
  require(physicalAddressBits >= 32 && physicalAddressBits <= 56, "physicalAddressBits must be between 32 and 56")
  require(Set(39, 48).contains(virtualAddressBits), "virtualAddressBits must select Sv39 or Sv48")
  require(resetAddress >= 0 && resetAddress < (BigInt(1) << physicalAddressBits), "resetAddress must fit the physical address space")
  require((resetAddress & 1) == 0, "resetAddress must be halfword aligned")
  require(powerOfTwo(iCacheBytes) && iCacheBytes >= 8192 && iCacheBytes <= 65536, "iCacheBytes must be a power of two between 8192 and 65536")
  require(powerOfTwo(dCacheBytes) && dCacheBytes >= 8192 && dCacheBytes <= 65536, "dCacheBytes must be a power of two between 8192 and 65536")
  require(l2CacheBytes == 0 || (powerOfTwo(l2CacheBytes) && l2CacheBytes >= 131072 && l2CacheBytes <= 8388608), "l2CacheBytes must be zero or a power of two between 131072 and 8388608")
  require(Set(128, 256, 512).contains(axiDataBits), "axiDataBits must be 128, 256, or 512")
  require(pmpEntries >= 0 && pmpEntries <= 64, "pmpEntries must be between 0 and 64")

  val xlen: Int = 64
  val registerCount: Int = 32
  val issueWidth: Int = 2
  val pipelineStages: Int = 8
  val cacheLineBytes: Int = 64
  val productName: String = "DitDah-A1"

given upickle.default.ReadWriter[DitDahA1Parameter] = upickle.default.macroRW
