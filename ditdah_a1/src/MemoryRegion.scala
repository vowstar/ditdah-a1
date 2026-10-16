// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

@upickle.implicits.serializeDefaults(true)
case class MemoryRegion(
  base: BigInt = BigInt(0),
  size: BigInt = BigInt(65536),
  readable: Boolean = true,
  writable: Boolean = true,
  executable: Boolean = true,
  device: Boolean = false
):
  require(base >= 0 && size > 0, "Memory regions require nonnegative base and positive size")
  require((base & 7) == 0 && (size & 7) == 0, "Memory regions must be doubleword aligned")
  require(!device || !executable, "Device memory cannot be executable")

given upickle.default.ReadWriter[MemoryRegion] = upickle.default.macroRW
