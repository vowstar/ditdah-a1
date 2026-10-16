// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import mainargs.TokensReader
import scala.util.Try

given TokensReader.Simple[BigInt] with
  def shortName: String = "integer"
  def read(values: Seq[String]): Either[String, BigInt] =
    Try(BigInt(values.head)).toEither.left.map(_.getMessage)

given TokensReader.Simple[MemoryRegion] with
  def shortName: String = "region"
  def read(values: Seq[String]): Either[String, MemoryRegion] =
    Try(upickle.default.read[MemoryRegion](values.head)).toEither.left.map(_.getMessage)
