// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import java.nio.file.{Files, Path}

object DitDahA1Config:
  def parameter(input: ujson.Value): DitDahA1Parameter =
    val payload = if input.obj.contains("parameters") then input("parameters") else input
    val unknown = payload.obj.keySet.toSet -- DitDahA1Parameter().productElementNames.toSet
    require(unknown.isEmpty, "Unknown configuration fields: " + unknown.toSeq.sorted.mkString(", "))
    upickle.default.read[DitDahA1Parameter](payload)

  def document(parameter: DitDahA1Parameter): ujson.Value =
    ujson.Obj(
      "product" -> parameter.productName,
      "status" -> "configuration",
      "target" -> ujson.Obj(
        "isa" -> "RV64GCB",
        "xlen" -> parameter.xlen,
        "registerCount" -> parameter.registerCount,
        "issueWidth" -> parameter.issueWidth,
        "pipelineStages" -> parameter.pipelineStages,
        "cacheLineBytes" -> parameter.cacheLineBytes
      ),
      "parameters" -> upickle.default.writeJs(parameter)
    )

  def main(args: Array[String]): Unit =
    if args.sameElements(Array("--check")) then
      DitDahA1ParameterCheck.run()
      return
    var parameter = DitDahA1Parameter()
    var output = Path.of("result", "ditdah_a1_config.json")
    var index = 0
    while index < args.length do
      args(index) match
        case "--config" if index + 1 < args.length =>
          val input = ujson.read(Files.readString(Path.of(args(index + 1))))
          parameter = DitDahA1Config.parameter(input)
          index += 2
        case "--output" if index + 1 < args.length =>
          output = Path.of(args(index + 1))
          index += 2
        case _ =>
          throw IllegalArgumentException("Usage: configure-ditdah-a1 [--config input.json] [--output config.json] | --check")
    Option(output.toAbsolutePath.getParent).foreach(Files.createDirectories(_))
    Files.writeString(output, ujson.write(document(parameter), indent = 2) + "\n")
    println(output)
