// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import java.nio.file.{Files, Path}

object DitDahA1Config:
  def parameter(input: ujson.Value): DitDahA1Parameter =
    val original = if input.obj.contains("parameters") then input("parameters") else input
    val payload = ujson.read(ujson.write(original))
    if payload.obj.contains("resetAddress") then
      require(!payload.obj.contains("resetVector"), "Specify only resetVector")
      payload("resetVector") = payload.obj.remove("resetAddress").get
    val unknown = payload.obj.keySet.toSet -- DitDahA1Parameter().productElementNames.toSet
    require(unknown.isEmpty, "Unknown configuration fields: " + unknown.toSeq.sorted.mkString(", "))
    payload.obj.get("memoryRegions").foreach { regions =>
      val fields = MemoryRegion().productElementNames.toSet
      regions.arr.foreach { region =>
        val unknownRegion = region.obj.keySet.toSet -- fields
        require(unknownRegion.isEmpty, "Unknown memory region fields: " + unknownRegion.toSeq.sorted.mkString(", "))
      }
    }
    upickle.default.read[DitDahA1Parameter](payload)

  def document(parameter: DitDahA1Parameter): ujson.Value =
    ujson.Obj(
      "product" -> parameter.productName,
      "schemaVersion" -> 2,
      "status" -> "development",
      "implementation" -> ujson.Obj(
        "instructions" -> ujson.Arr.from(DitDahA1Isa.instructions ++ (if parameter.enableSupervisorMode then DitDahA1Isa.supervisorInstructions else Seq.empty) ++ (if parameter.enableTranslation then Seq("sfence.vma") else Seq.empty)),
        "privilege" -> (if parameter.enableSupervisorMode then "MSU" else if parameter.enableUserMode then "MU" else "M"), "issueWidth" -> parameter.issueWidth, "maxInflight" -> parameter.maxInflight,
        "pipelineStages" -> parameter.pipelineStages, "backendCapacity" -> parameter.backendCapacity, "frontendCapacity" -> parameter.frontendCapacity,
        "fetchWords" -> parameter.fetchWords,
        "translation" -> (if parameter.enableTranslation then "Sv39/Svade" else "Bare"),
        "tlbEntries" -> (if parameter.enableTranslation then parameter.tlbEntries else 0),
        "enableBurstRefill" -> parameter.enableBurstRefill, "isaComplete" -> false
      ),
      "target" -> ujson.Obj(
        "isa" -> "RV64GCB", "maxHartCount" -> 16,
        "xlen" -> parameter.xlen,
        "registerCount" -> parameter.registerCount,
        "issueWidth" -> 3,
        "pipelineStages" -> parameter.pipelineStages,
        "cacheLineBytes" -> parameter.cacheLineBytes
      ),
      "parameters" -> upickle.default.writeJs(parameter)
    )

  def main(args: Array[String]): Unit =
    if args.sameElements(Array("--check")) then
      DitDahA1ParameterCheck.run()
      return
    var parameter = DitDahA1Parameter.uncached
    var rtl = false
    var output = Path.of("result", "ditdah_a1_config.json")
    var index = 0
    while index < args.length do
      args(index) match
        case "--rtl" =>
          rtl = true
          index += 1
        case "--config" if index + 1 < args.length =>
          val input = ujson.read(Files.readString(Path.of(args(index + 1))))
          parameter = DitDahA1Config.parameter(input)
          index += 2
        case "--output" if index + 1 < args.length =>
          output = Path.of(args(index + 1))
          index += 2
        case _ =>
          throw IllegalArgumentException("Usage: configure-ditdah-a1 [--rtl] [--config input.json] [--output config.json] | --check")
    if rtl then parameter.validateRtl()
    Option(output.toAbsolutePath.getParent).foreach(Files.createDirectories(_))
    Files.writeString(output, ujson.write(document(parameter), indent = 2) + "\n")
    println(output)
