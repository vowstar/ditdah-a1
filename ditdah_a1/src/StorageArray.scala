// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context, LocationApi, OperationApi, Value, given}
import org.llvm.circt.scalalib.dialect.firrtl.operation.{ConnectApi, SubfieldApi, given}

object StorageArray:
  def apply(name: String, depth: Int, width: Int, readAddress: Referable[UInt],
            writeAddress: Referable[UInt], writeData: Referable[UInt], writeEnable: Referable[Bool],
            readEnable: Referable[Bool], clock: Referable[Clock])(using Arena, Context, Block, InstanceContext): Wire[UInt] =
      val addressBits = Integer.numberOfTrailingZeros(depth)
      val output = Wire(UInt(width))
      // The native verifier requires a containing module while parsing a memory.
      val container = summon[OperationApi].operationCreateParse(
        s"""firrtl.circuit "StorageArray" { firrtl.module @StorageArray() {
          %r, %w = firrtl.mem interesting_name Undefined {depth = $depth : i64,
          name = "$name", portNames = ["read", "write"], readLatency = 1 : i32, writeLatency = 1 : i32} :
          !firrtl.bundle<addr: uint<$addressBits>, en: uint<1>, clk: clock, data flip: uint<$width>>,
          !firrtl.bundle<addr: uint<$addressBits>, en: uint<1>, clk: clock, data: uint<$width>, mask: uint<1>>
        } }""", "instruction-storage")
      val memory = container.getFirstRegion.getFirstBlock.getFirstOperation.getFirstRegion.getFirstBlock.getFirstOperation
      memory.removeFromParent()
      container.destroy()
      val block = summon[Block]
      block.appendOwnedOperation(memory)
      val location = summon[LocationApi].locationUnknownGet
      def field(port: Int, fieldIndex: Int): Value =
        val subfield = summon[SubfieldApi].op(memory.getResult(port), BigInt(fieldIndex), location)
        block.appendOwnedOperation(subfield.operation)
        subfield.result
      def connect(sink: Value, source: Value): Unit =
        block.appendOwnedOperation(summon[ConnectApi].op(source, sink, location).operation)
      connect(field(0, 0), readAddress.refer)
      connect(field(0, 1), readEnable.refer)
      connect(field(0, 2), clock.refer)
      connect(output.refer, field(0, 3))
      connect(field(1, 0), writeAddress.refer)
      connect(field(1, 1), writeEnable.refer)
      connect(field(1, 2), clock.refer)
      connect(field(1, 3), writeData.refer)
      connect(field(1, 4), true.B.refer)
      output

