// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import org.llvm.mlir.scalalib.capi.ir.{Block, LocationApi, OperationApi, Value, given}
import org.llvm.circt.scalalib.dialect.firrtl.operation.{ConnectApi, SubfieldApi, given}

class DitDahA1InstructionCacheIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val upstream = Flipped(new MemoryPort)
  val downstream = Aligned(new MemoryPort)
  val cancel = Flipped(Bool())
  val invalidate = Flipped(Bool())
  val checkAddress = Aligned(UInt(64))
  val allowed = Flipped(Bool())

@generator
object DitDahA1InstructionCache extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1InstructionCacheIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1InstructionCache"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1InstructionCacheIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val indexBits = Integer.numberOfTrailingZeros(parameter.iCacheBytes) - 6
    val lines = parameter.iCacheBytes / 64
    val tagBits = parameter.physicalAddressBits - indexBits - 6
    val state = RegInit(0.U(3))
    val address = Reg(UInt(64))
    val tag = Reg(UInt(8))
    val privileged = Option.when(parameter.enableUserMode)(Reg(Bool()))
    val data = Reg(UInt(32))
    val fault = Reg(Bool())
    val valid = RegInit(0.B(lines))
    val word = Reg(UInt(4))
    val bypass = Reg(Bool())
    val killed = RegInit(false.B)
    val up = io.upstream
    val down = io.downstream
    val index = address.asBits.bits(indexBits + 5, 6).asUInt
    val mask = (1.U(lines) << index).asBits.bits(lines - 1, 0)
    val demandWord = address.asBits.bits(5, 2).asUInt
    val candidate = bypass.?(address, (address.asBits.bits(63, 6) ## word.asBits ## 0.B(2)).asUInt)
    val abort = killed | io.cancel | io.invalidate
    up.request.ready := state === 0.U(3)
    up.response.valid := state === 5.U(3)
    up.response.bits.data := data
    up.response.bits.tag := tag
    up.response.bits.fault := fault
    io.checkAddress := candidate
    down.request.valid := state === 3.U(3)
    down.request.bits.address := candidate
    down.request.bits.data := 0.U(64)
    down.request.bits.size := 2.U(3)
    down.request.bits.mask := 0.U(8)
    down.request.bits.tag := tag
    down.request.bits.write := false.B
    down.request.bits.fetch := true.B
    down.request.bits.privileged := privileged.getOrElse(true.B)
    down.request.bits.atomic := false.B
    down.request.bits.atomicOperation := 0.U(5)
    down.request.bits.scEligible := false.B
    down.response.ready := state === 4.U(3)
    val reading = up.request.valid & up.request.ready
    val responseFault = down.response.bits.fault | (down.response.bits.tag =/= tag)
    val filling = down.response.valid & down.response.ready & !responseFault & !bypass & !abort
    val complete = word === 15.U(4)

    def array(name: String, depth: Int, width: Int, readAddress: Referable[UInt],
              writeAddress: Referable[UInt], writeData: Referable[UInt], writeEnable: Referable[Bool]): Wire[UInt] =
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
      connect(field(0, 1), reading.refer)
      connect(field(0, 2), io.clock.refer)
      connect(output.refer, field(0, 3))
      connect(field(1, 0), writeAddress.refer)
      connect(field(1, 1), writeEnable.refer)
      connect(field(1, 2), io.clock.refer)
      connect(field(1, 3), writeData.refer)
      connect(field(1, 4), true.B.refer)
      output

    val wordRead = array("instructions", parameter.iCacheBytes / 4, 32,
      up.request.bits.address.asBits.bits(indexBits + 5, 2).asUInt,
      (index.asBits ## word.asBits).asUInt, down.response.bits.data.asBits.bits(31, 0).asUInt, filling)
    val tagRead = array("tags", lines, tagBits,
      up.request.bits.address.asBits.bits(indexBits + 5, 6).asUInt, index,
      address.asBits.bits(parameter.physicalAddressBits - 1, indexBits + 6).asUInt, filling & complete)
    val hit = (valid.asUInt >> index).asBits.bit(0) &
      (tagRead === address.asBits.bits(parameter.physicalAddressBits - 1, indexBits + 6).asUInt)

    when(reading) {
      privileged.foreach(_ := up.request.bits.privileged)
      address := up.request.bits.address
      tag := up.request.bits.tag
      data := 0.U(32)
      fault := false.B
      word := 0.U(4)
      bypass := false.B
      killed := io.cancel | io.invalidate
      state := (io.cancel | io.invalidate).?(5.U(3), 1.U(3))
    }
    when(state === 1.U(3)) {
      when(abort) { state := 5.U(3) }.otherwise {
        when(hit) { data := wordRead; state := 5.U(3) }.otherwise {
          valid := valid & ~mask
          state := 2.U(3)
        }
      }
    }
    when(state === 2.U(3)) {
      when(abort) { state := 5.U(3) }.otherwise {
        when(io.allowed) { state := 3.U(3) }.otherwise {
          when(bypass | (word === demandWord)) { fault := true.B; state := 5.U(3) }.otherwise {
            bypass := true.B
          }
        }
      }
    }
    when(down.request.valid & down.request.ready) { state := 4.U(3) }
    when(down.response.valid & down.response.ready) {
      when(abort) { state := 5.U(3) }.otherwise {
        when(responseFault) {
          when(bypass | (word === demandWord)) { fault := true.B; state := 5.U(3) }.otherwise {
            bypass := true.B
            state := 2.U(3)
          }
        }.otherwise {
          when(bypass | (word === demandWord)) { data := down.response.bits.data.asBits.bits(31, 0).asUInt }
          when(bypass) { state := 5.U(3) }.otherwise {
            when(complete) { valid := valid | mask; state := 5.U(3) }.otherwise {
              word := (word + 1.U(4)).asBits.bits(3, 0).asUInt
              state := 2.U(3)
            }
          }
        }
      }
    }
    when(up.response.valid & up.response.ready) { state := 0.U(3) }
    when((io.cancel | io.invalidate) & (state =/= 0.U(3))) { killed := true.B }
    when(io.invalidate) { valid := 0.B(lines) }
