// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1DecodeIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val input = Flipped(new Decoupled(new FetchPacket))
  val output = Aligned(new Decoupled(new DecodedPacket))

@generator
object DitDahA1Decode extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1DecodeIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Decode"
  def architecture(parameter: DitDahA1Parameter) =
    import DitDahA1Isa.*
    val io = summon[Interface[DitDahA1DecodeIO]]
    val in = io.input.bits
    val out = io.output.bits
    val insn = in.instruction.asBits
    val opcode = insn.bits(6, 0)
    val funct3 = insn.bits(14, 12)
    io.input.ready := io.output.ready
    io.output.valid := io.input.valid
    out.instruction :<= in
    out.operation := Illegal.U(operationBits)
    out.rs1 := insn.bits(19, 15).asUInt
    out.rs2 := insn.bits(24, 20).asUInt
    out.rd := insn.bits(11, 7).asUInt
    val immI = (insn.bit(31).?(BigInt("fffffffffffff", 16).B(52), 0.B(52)) ## insn.bits(31, 20)).asUInt
    val immS = (insn.bit(31).?(BigInt("fffffffffffff", 16).B(52), 0.B(52)) ## insn.bits(31, 25) ## insn.bits(11, 7)).asUInt
    val immU = (insn.bit(31).?(BigInt("ffffffff", 16).B(32), 0.B(32)) ## insn.bits(31, 12) ## 0.B(12)).asUInt
    val immB = (insn.bit(31).?(((BigInt(1) << 51) - 1).B(51), 0.B(51)) ## insn.bits(31, 31) ## insn.bits(7, 7) ## insn.bits(30, 25) ## insn.bits(11, 8) ## 0.B(1)).asUInt
    val immJ = (insn.bit(31).?(((BigInt(1) << 43) - 1).B(43), 0.B(43)) ## insn.bits(31, 31) ## insn.bits(19, 12) ## insn.bits(20, 20) ## insn.bits(30, 21) ## 0.B(1)).asUInt
    out.immediate := immI
    when(opcode === 0x37.B(7)) { out.operation := Lui.U(operationBits); out.immediate := immU }
    when(opcode === 0x17.B(7)) { out.operation := Auipc.U(operationBits); out.immediate := immU }
    when((opcode === 0x13.B(7)) & (funct3 === 0.B(3))) { out.operation := Addi.U(operationBits) }
    when((opcode === 0x33.B(7)) & (funct3 === 0.B(3)) & (insn.bits(31, 25) === 0.B(7))) { out.operation := Add.U(operationBits) }
    when((opcode === 0x33.B(7)) & (funct3 === 0.B(3)) & (insn.bits(31, 25) === 1.B(7))) { out.operation := Mul.U(operationBits) }
    when((opcode === 0x63.B(7)) & (funct3 === 0.B(3))) { out.operation := Beq.U(operationBits); out.immediate := immB }
    when(opcode === 0x6f.B(7)) { out.operation := Jal.U(operationBits); out.immediate := immJ }
    when((opcode === 0x67.B(7)) & (funct3 === 0.B(3))) { out.operation := Jalr.U(operationBits) }
    when((opcode === 0x03.B(7)) & (funct3 === 3.B(3))) { out.operation := Ld.U(operationBits) }
    when((opcode === 0x23.B(7)) & (funct3 === 3.B(3))) { out.operation := Sd.U(operationBits); out.immediate := immS }
    when((opcode === 0x2f.B(7)) & (funct3 === 3.B(3)) & (insn.bits(31, 27) === 0.B(5))) { out.operation := AmoaddD.U(operationBits); out.immediate := 0.U(64) }
    when((opcode === 0x73.B(7)) & (funct3 === 1.B(3))) { out.operation := Csrrw.U(operationBits) }
    when((opcode === 0x73.B(7)) & (funct3 === 2.B(3))) { out.operation := Csrrs.U(operationBits) }
    when(insn === 0x00000073L.B(32)) { out.operation := Ecall.U(operationBits) }
    when(insn === 0x30200073L.B(32)) { out.operation := Mret.U(operationBits) }
    when((opcode === 0x0f.B(7)) & (funct3 === 0.B(3))) { out.operation := Fence.U(operationBits) }
    when((opcode === 0x0f.B(7)) & (funct3 === 1.B(3))) { out.operation := FenceI.U(operationBits) }
    val operation = out.operation
    val both = (operation === Add.U(operationBits)) | (operation === Mul.U(operationBits)) | (operation === Beq.U(operationBits)) | (operation === Sd.U(operationBits)) | (operation === AmoaddD.U(operationBits))
    out.usesRs1 := !in.fault & (both | (operation === Addi.U(operationBits)) | (operation === Jalr.U(operationBits)) | (operation === Ld.U(operationBits)) | (operation === Csrrw.U(operationBits)) | (operation === Csrrs.U(operationBits)))
    out.usesRs2 := !in.fault & both
    out.writesRd := !in.fault & (operation =/= Illegal.U(operationBits)) & (operation =/= Beq.U(operationBits)) & (operation =/= Sd.U(operationBits)) & (operation =/= Ecall.U(operationBits)) & (operation =/= Mret.U(operationBits)) & (operation =/= Fence.U(operationBits)) & (operation =/= FenceI.U(operationBits))
    out.serializing := !in.fault & ((operation === Csrrw.U(operationBits)) | (operation === Csrrs.U(operationBits)) | (operation === Mret.U(operationBits)) | (operation === Fence.U(operationBits)) | (operation === FenceI.U(operationBits)))
