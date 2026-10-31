// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1DecodeIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val input = Flipped(new Decoupled(new FetchPacket))
  val output = Aligned(new Decoupled(new DecodedPacket(parameter)))

@generator
object DitDahA1Decode extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1DecodeIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Decode"
  def architecture(parameter: DitDahA1Parameter) =
    import DitDahA1Isa.*
    val io = summon[Interface[DitDahA1DecodeIO]]
    val in = io.input.bits
    val out = io.output.bits
    val insn = if parameter.enableC then (in.length === 2.U(3)).?(DitDahA1Compressed(in.instruction, parameter.floatingPointBits == 64), in.instruction.asBits) else in.instruction.asBits
    out.floating.foreach(_ := false.B)
    out.fpWrite.foreach(_ := false.B)
    out.functionCode.foreach(_ := (insn.bits(30, 30) ## insn.bits(14, 12)).asUInt)
    val opcode = insn.bits(6, 0)
    val funct3 = insn.bits(14, 12)
    val funct7 = insn.bits(31, 25)
    val atomicOperation = insn.bits(31, 27)
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
    val immediateShift = (funct3 === 1.B(3)) | (funct3 === 5.B(3))
    val shiftEncoding = (insn.bits(31, 26) === 0.B(6)) | ((funct3 === 5.B(3)) & (insn.bits(31, 26) === 0x10.B(6)))
    when((opcode === 0x13.B(7)) & (funct3 =/= 0.B(3)) & (!immediateShift | shiftEncoding)) { out.operation := AluImmediate.U(operationBits) }
    val subtractOrArithmetic = (funct7 === 0x20.B(7)) & ((funct3 === 0.B(3)) | (funct3 === 5.B(3)))
    when((opcode === 0x33.B(7)) & (((funct7 === 0.B(7)) & (funct3 =/= 0.B(3))) | subtractOrArithmetic)) { out.operation := AluRegister.U(operationBits) }
    val wordShift = (funct3 === 1.B(3)) | (funct3 === 5.B(3))
    val wordShiftEncoding = (funct7 === 0.B(7)) | ((funct3 === 5.B(3)) & (funct7 === 0x20.B(7)))
    when((opcode === 0x1b.B(7)) & ((funct3 === 0.B(3)) | (wordShift & wordShiftEncoding))) { out.operation := AluWordImmediate.U(operationBits) }
    when((opcode === 0x3b.B(7)) & (((funct7 === 0.B(7)) & ((funct3 === 0.B(3)) | wordShift)) | subtractOrArithmetic)) { out.operation := AluWordRegister.U(operationBits) }
    when((opcode === 0x33.B(7)) & (funct3 === 0.B(3)) & (insn.bits(31, 25) === 0.B(7))) { out.operation := Add.U(operationBits) }
    if parameter.enableM then
      when(((opcode === 0x33.B(7)) | ((opcode === 0x3b.B(7)) & ((funct3 === 0.B(3)) | funct3.bit(2)))) &
        (funct7 === 1.B(7))) { out.operation := Arithmetic.U(operationBits) }
    when((opcode === 0x63.B(7)) & (funct3 === 0.B(3))) { out.operation := Beq.U(operationBits); out.immediate := immB }
    when((opcode === 0x63.B(7)) & ((funct3 === 1.B(3)) | funct3.bit(2))) { out.operation := Branch.U(operationBits); out.immediate := immB }
    when(opcode === 0x6f.B(7)) { out.operation := Jal.U(operationBits); out.immediate := immJ }
    when((opcode === 0x67.B(7)) & (funct3 === 0.B(3))) { out.operation := Jalr.U(operationBits) }
    when((opcode === 0x03.B(7)) & (funct3 === 3.B(3))) { out.operation := Ld.U(operationBits) }
    when((opcode === 0x03.B(7)) & (funct3 === 2.B(3))) { out.operation := Lw.U(operationBits) }
    when((opcode === 0x03.B(7)) & (funct3 === 6.B(3))) { out.operation := Lwu.U(operationBits) }
    when((opcode === 0x03.B(7)) & ((funct3 === 0.B(3)) | (funct3 === 1.B(3)) | (funct3 === 4.B(3)) | (funct3 === 5.B(3)))) { out.operation := Load.U(operationBits) }
    when((opcode === 0x23.B(7)) & (funct3 === 3.B(3))) { out.operation := Sd.U(operationBits); out.immediate := immS }
    when((opcode === 0x23.B(7)) & (funct3 === 2.B(3))) { out.operation := Sw.U(operationBits); out.immediate := immS }
    when((opcode === 0x23.B(7)) & ((funct3 === 0.B(3)) | (funct3 === 1.B(3)))) { out.operation := Store.U(operationBits); out.immediate := immS }
    val lr = atomicOperation === 2.B(5)
    if parameter.enableA then
      val supportedAtomic = (DitDahA1Isa.atomicOperations :+ 3).map(op => atomicOperation === op.B(5)).reduce(_ | _) | (lr & (out.rs2 === 0.U(5)))
      when((opcode === 0x2f.B(7)) & ((funct3 === 2.B(3)) | (funct3 === 3.B(3))) & supportedAtomic) {
        out.operation := ((atomicOperation === 0.B(5)) & (funct3 === 3.B(3))).?(AmoaddD.U(operationBits), Atomic.U(operationBits))
        out.immediate := 0.U(64)
      }
    when((opcode === 0x73.B(7)) & (funct3 === 1.B(3))) { out.operation := Csrrw.U(operationBits) }
    when((opcode === 0x73.B(7)) & (funct3 === 2.B(3))) { out.operation := Csrrs.U(operationBits) }
    when((opcode === 0x73.B(7)) & ((funct3 === 3.B(3)) | funct3.bit(2) & (funct3 =/= 4.B(3)))) { out.operation := Csr.U(operationBits) }
    when((insn === 0x00000073L.B(32)) | (insn === 0x00100073L.B(32))) { out.operation := Ecall.U(operationBits) }
    when(insn === 0x30200073L.B(32)) { out.operation := Mret.U(operationBits) }
    if parameter.enableJtag then
      when(insn === 0x7b200073L.B(32)) { out.operation := Mret.U(operationBits) }
    if parameter.enableSupervisorMode then
      when(insn === 0x10200073L.B(32)) { out.operation := Sret.U(operationBits) }
    when(insn === 0x10500073L.B(32)) { out.operation := Wfi.U(operationBits) }
    when((opcode === 0x0f.B(7)) & (funct3 === 0.B(3))) { out.operation := Fence.U(operationBits) }
    when((opcode === 0x0f.B(7)) & (funct3 === 1.B(3))) { out.operation := FenceI.U(operationBits) }
    for (_, mask, encoding) <- DitDahA1BitManip.encodings(parameter) do
      when((insn & BigInt(mask).B(32)) === BigInt(encoding).B(32)) {
        val unary = (encoding & 0x7f) == 0x13 || (encoding & 0x7f) == 0x1b || mask == 0xfff0707fL
        out.operation := (if unary then AluImmediate else AluRegister).U(operationBits)
      }
    if parameter.floatingPointBits != 0 then
      val format = (insn.bits(26, 25) === 0.B(2)) | ((parameter.floatingPointBits == 64).B & (insn.bits(26, 25) === 1.B(2)))
      val function = insn.bits(31, 27)
      val rounding = (funct3.asUInt <= 4.U(3)) | (funct3 === 7.B(3))
      val unary = out.rs2 === 0.U(5)
      val conversion = ((function === 24.B(5)) | (function === 26.B(5))) & (out.rs2 <= 3.U(5)) & rounding
      val formatConversion = (parameter.floatingPointBits == 64).B & (function === 8.B(5)) & rounding &
        (insn.bit(25).?((out.rs2 === 0.U(5)), (out.rs2 === 1.U(5))))
      val supported = ((function.asUInt <= 3.U(5)) & rounding) | ((function === 11.B(5)) & unary & rounding) |
        (((function === 4.B(5)) | (function === 20.B(5))) & (funct3.asUInt <= 2.U(3))) |
        ((function === 5.B(5)) & (funct3.asUInt <= 1.U(3))) | conversion | formatConversion |
        ((function === 28.B(5)) & unary & (funct3.asUInt <= 1.U(3))) | ((function === 30.B(5)) & unary & (funct3 === 0.B(3)))
      val fused = Seq(0x43, 0x47, 0x4b, 0x4f).map(op => opcode === op.B(7)).reduce(_ | _)
      val arithmetic = format & (((opcode === 0x53.B(7)) & supported) | (fused & rounding))
      val memory = ((funct3 === 2.B(3)) | ((parameter.floatingPointBits == 64).B & (funct3 === 3.B(3))))
      val load = (opcode === 0x07.B(7)) & memory
      val store = (opcode === 0x27.B(7)) & memory
      out.floating.get := arithmetic | load | store
      out.fpWrite.get := !in.fault & (load | (arithmetic & (fused | !Seq(20, 24, 28).map(f => function === f.B(5)).reduce(_ | _))))
      when(arithmetic) { out.operation := Arithmetic.U(operationBits) }
      when(load) { out.operation := (funct3 === 2.B(3)).?(Lw.U(operationBits), Ld.U(operationBits)) }
      when(store) { out.operation := (funct3 === 2.B(3)).?(Sw.U(operationBits), Sd.U(operationBits)); out.immediate := immS }
    val operation = out.operation
    val csr = (operation === Csrrw.U(operationBits)) | (operation === Csrrs.U(operationBits)) | (operation === Csr.U(operationBits))
    val branch = (operation === Beq.U(operationBits)) | (operation === Branch.U(operationBits))
    val store = (operation === Sd.U(operationBits)) | (operation === Sw.U(operationBits)) | (operation === Store.U(operationBits))
    val both = (operation === Add.U(operationBits)) | (operation === Arithmetic.U(operationBits)) | branch | store | (operation === AmoaddD.U(operationBits)) | (operation === AluRegister.U(operationBits)) | (operation === AluWordRegister.U(operationBits))
    out.usesRs1 := !in.fault & (both | (operation === Addi.U(operationBits)) | (operation === AluImmediate.U(operationBits)) | (operation === AluWordImmediate.U(operationBits)) | (operation === Jalr.U(operationBits)) | (operation === Ld.U(operationBits)) | (operation === Lw.U(operationBits)) | (operation === Lwu.U(operationBits)) | (operation === Load.U(operationBits)) | (csr & !funct3.bit(2)))
    out.usesRs2 := !in.fault & both
    when(operation === Atomic.U(operationBits)) {
      out.usesRs1 := !in.fault
      out.usesRs2 := !in.fault & !lr
    }
    if parameter.enableTranslation then
      when((in.instruction.asBits & BigInt("fe007fff", 16).B(32)) === 0x12000073.B(32)) {
        out.operation := Fence.U(operationBits)
        if parameter.preciseTranslationMaintenance then
          out.usesRs1 := !in.fault
          out.usesRs2 := !in.fault
      }
    out.writesRd := !in.fault & (operation =/= Illegal.U(operationBits)) & !branch & !store & (operation =/= Ecall.U(operationBits)) & (operation =/= Mret.U(operationBits)) & (operation =/= Sret.U(operationBits)) & (operation =/= Fence.U(operationBits)) & (operation =/= FenceI.U(operationBits)) & (operation =/= Wfi.U(operationBits))
    out.serializing := !in.fault & (csr | (operation === Mret.U(operationBits)) | (operation === Sret.U(operationBits)) | (operation === Fence.U(operationBits)) | (operation === FenceI.U(operationBits)) | (operation === Wfi.U(operationBits)))
    if parameter.floatingPointBits != 0 then
      when(out.floating.get) {
        val arithmetic = operation === Arithmetic.U(operationBits)
        out.usesRs2 := false.B
        when(arithmetic) { out.usesRs1 := !in.fault & ((insn.bits(31, 27) === 26.B(5)) | (insn.bits(31, 27) === 30.B(5))) & (opcode === 0x53.B(7)) }
        out.writesRd := !in.fault & arithmetic & !out.fpWrite.get
        out.serializing := !in.fault
      }
