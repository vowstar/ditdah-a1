// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*

class DitDahA1ExecuteIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val input = Flipped(new Decoupled(new IssuedPacket))
  val output = Aligned(new Decoupled(new ResultPacket))
  val csrAddress = Aligned(UInt(12))
  val csrValue = Flipped(UInt(64))
  val csrLegal = Flipped(Bool())
  val privilege = Flipped(UInt(2))
  val wfiLegal = Flipped(Bool())
  val sretLegal = Flipped(Bool())
  val sfenceLegal = Flipped(Bool())

@generator
object DitDahA1Execute extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1ExecuteIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1Execute"
  def architecture(parameter: DitDahA1Parameter) =
    val io = summon[Interface[DitDahA1ExecuteIO]]
    import DitDahA1Isa.*
    val in = io.input.bits
    val d = in.decoded
    val insn = d.instruction
    val op = d.operation
    val machine = if parameter.enableUserMode then io.privilege === 3.U(2) else true.B
    val wfiLegal = if parameter.enableUserMode then io.wfiLegal else true.B
    val out = io.output.bits
    val a = in.operand1
    val b = in.operand2
    val imm = d.immediate
    val encoding = insn.instruction.asBits
    val funct3 = encoding.bits(14, 12)
    val addImm = (a + imm).asBits.bits(63, 0).asUInt
    val pcImm = (insn.pc + imm).asBits.bits(63, 0).asUInt
    val sequential = (insn.pc + insn.length).asBits.bits(63, 0).asUInt
    io.input.ready := io.output.ready
    io.output.valid := io.input.valid
    io.csrAddress := insn.instruction.asBits.bits(31, 20).asUInt
    out.instruction :<= insn
    out.rd := d.rd
    out.rdWrite := d.writesRd
    out.value := 0.U(64)
    out.nextPc := sequential
    out.load := (op === Ld.U(operationBits)) | (op === Lw.U(operationBits)) | (op === Lwu.U(operationBits)) | (op === Load.U(operationBits)) | (op === AmoaddD.U(operationBits))
    out.store := (op === Sd.U(operationBits)) | (op === Sw.U(operationBits)) | (op === Store.U(operationBits)) | (op === AmoaddD.U(operationBits))
    out.atomic := (op === AmoaddD.U(operationBits)) | (op === Atomic.U(operationBits))
    when(op === Atomic.U(operationBits)) {
      out.load := encoding.bits(31, 27) =/= 3.B(5)
      out.store := encoding.bits(31, 27) =/= 2.B(5)
    }
    val wordMemory = (op === Lw.U(operationBits)) | (op === Lwu.U(operationBits)) | (op === Sw.U(operationBits))
    out.memorySize := wordMemory.?(2.U(3), 3.U(3))
    when((op === Load.U(operationBits)) | (op === Store.U(operationBits))) { out.memorySize := funct3.bits(1, 0).asUInt }
    out.unsignedLoad := (op === Lwu.U(operationBits)) | ((op === Load.U(operationBits)) & funct3.bit(2))
    out.address := addImm
    out.storeData := b
    out.csrAddress := io.csrAddress
    val csr = (op === Csrrw.U(operationBits)) | (op === Csrrs.U(operationBits)) | (op === Csr.U(operationBits))
    val csrAction = (op === Csrrw.U(operationBits)).?(1.B(2), (op === Csrrs.U(operationBits)).?(2.B(2), funct3.bits(1, 0)))
    val csrSource = ((op === Csr.U(operationBits)) & funct3.bit(2)).?(d.rs1, a)
    out.csrWrite := csr & ((csrAction === 1.B(2)) | (d.rs1 =/= 0.U(5)))
    out.csrData := csrSource
    when(csrAction === 2.B(2)) { out.csrData := (io.csrValue.asBits | csrSource.asBits).asUInt }
    when(csrAction === 3.B(2)) { out.csrData := (io.csrValue.asBits & (csrSource.asBits ^ BigInt("ffffffffffffffff", 16).B(64))).asUInt }
    out.mret := op === Mret.U(operationBits)
    out.sret := op === Sret.U(operationBits)
    out.fenceI := op === FenceI.U(operationBits)
    out.sfenceVma := parameter.enableTranslation.B & (op === Fence.U(operationBits)) &
      ((encoding & BigInt("fe007fff", 16).B(32)) === 0x12000073.B(32))
    out.wfi := op === Wfi.U(operationBits)
    when(op === Lui.U(operationBits)) { out.value := imm }
    when(op === Auipc.U(operationBits)) { out.value := pcImm }
    when(op === Addi.U(operationBits)) { out.value := addImm }
    when(op === Add.U(operationBits)) { out.value := (a + b).asBits.bits(63, 0).asUInt }
    val word = (op === AluWordImmediate.U(operationBits)) | (op === AluWordRegister.U(operationBits))
    val register = (op === AluRegister.U(operationBits)) | (op === AluWordRegister.U(operationBits))
    val rhs = register.?(b, imm)
    val left = word.?((a.asBits.bit(31).?(BigInt("ffffffff", 16).B(32), 0.B(32)) ## a.asBits.bits(31, 0)).asUInt, a)
    val shift = word.?((0.B(1) ## rhs.asBits.bits(4, 0)).asUInt, rhs.asBits.bits(5, 0).asUInt)
    val lessSigned = left.asBits.asSInt < rhs.asBits.asSInt
    val alu = Wire(UInt(64))
    alu := (register & encoding.bit(30)).?((left - rhs).asBits.bits(63, 0).asUInt, (left + rhs).asBits.bits(63, 0).asUInt)
    when(funct3 === 1.B(3)) { alu := (left << shift).asBits.bits(63, 0).asUInt }
    when(funct3 === 2.B(3)) { alu := lessSigned.asBits.asUInt }
    when(funct3 === 3.B(3)) { alu := (left < rhs).asBits.asUInt }
    when(funct3 === 4.B(3)) { alu := (left.asBits ^ rhs.asBits).asUInt }
    when(funct3 === 5.B(3)) {
      val logicalLeft = word.?((0.B(32) ## a.asBits.bits(31, 0)).asUInt, a)
      alu := encoding.bit(30).?((left.asBits.asSInt >> shift).asBits.asUInt, logicalLeft >> shift)
    }
    when(funct3 === 6.B(3)) { alu := (left.asBits | rhs.asBits).asUInt }
    when(funct3 === 7.B(3)) { alu := (left.asBits & rhs.asBits).asUInt }
    when((op === AluImmediate.U(operationBits)) | (op === AluRegister.U(operationBits)) | word) {
      out.value := word.?((alu.asBits.bit(31).?(BigInt("ffffffff", 16).B(32), 0.B(32)) ## alu.asBits.bits(31, 0)).asUInt, alu)
    }
    when(csr) { out.value := io.csrValue }
    val jump = (op === Jal.U(operationBits)) | (op === Jalr.U(operationBits))
    val branchCondition = Wire(Bool())
    branchCondition := a === b
    when(funct3.bits(2, 1) === 2.B(2)) { branchCondition := a.asBits.asSInt < b.asBits.asSInt }
    when(funct3.bits(2, 1) === 3.B(2)) { branchCondition := a < b }
    val taken = jump | ((op === Beq.U(operationBits)) & (a === b)) | ((op === Branch.U(operationBits)) & (branchCondition ^ funct3.bit(0)))
    val target = (op === Jalr.U(operationBits)).?((addImm.asBits.bits(63, 1) ## 0.B(1)).asUInt, pcImm)
    when(taken) { out.nextPc := target }
    when(jump) { out.value := sequential }
    when(!insn.fault) {
      when((op === Illegal.U(operationBits)) | (out.sfenceVma & !io.sfenceLegal) | ((op === Mret.U(operationBits)) & !machine) |
        ((op === Wfi.U(operationBits)) & !wfiLegal) |
        ((op === Sret.U(operationBits)) & !io.sretLegal) |
        (csr & (!io.csrLegal | (out.csrWrite & (io.csrAddress.asBits.bits(11, 10) === 3.B(2)))))) {
        out.instruction.fault := true.B
        out.instruction.cause := 2.U(64)
        out.instruction.tval := insn.instruction
      }
      when(op === Ecall.U(operationBits)) {
        out.instruction.fault := true.B
        out.instruction.cause := machine.?(11.U(64),
          (parameter.enableSupervisorMode.B & (io.privilege === 1.U(2))).?(9.U(64), 8.U(64)))
        out.instruction.tval := 0.U(64)
      }
      when(taken & (target.asBits.bits(1, 0) =/= 0.B(2))) {
        out.instruction.fault := true.B
        out.instruction.cause := 0.U(64)
        out.instruction.tval := target
      }
    }
