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
    val out = io.output.bits
    val a = in.operand1
    val b = in.operand2
    val imm = d.immediate
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
    out.load := (op === Ld.U(operationBits)) | (op === AmoaddD.U(operationBits))
    out.store := (op === Sd.U(operationBits)) | (op === AmoaddD.U(operationBits))
    out.address := addImm
    out.storeData := b
    out.csrAddress := io.csrAddress
    out.csrWrite := (op === Csrrw.U(operationBits)) | ((op === Csrrs.U(operationBits)) & (d.rs1 =/= 0.U(5)))
    out.csrData := (op === Csrrs.U(operationBits)).?((io.csrValue.asBits | a.asBits).asUInt, a)
    out.mret := op === Mret.U(operationBits)
    out.fenceI := op === FenceI.U(operationBits)
    when(op === Lui.U(operationBits)) { out.value := imm }
    when(op === Auipc.U(operationBits)) { out.value := pcImm }
    when(op === Addi.U(operationBits)) { out.value := addImm }
    when(op === Add.U(operationBits)) { out.value := (a + b).asBits.bits(63, 0).asUInt }
    when((op === Csrrw.U(operationBits)) | (op === Csrrs.U(operationBits))) { out.value := io.csrValue }
    val jump = (op === Jal.U(operationBits)) | (op === Jalr.U(operationBits))
    val taken = jump | ((op === Beq.U(operationBits)) & (a === b))
    val target = (op === Jalr.U(operationBits)).?((addImm.asBits.bits(63, 1) ## 0.B(1)).asUInt, pcImm)
    when(taken) { out.nextPc := target }
    when(jump) { out.value := sequential }
    when(!insn.fault) {
      when((op === Illegal.U(operationBits)) | (((op === Csrrw.U(operationBits)) | (op === Csrrs.U(operationBits))) & (!io.csrLegal | (out.csrWrite & (io.csrAddress.asBits.bits(11, 10) === 3.B(2)))))) {
        out.instruction.fault := true.B
        out.instruction.cause := 2.U(64)
        out.instruction.tval := insn.instruction
      }
      when(op === Ecall.U(operationBits)) {
        out.instruction.fault := true.B
        out.instruction.cause := 11.U(64)
        out.instruction.tval := 0.U(64)
      }
      when(taken & (target.asBits.bits(1, 0) =/= 0.B(2))) {
        out.instruction.fault := true.B
        out.instruction.cause := 0.U(64)
        out.instruction.tval := target
      }
    }
