// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
package com.vowstar.ditdah.a1

import me.jiuyang.zaozi.*
import me.jiuyang.zaozi.default.{*, given}
import me.jiuyang.zaozi.reftpe.*
import me.jiuyang.zaozi.valuetpe.*
import java.lang.foreign.Arena
import org.llvm.mlir.scalalib.capi.ir.{Block, Context}

class DitDahA1DebugModuleIO(parameter: DitDahA1Parameter) extends HWBundle(parameter):
  val clock = Flipped(Clock())
  val reset = Flipped(Reset())
  val hartsReset = Flipped(Bool())
  val ndmreset = Aligned(Bool())
  val harts = Flipped(Vec(parameter.hartCount, new DebugHartPort))
  val dmi = Flipped(new DmiPort)
  val memory = Flipped(new MemoryPort(parameter))
  val memoryHart = Flipped(UInt(4))

private object DebugProgram:
  val exception = 0x80
  val access = 0x100
  val program = 0x180
  val data = program + 32
  val flags = 0x200
  val halted = 0x208
  val failed = 0x210
  def csr(rd: Int, address: Int, rs: Int, operation: Int): Int =
    (address << 20) | (rs << 15) | (operation << 12) | (rd << 7) | 0x73
  def csrSwap(r: Int): Int = csr(r, 0x7b2, r, 1)
  def load(r: Int, offset: Int): Int = (offset << 20) | (r << 15) | (2 << 12) | (r << 7) | 3
  def store(offset: Int): Int = ((offset >> 5) << 25) | (8 << 15) | (2 << 12) | ((offset & 31) << 7) | 0x23
  def branch(offset: Int): Int = ((offset >> 12 & 1) << 31) | ((offset >> 5 & 63) << 25) |
    (8 << 15) | ((offset >> 1 & 15) << 8) | ((offset >> 11 & 1) << 7) | 0x63
  def jump(offset: Int): Int = ((offset >> 20 & 1) << 31) | ((offset >> 1 & 1023) << 21) |
    ((offset >> 11 & 1) << 20) | ((offset >> 12 & 255) << 12) | 0x6f
  val saveStatus = Seq(csrSwap(8), 0x20437, csr(8, 0x300, 8, 3), csr(0, 0x7b3, 8, 1))
  val restoreStatus = Seq(csr(8, 0x7b3, 0, 2), csr(0, 0x300, 8, 1), csrSwap(8))
  val entry = saveStatus ++ Seq(0x417, store(halted - 16), 0x417, load(8, flags - 24),
    branch(-8), 0xfff40413, branch(12), csrSwap(8), jump(access - 48)) ++ restoreStatus ++ Seq(0x7b200073)
  val handler = saveStatus ++ Seq(0x417, store(failed - exception - 16)) ++ restoreStatus ++ Seq(0x00100073)

@generator
object DitDahA1DebugModule extends Generator[DitDahA1Parameter, DitDahA1UnitLayers, DitDahA1DebugModuleIO, DitDahA1UnitProbe]:
  override def moduleName(parameter: DitDahA1Parameter): String = "DitDahA1DebugModule"
  def architecture(parameter: DitDahA1Parameter) =
    require(parameter.enableJtag && parameter.debugBase.nonEmpty, "Debug module requires a dedicated memory window")
    val io = summon[Interface[DitDahA1DebugModuleIO]]
    given ClockScope = ClockScope.posedge(io.clock)
    given ResetScope = ResetScope.syncActiveHigh(io.reset)
    val active = RegInit(false.B)
    val ndmreset = RegInit(false.B)
    val selectBits = math.max(1, 32 - Integer.numberOfLeadingZeros(parameter.hartCount - 1))
    val selected = RegInit(0.U(selectBits))
    val halt = Seq.fill(parameter.hartCount)(RegInit(false.B))
    val resume = Seq.fill(parameter.hartCount)(RegInit(false.B))
    val acknowledged = Seq.fill(parameter.hartCount)(RegInit(false.B))
    val haveReset = Seq.fill(parameter.hartCount)(RegInit(true.B))
    val data = RegInit(0.U(64))
    val program = Seq.fill(8)(RegInit(0.U(32)))
    val command = RegInit(0.U(32))
    val autoexec = RegInit(false.B)
    val owner = RegInit(0.U(selectBits))
    val busy = RegInit(false.B)
    val started = RegInit(false.B)
    val error = RegInit(0.U(3))
    val base = parameter.debugBase.get
    io.ndmreset := ndmreset
    for n <- 0 until parameter.hartCount do
      io.harts(n).haltReq := active & halt(n)
      io.harts(n).entryPc := base.U(64)
      io.harts(n).exceptionPc := (base + DebugProgram.exception).U(64)
      when(resume(n) & !io.harts(n).mode & !io.hartsReset) { resume(n) := false.B; acknowledged(n) := true.B }
      when(io.hartsReset) { haveReset(n) := true.B; resume(n) := false.B; acknowledged(n) := false.B }
    val exists = selected < parameter.hartCount.U(selectBits + 1)
    val halted = (0 until parameter.hartCount).map(n => (selected === n.U(selectBits)) & io.harts(n).mode).reduce(_ | _)
    val ack = (0 until parameter.hartCount).map(n => (selected === n.U(selectBits)) & acknowledged(n)).reduce(_ | _)
    val resetSeen = (0 until parameter.hartCount).map(n => (selected === n.U(selectBits)) & haveReset(n)).reduce(_ | _)
    val unavailable = exists & io.hartsReset
    val running = exists & !io.hartsReset & !halted
    val stopped = exists & !io.hartsReset & halted
    val status = 0.B(12) ## resetSeen.asBits ## resetSeen.asBits ##
      ack.asBits ## ack.asBits ## (!exists).asBits ## (!exists).asBits ## unavailable.asBits ## unavailable.asBits ##
      running.asBits ## running.asBits ## stopped.asBits ## stopped.asBits ## 0x83.B(8)
    val request = io.dmi.request
    val replyValid = RegInit(false.B)
    val replyData = Reg(UInt(32))
    val replyStatus = Reg(UInt(2))
    request.ready := !replyValid
    io.dmi.response.valid := replyValid
    io.dmi.response.bits.data := replyData
    io.dmi.response.bits.status := replyStatus
    val access = request.valid & request.ready
    val writing = access & (request.bits.op === 2.U(2))
    val address = request.bits.address
    val value = request.bits.data
    val controlWrite = writing & (address === 0x10.U(7))
    val stateAccess = ((address >= 4.U(7)) & (address < 6.U(7))) | ((address >= 0x20.U(7)) & (address < 0x28.U(7)))
    val readData = Wire(UInt(32))
    readData := 0.U(32)
    when(address === 0x10.U(7)) { readData := (0.B(16 - selectBits) ## selected.asBits ## 0.B(14) ## ndmreset.asBits ## active.asBits).asUInt }
    when(address === 0x11.U(7)) { readData := status.asUInt }
    when(address === 0x16.U(7)) { readData := (8.B(8) ## 0.B(11) ## busy.asBits ## 0.B(1) ## error.asBits ## 2.B(8)).asUInt }
    when(address === 0x17.U(7)) { readData := command }
    when(address === 0x18.U(7)) { readData := autoexec.?(1.U(32), 0.U(32)) }
    for n <- 0 until 2 do when(address === (4 + n).U(7)) { readData := data.asBits.bits(32 * n + 31, 32 * n).asUInt }
    for n <- 0 until 8 do when(address === (0x20 + n).U(7)) { readData := program(n) }
    when(io.dmi.response.valid & io.dmi.response.ready) { replyValid := false.B }
    when(access) {
      replyValid := true.B
      replyData := readData
      replyStatus := ((request.bits.op === 1.U(2)) | (request.bits.op === 2.U(2))).?(0.U(2), 2.U(2))
    }
    val blockedAccess = active & access & busy & (stateAccess | writing & ((address === 0x16.U(7)) | (address === 0x17.U(7)) | (address === 0x18.U(7))))
    when(blockedAccess & (error === 0.U(3))) { error := 1.U(3) }
    when(controlWrite) {
      active := value.asBits.bit(0)
      when(active & value.asBits.bit(0)) {
        ndmreset := value.asBits.bit(1)
        when(!busy) {
          val nextSelected = if parameter.hartCount == 1 then 0.U(selectBits) else value.asBits.bits(16 + selectBits - 1, 16).asUInt
          selected := nextSelected
          for n <- 0 until parameter.hartCount do when(nextSelected === n.U(selectBits)) {
            halt(n) := value.asBits.bit(31)
            when(value.asBits.bit(30) & !value.asBits.bit(31) & !io.hartsReset) { resume(n) := true.B; acknowledged(n) := false.B }
            when(value.asBits.bit(28) & !io.hartsReset) { haveReset(n) := false.B }
          }
        }
      }
    }
    when(active & !busy & writing) {
      for n <- 0 until 2 do when(address === (4 + n).U(7)) {
        data := (if n == 0 then data.asBits.bits(63, 32) ## value.asBits else value.asBits ## data.asBits.bits(31, 0)).asUInt
      }
      for n <- 0 until 8 do when(address === (0x20 + n).U(7)) { program(n) := value }
      when(address === 0x18.U(7)) { autoexec := value.asBits.bit(0) }
      when(address === 0x16.U(7)) { error := (error.asBits & ~value.asBits.bits(10, 8)).asUInt }
    }
    val commandWrite = writing & (address === 0x17.U(7))
    val repeatCommand = autoexec & access & (address === 4.U(7)) &
      ((request.bits.op === 1.U(2)) | (request.bits.op === 2.U(2)))
    when(active & !busy & (commandWrite | repeatCommand) & (error === 0.U(3))) {
      val nextCommand = commandWrite.?(value, command)
      val bits = nextCommand.asBits
      val size = bits.bits(22, 20).asUInt
      val unsupported = (bits.bits(31, 23) =/= 0.B(9)) | bits.bit(19) | (bits.bit(17) &
        ((bits.bits(15, 5) =/= 0x80.B(11)) | ((size =/= 2.U(3)) & (size =/= 3.U(3))) | (bits.bit(16) & (size =/= 3.U(3)))))
      command := nextCommand
      when(unsupported) { error := 2.U(3) }.otherwise {
        when(!exists | !halted | io.hartsReset) { error := 4.U(3) }.otherwise {
          busy := true.B; started := false.B; owner := selected
        }
      }
    }
    val memory = io.memory
    val pending = RegInit(false.B)
    val memoryData = Reg(UInt(64))
    val memoryFault = Reg(Bool())
    val tag = Reg(UInt(8))
    memory.request.ready := (!pending | memory.response.ready) & !io.hartsReset
    memory.response.valid := pending
    memory.response.bits.data := memoryData
    memory.response.bits.fault := memoryFault
    memory.response.bits.tag := tag
    memory.response.bits.last := true.B
    val m = memory.request.bits
    val offset = (m.address - base.U(64)).asBits.bits(11, 0).asUInt
    val sameHart = io.memoryHart === owner
    val commandBits = command.asBits
    val transfer = commandBits.bit(17)
    val target = commandBits.bits(4, 0)
    val helper = (target === 8.B(5)).?(9.B(5), 8.B(5))
    val swap = (0x7b2.B(12) ## helper ## 1.B(3) ## helper ## 0x73.B(7)).asUInt
    val size = (commandBits.bits(22, 20) === 2.B(3)).?(2.B(3), 3.B(3))
    val dataOffset = DebugProgram.data - DebugProgram.access - 4
    val load = (dataOffset.B(12) ## helper ## 3.B(3) ## target ## 3.B(7)).asUInt
    val store = ((dataOffset >> 5).B(7) ## target ## helper ## size ## (dataOffset & 31).B(5) ## 0x23.B(7)).asUInt
    val generated = Seq(transfer.?(swap, 0x13.U(32)), transfer.?((0.B(20) ## helper ## 0x17.B(7)).asUInt, 0x13.U(32)),
      transfer.?(commandBits.bit(16).?(load, store), 0x13.U(32)), transfer.?(swap, 0x13.U(32))) ++
      (Seq(DebugProgram.csrSwap(8)) ++ DebugProgram.restoreStatus).map(v => (v.toLong & 0xffffffffL).U(32)) ++
      Seq(commandBits.bit(18).?(DebugProgram.jump(DebugProgram.program - DebugProgram.access - 32).U(32), 0x13.U(32)), 0x00100073.U(32))
    val words = DebugProgram.entry.zipWithIndex.map((v, n) => (4 * n, (v.toLong & 0xffffffffL).U(32))) ++
      DebugProgram.handler.zipWithIndex.map((v, n) => (DebugProgram.exception + 4 * n, (v.toLong & 0xffffffffL).U(32))) ++
      generated.zipWithIndex.map((v, n) => (DebugProgram.access + 4 * n, v)) ++
      program.zipWithIndex.map((v, n) => (DebugProgram.program + 4 * n, v))
    def wordAt(location: Referable[UInt])(using Arena, Context, Block, InstanceContext): Referable[UInt] =
      val out = Wire(UInt(32))
      out := 0.U(32)
      for (address, value) <- words do when(location === address.U(12)) { out := value }
      out
    val wordAddress = (offset.asBits.bits(11, 2) ## 0.B(2)).asUInt
    val pair = wordAt((wordAddress + 4.U(12)).asBits.bits(11, 0).asUInt).asBits ## wordAt(wordAddress).asBits
    val readValue = Wire(UInt(64))
    readValue := pair.asUInt >> (offset.asBits.bits(1, 0).asUInt << 3)
    val dataHit = (offset >= DebugProgram.data.U(12)) & (offset < (DebugProgram.data + 8).U(12))
    val flagsHit = offset === DebugProgram.flags.U(12)
    val flags = Wire(UInt(32))
    flags := 0.U(32)
    for n <- 0 until parameter.hartCount do when(io.memoryHart === n.U(4)) {
      flags := (busy & !started & sameHart).?(2.U(32), resume(n).?(1.U(32), 0.U(32)))
    }
    when(flagsHit) { readValue := flags }
    val shift = offset.asBits.bits(2, 0).asUInt << 3
    when(dataHit) { readValue := data >> shift }
    val codeHit = words.map((address, _) => wordAddress === address.U(12)).reduce(_ | _)
    val allowed = Wire(Bool())
    allowed := false.B
    for size <- 0 to 3 do
      val bytes = 1 << size
      val aligned = if size == 0 then true.B else offset.asBits.bits(size - 1, 0) === 0.B(size)
      val mask = (m.mask =/= 0.U(8)) & ((m.mask.asBits & (255 ^ ((1 << bytes) - 1)).B(8)) === 0.B(8))
      val registerData = dataHit & (offset <= (DebugProgram.data + 8 - bytes).U(12)) & busy & sameHart
      val notification = (offset === DebugProgram.halted.U(12)) | (offset === DebugProgram.failed.U(12))
      when((m.size === size.U(3)) & aligned) {
        allowed := m.write.?(mask & !m.fetch & (registerData | (size == 2).B & notification),
          registerData & !m.fetch | flagsHit & !m.fetch & (size <= 2).B | codeHit & (size <= 2).B)
      }
    val authorized = m.debug.get & (io.memoryHart < parameter.hartCount.U(5)) &
      (m.address >= base.U(64)) & (m.address < (base + 4096).U(64)) & !m.atomic & (m.cacheOperation === 0.U(2))
    val accepted = memory.request.valid & memory.request.ready
    when(memory.response.valid & memory.response.ready) { pending := false.B }
    when(accepted) {
      pending := true.B; memoryData := readValue; memoryFault := !authorized | !allowed; tag := m.tag
      when(authorized & allowed) {
        when(!m.write & flagsHit & busy & !started & sameHart) { started := true.B }
        when(m.write & dataHit) {
          val expanded = (0 until 8).reverse.map(n => m.mask.asBits.bit(n).?(255.B(8), 0.B(8))).reduce(_ ## _)
          val mask = (expanded.asUInt << shift).asBits.bits(63, 0)
          data := ((data.asBits & ~mask) | ((m.data << shift).asBits.bits(63, 0) & mask)).asUInt
        }
        when(m.write & (offset === DebugProgram.failed.U(12)) & busy & sameHart & (error === 0.U(3)) & !blockedAccess) { error := 3.U(3) }
        when(m.write & (offset === DebugProgram.halted.U(12)) & busy & started & sameHart) { busy := false.B; started := false.B }
      }
    }
    when(io.hartsReset) {
      pending := false.B; busy := false.B; started := false.B
      when(busy & (error === 0.U(3))) { error := 4.U(3) }
    }
    when(!active | controlWrite & !value.asBits.bit(0)) {
      ndmreset := false.B; selected := 0.U(selectBits); data := 0.U(64); command := 0.U(32); autoexec := false.B
      busy := false.B; started := false.B; error := 0.U(3)
      for n <- 0 until parameter.hartCount do { halt(n) := false.B; resume(n) := false.B; acknowledged(n) := false.B }
      for word <- program do word := 0.U(32)
    }
