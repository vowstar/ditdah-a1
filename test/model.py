# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Instruction-level oracle for the implemented scalar operations."""

MASK = (1 << 64) - 1


def signed(value, bits):
    return (value & ((1 << (bits - 1)) - 1)) - (value & (1 << (bits - 1)))


class Fault(Exception):
    def __init__(self, cause, value):
        self.cause, self.value = cause, value


class Model:
    def __init__(self, config, memory, faults):
        self.config = config
        self.memory = dict(memory)
        self.faults = faults
        self.pc = int(config['resetVector'])
        self.registers = [0] * 32
        self.csrs = {address: 0 for address in (0x300, 0x301, 0x304, 0x305, 0x340,
                                               0x341, 0x342, 0x343, 0x344,
                                               0xf11, 0xf12, 0xf13, 0xf14)}
        self.csrs[0x300] = 0x1800
        self.bus = []
        self.requests = []
        self.order = 0

    def access(self, address, size, kind, data=0):
        cause = {'fetch': 1, 'read': 5, 'write': 7}[kind]
        if address % size:
            raise Fault({'fetch': 0, 'read': 4, 'write': 6}[kind], address)
        self.requests.append((kind, address, size, data if kind == 'write' else 0))
        permission = {'fetch': 'executable', 'read': 'readable', 'write': 'writable'}[kind]
        allowed = any(int(r['base']) <= address and address + size <= int(r['base']) + int(r['size'])
                      and r[permission] for r in self.config['memoryRegions'])
        if not allowed:
            raise Fault(cause, address)
        self.bus.append((kind, address, size, data if kind == 'write' else 0))
        if address == self.faults.get(kind):
            raise Fault(cause, address)
        if kind == 'write':
            for i in range(size):
                self.memory[address + i] = (data >> (8 * i)) & 255
            return 0
        return sum(self.memory.get(address + i, 0) << (8 * i) for i in range(size))

    def write_csr(self, address, value):
        if address == 0x300:
            self.csrs[address] = 0x1800 | (value & 0x88)
        elif address in (0x305, 0x341):
            self.csrs[address] = value & ~3
        elif address in (0x340, 0x342, 0x343):
            self.csrs[address] = value

    def step(self):
        pc, insn = self.pc, 0
        next_pc = (pc + 4) & MASK
        rd, write, value, trap, cause, tval = 0, False, 0, False, 0, 0
        try:
            insn = self.access(pc, 4, 'fetch')
            opcode, rd, funct3 = insn & 127, (insn >> 7) & 31, (insn >> 12) & 7
            rs1, rs2 = (insn >> 15) & 31, (insn >> 20) & 31
            a, b = self.registers[rs1], self.registers[rs2]
            immediate = signed(insn >> 20, 12)
            if opcode == 0x37:
                value, write = signed(insn & 0xfffff000, 32), True
            elif opcode == 0x17:
                value, write = pc + signed(insn & 0xfffff000, 32), True
            elif opcode == 0x13 and funct3 == 0:
                value, write = a + immediate, True
            elif opcode == 0x33 and funct3 == 0 and insn >> 25 == 0:
                value, write = a + b, True
            elif opcode == 0x33 and funct3 == 0 and insn >> 25 == 1:
                value, write = a * b, True
            elif opcode == 0x63 and funct3 == 0:
                displacement = signed(((insn >> 31) << 12) | (((insn >> 7) & 1) << 11)
                                      | (((insn >> 25) & 63) << 5) | (((insn >> 8) & 15) << 1), 13)
                if a == b:
                    next_pc = (pc + displacement) & MASK
            elif opcode == 0x6f:
                displacement = signed(((insn >> 31) << 20) | (((insn >> 12) & 255) << 12)
                                      | (((insn >> 20) & 1) << 11) | (((insn >> 21) & 1023) << 1), 21)
                value, write, next_pc = pc + 4, True, (pc + displacement) & MASK
            elif opcode == 0x67 and funct3 == 0:
                value, write, next_pc = pc + 4, True, ((a + immediate) & MASK) & ~1
            elif opcode == 0x03 and funct3 == 3:
                value, write = self.access((a + immediate) & MASK, 8, 'read'), True
            elif opcode == 0x23 and funct3 == 3:
                offset = signed(((insn >> 25) << 5) | ((insn >> 7) & 31), 12)
                self.access((a + offset) & MASK, 8, 'write', b)
            elif opcode == 0x73 and funct3 in (1, 2):
                address = insn >> 20
                update = funct3 == 1 or rs1 != 0
                if address not in self.csrs or (update and address >> 10 == 3):
                    raise Fault(2, insn)
                value, write = self.csrs[address], True
                if update:
                    self.write_csr(address, a if funct3 == 1 else value | a)
            elif insn == 0x73:
                raise Fault(11, 0)
            elif insn == 0x30200073:
                next_pc = self.csrs[0x341]
                self.csrs[0x300] = 0x1880 | ((self.csrs[0x300] >> 4) & 8)
            else:
                raise Fault(2, insn)
            if next_pc & 3:
                raise Fault(0, next_pc)
        except Fault as error:
            trap, cause, tval, write = True, error.cause, error.value, False
            self.csrs[0x341], self.csrs[0x342], self.csrs[0x343] = pc & ~3, cause, tval
            self.csrs[0x300] = 0x1800 | ((self.csrs[0x300] & 8) << 4)
            next_pc = self.csrs[0x305]
        write = write and rd != 0
        value = (value & MASK) if write else 0
        if write:
            self.registers[rd] = value
        self.pc = next_pc
        record = (self.order, pc, insn, next_pc, rd, int(write), value, int(trap), cause, tval)
        self.order += 1
        return record
