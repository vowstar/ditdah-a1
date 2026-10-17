# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Instruction-level oracle for the implemented scalar operations."""

MASK = (1 << 64) - 1


def signed(value, bits):
    return (value & ((1 << (bits - 1)) - 1)) - (value & (1 << (bits - 1)))


def pmp_allowed(configs, addresses, address, size, kind, pa):
    if address < 0 or address + size > 1 << pa:
        return False
    for index, config in enumerate(configs):
        mode = (config >> 3) & 3
        if not mode:
            continue
        if mode == 1:
            low, high = (addresses[index - 1] * 4 if index else 0), addresses[index] * 4
        else:
            width = 4
            if mode == 3:
                width, value = 8, addresses[index]
                while value & 1:
                    width *= 2
                    value >>= 1
            low = addresses[index] * 4 & -width
            high = low + width
        matches = [low <= byte < high for byte in range(address, address + size)]
        if any(matches):
            return all(matches) and (not config & 128 or bool(config & {'fetch': 4, 'read': 1, 'write': 2}[kind]))
    return True


class Fault(Exception):
    def __init__(self, cause, value):
        self.cause, self.value = cause, value


class Model:
    def __init__(self, config, memory, faults, hart_id=0, access=None):
        self.config = config
        self.memory = dict(memory)
        self.faults = faults
        self.external_access = access
        self.pc = int(config['resetVector'])
        self.registers = [0] * 32
        self.csrs = {address: 0 for address in (0x300, 0x301, 0x304, 0x305, 0x340,
                                               0x341, 0x342, 0x343, 0x344,
                                               0xf11, 0xf12, 0xf13, 0xf14)}
        self.csrs[0x300] = 0x1800
        self.csrs[0xf14] = hart_id
        if config['pmpEntries']:
            self.csrs.update({address: 0 for address in (*range(0x3a0, 0x3b0, 2), *range(0x3b0, 0x3f0))})
        self.local_fetch_faults = set()
        self.bus = []
        self.requests = []
        self.order = 0

    def access(self, address, size, kind, data=0):
        cause = {'fetch': 1, 'read': 5, 'write': 7}[kind]
        if address % size:
            raise Fault({'fetch': 0, 'read': 4, 'write': 6}[kind], address)
        if self.config['pmpEntries'] and not pmp_allowed(
                [self.pmp_config(i) for i in range(self.config['pmpEntries'])],
                [self.csrs[0x3b0 + i] for i in range(self.config['pmpEntries'])],
                address, size, kind, self.config['physicalAddressBits']):
            if kind == 'fetch':
                self.local_fetch_faults.add(self.order)
            raise Fault(cause, address)
        self.requests.append((kind, address, size, data if kind == 'write' else 0))
        permission = {'fetch': 'executable', 'read': 'readable', 'write': 'writable'}[kind]
        allowed = any(int(r['base']) <= address and address + size <= int(r['base']) + int(r['size'])
                      and r[permission] for r in self.config['memoryRegions'])
        if not allowed:
            raise Fault(cause, address)
        self.bus.append((kind, address, size, data if kind == 'write' else 0))
        if kind != 'fetch' and self.external_access is not None:
            return self.external_access(address, size, kind, data)
        if address == self.faults.get(kind):
            raise Fault(cause, address)
        if kind == 'write':
            for i in range(size):
                self.memory[address + i] = (data >> (8 * i)) & 255
            return 0
        return sum(self.memory.get(address + i, 0) << (8 * i) for i in range(size))

    def set_interrupts(self, levels):
        self.csrs[0x344] = sum(((levels >> index) & 1) << bit for index, bit in enumerate((3, 7, 11)))

    def interrupt_cause(self):
        pending = self.csrs[0x304] & self.csrs[0x344] if self.csrs[0x300] & 8 else 0
        return next(((1 << 63) | bit for bit in (11, 3, 7) if pending & (1 << bit)), 0)

    def interrupt(self):
        cause = self.interrupt_cause()
        assert cause, 'Interrupt without independently eligible source'
        pc, target = self.pc, self.csrs[0x305]
        self.csrs[0x341], self.csrs[0x342], self.csrs[0x343] = pc, cause, 0
        self.csrs[0x300] = 0x1800 | ((self.csrs[0x300] & 8) << 4)
        self.pc = target
        record = (self.order, pc, 0, target, 0, 0, 0, 1, cause, 0)
        self.order += 1
        return record

    def pmp_config(self, index):
        return (self.csrs[0x3a0 + (index // 8) * 2] >> ((index % 8) * 8)) & 255

    def write_csr(self, address, value):
        if address == 0x300:
            self.csrs[address] = 0x1800 | (value & 0x88)
        elif address == 0x304 and self.config.get('enableInterrupts', False):
            self.csrs[address] = value & 0x888
        elif address in (0x305, 0x341):
            self.csrs[address] = value & ~3
        elif address in (0x340, 0x342, 0x343):
            self.csrs[address] = value
        elif 0x3a0 <= address < 0x3b0:
            for slot in range(8):
                index = (address - 0x3a0) * 4 + slot
                if index < self.config['pmpEntries'] and not self.pmp_config(index) & 128:
                    field = (value >> (slot * 8)) & 0x9f
                    if not field & 1:
                        field &= ~2
                    self.csrs[address] = (self.csrs[address] & ~(255 << (slot * 8))) | (field << (slot * 8))
        elif 0x3b0 <= address < 0x3f0:
            index = address - 0x3b0
            if index < self.config['pmpEntries']:
                locked = self.pmp_config(index) & 128
                if index + 1 < self.config['pmpEntries']:
                    locked |= (self.pmp_config(index + 1) & 0x98) == 0x88
                if not locked:
                    self.csrs[address] = value & ((1 << (self.config['physicalAddressBits'] - 2)) - 1)

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
