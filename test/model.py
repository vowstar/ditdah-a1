# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Instruction-level oracle for the implemented scalar operations."""

MASK = (1 << 64) - 1


def signed(value, bits):
    return (value & ((1 << (bits - 1)) - 1)) - (value & (1 << (bits - 1)))


def atomic_value(operation, old, operand, size):
    assert size == 8 and operation in (0, 1, 8)
    return {0: old + operand, 1: operand, 8: old | operand}[operation] & MASK


class ExclusiveMonitor:
    def __init__(self):
        self.reservations = {}

    def reserve(self, owner, address, size):
        self.reservations[owner] = address, size

    def write(self, address, size):
        self.reservations = {owner: (base, length) for owner, (base, length) in self.reservations.items()
                             if address + size <= base or base + length <= address}

    def conditional(self, owner, address, size):
        success = self.reservations.pop(owner, None) == (address, size)
        if success:
            self.write(address, size)
        return success


def integer_value(insn, a, b):
    opcode, function, upper = insn & 127, (insn >> 12) & 7, insn >> 25
    word, immediate = opcode in (0x1b, 0x3b), opcode in (0x13, 0x1b)
    width = 32 if word else 64
    left, right = a & ((1 << width) - 1), signed(insn >> 20, 12) & MASK if immediate else b
    shift = (insn >> 20 if immediate else b) & (width - 1)
    if function == 0 and (immediate or upper in (0, 32)):
        value = left - right if not immediate and upper == 32 else left + right
    elif not immediate and opcode == 0x33 and function == 0 and upper == 1:
        value = a * b
    elif function in (1, 5):
        prefix = insn >> (25 if word or not immediate else 26)
        arithmetic = prefix == (32 if word or not immediate else 16)
        if prefix != 0 and not (function == 5 and arithmetic):
            raise Fault(2, insn)
        value = left << shift if function == 1 else signed(left, width) >> shift if arithmetic else left >> shift
    elif not word and (immediate or upper == 0) and function in (2, 3, 4, 6, 7):
        value = {2: int(signed(a, 64) < signed(right, 64)), 3: int(a < right),
                 4: a ^ right, 6: a | right, 7: a & right}[function]
    else:
        raise Fault(2, insn)
    return signed(value, 32) if word else value & MASK


def pmp_allowed(configs, addresses, address, size, kind, pa, privilege=3):
    permission = {'fetch': 4, 'read': 1, 'write': 2, 'atomic': 3}[kind]
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
            return all(matches) and (privilege == 3 and not config & 128 or config & permission == permission)
    return privilege == 3 or not configs


class Fault(Exception):
    def __init__(self, cause, value):
        self.cause, self.value = cause, value


class LocalInterrupts:
    def __init__(self, base, harts):
        self.base, self.harts = base, harts
        self.time, self.software, self.compare = 0, [0] * harts, [MASK] * harts
        self.cycle, self.tick, self.time_written = -1, False, False

    def begin_cycle(self, cycle, tick):
        assert cycle == self.cycle + 1, 'Missing or repeated platform cycle'
        if self.tick and not self.time_written:
            self.time = (self.time + 1) & MASK
        self.cycle, self.tick, self.time_written = cycle, bool(tick), False

    def levels(self, hart):
        return self.software[hart] | (int(self.time >= self.compare[hart]) << 1)

    def access(self, address, size, kind, data):
        offset = address - self.base
        if kind not in ('read', 'write'):
            raise Fault(7, address)
        if size == 4 and offset % 4 == 0 and 0 <= offset < 4 * self.harts:
            index, registers = offset // 4, self.software
            value = registers[index]
            if kind == 'write':
                registers[index] = data & 1
        elif size == 8 and offset % 8 == 0 and 0x4000 <= offset < 0x4000 + 8 * self.harts:
            index, registers = (offset - 0x4000) // 8, self.compare
            value = registers[index]
            if kind == 'write':
                registers[index] = data & MASK
        elif size == 8 and offset == 0xbff8:
            value = self.time
            if kind == 'write':
                self.time, self.time_written = data & MASK, True
        else:
            raise Fault(5 if kind == 'read' else 7, address)
        return 0 if kind == 'write' else value


class Model:
    def __init__(self, config, memory, faults, hart_id=0, access=None):
        self.config = config
        self.memory = dict(memory)
        self.faults = faults
        self.external_access = access
        self.monitor = ExclusiveMonitor()
        self.local_reservation = None
        self.atomic_operation, self.sc_eligible = 0, False
        self.pc = int(config['resetVector'])
        self.privilege = 3
        self.registers = [0] * 32
        self.csrs = {address: 0 for address in (0x300, 0x301, 0x304, 0x305, 0x340,
                                               0x341, 0x342, 0x343, 0x344,
                                               0xf11, 0xf12, 0xf13, 0xf14, 0xf15)}
        if config.get('enableUserMode'):
            self.csrs.update({0x306: 0, 0x30a: 0})
        self.csrs[0x300] = 2 << 32 if config.get('enableUserMode') else 0x1800
        self.csrs[0xf14] = hart_id
        if config['pmpEntries']:
            self.csrs.update({address: 0 for address in (*range(0x3a0, 0x3b0, 2), *range(0x3b0, 0x3f0))})
        self.local_fetch_faults = set()
        self.bus = []
        self.requests = []
        self.request_privileges = []
        self.order = 0

    def access(self, address, size, kind, data=0):
        permission_kind = {2: 'read', 3: 'write'}.get(self.atomic_operation, 'atomic') if kind == 'atomic' else kind
        cause = {'fetch': 1, 'read': 5, 'write': 7, 'atomic': 7}[permission_kind]
        data &= (1 << (8 * size)) - 1
        if address % size:
            raise Fault({'fetch': 0, 'read': 4, 'write': 6, 'atomic': 6}[permission_kind], address)
        if self.config['pmpEntries'] and not pmp_allowed(
                [self.pmp_config(i) for i in range(self.config['pmpEntries'])],
                [self.csrs[0x3b0 + i] for i in range(self.config['pmpEntries'])],
                address, size, permission_kind, self.config['physicalAddressBits'],
                self.privilege if kind == 'fetch' else self.data_privilege()):
            if kind == 'fetch':
                self.local_fetch_faults.add(self.order)
            raise Fault(cause, address)
        self.requests.append((kind, address, size, data if kind in ('write', 'atomic') else 0))
        self.request_privileges.append(self.privilege if kind == 'fetch' else self.data_privilege())
        permission = {'fetch': 'executable', 'read': 'readable', 'write': 'writable', 'atomic': 'atomic'}[kind]
        allowed = any(int(r['base']) <= address and address + size <= int(r['base']) + int(r['size'])
                      and r.get(permission, False) and (kind != 'atomic' or (r['readable'] and r['writable'] and not r['device']))
                      for r in self.config['memoryRegions'])
        if not allowed:
            raise Fault(cause, address)
        self.bus.append((kind, address, size, data if kind in ('write', 'atomic') else 0))
        if kind != 'fetch' and self.external_access is not None:
            return self.external_access(address, size, kind, data)
        if kind == 'atomic' and self.atomic_operation == 3 and not self.sc_eligible:
            return 1
        stages = ('read', 'exclusive') if self.atomic_operation == 2 else ('write',) if self.atomic_operation == 3 else ('read', 'write', 'exclusive')
        if address == self.faults.get(kind) or (kind == 'atomic' and address in [self.faults.get(k) for k in stages]):
            raise Fault(cause, address)
        old = sum(self.memory.get(address + i, 0) << (8 * i) for i in range(size))
        if kind == 'atomic':
            if self.atomic_operation == 2:
                self.monitor.reserve(self.csrs[0xf14], address, size)
                return old
            if self.atomic_operation == 3:
                if not self.monitor.conditional(self.csrs[0xf14], address, size):
                    return 1
            else:
                data = atomic_value(self.atomic_operation, old, data, size)
        if kind in ('write', 'atomic'):
            self.monitor.write(address, size)
            for i in range(size):
                self.memory[address + i] = (data >> (8 * i)) & 255
            return old if kind == 'atomic' and self.atomic_operation != 3 else 0
        return old

    def set_interrupts(self, levels):
        self.csrs[0x344] = sum(((levels >> index) & 1) << bit for index, bit in enumerate((3, 7, 11)))

    def interrupt_cause(self):
        pending = self.csrs[0x304] & self.csrs[0x344] if self.privilege < 3 or self.csrs[0x300] & 8 else 0
        return next(((1 << 63) | bit for bit in (11, 3, 7) if pending & (1 << bit)), 0)

    def data_privilege(self):
        return (self.csrs[0x300] >> 11) & 3 if self.csrs[0x300] & (1 << 17) else self.privilege

    def trap(self, pc, cause, value):
        self.csrs[0x341], self.csrs[0x342], self.csrs[0x343] = pc & ~3, cause, value
        status = self.csrs[0x300]
        self.csrs[0x300] = (status & ~0x1888) | (self.privilege << 11) | ((status & 8) << 4)
        self.privilege = 3

    def interrupt(self):
        cause = self.interrupt_cause()
        assert cause, 'Interrupt without independently eligible source'
        pc, target = self.pc, self.csrs[0x305]
        self.trap(pc, cause, 0)
        self.pc = target
        record = (self.order, pc, 0, target, 0, 0, 0, 1, cause, 0)
        self.order += 1
        return record

    def pmp_config(self, index):
        return (self.csrs[0x3a0 + (index // 8) * 2] >> ((index % 8) * 8)) & 255

    def write_csr(self, address, value):
        if address == 0x300:
            self.csrs[address] = ((2 << 32) | (value & 0x220088) | (0x1800 if value & 0x1800 == 0x1800 else 0)
                                  if self.config.get('enableUserMode') else 0x1800 | (value & 0x88))
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
            elif opcode in (0x13, 0x1b, 0x33, 0x3b):
                value, write = integer_value(insn, a, b), True
            elif opcode == 0x63 and funct3 in (0, 1, 4, 5, 6, 7):
                displacement = signed(((insn >> 31) << 12) | (((insn >> 7) & 1) << 11)
                                      | (((insn >> 25) & 63) << 5) | (((insn >> 8) & 15) << 1), 13)
                taken = {0: a == b, 1: a != b, 4: signed(a, 64) < signed(b, 64),
                         5: signed(a, 64) >= signed(b, 64), 6: a < b, 7: a >= b}[funct3]
                if taken:
                    next_pc = (pc + displacement) & MASK
            elif opcode == 0x6f:
                displacement = signed(((insn >> 31) << 20) | (((insn >> 12) & 255) << 12)
                                      | (((insn >> 20) & 1) << 11) | (((insn >> 21) & 1023) << 1), 21)
                value, write, next_pc = pc + 4, True, (pc + displacement) & MASK
            elif opcode == 0x67 and funct3 == 0:
                value, write, next_pc = pc + 4, True, ((a + immediate) & MASK) & ~1
            elif opcode == 0x03 and funct3 != 7:
                size = 1 << (funct3 & 3)
                value = self.access((a + immediate) & MASK, size, 'read')
                value, write = signed(value, size * 8) if funct3 < 4 else value, True
            elif opcode == 0x23 and funct3 < 4:
                offset = signed(((insn >> 25) << 5) | ((insn >> 7) & 31), 12)
                self.access((a + offset) & MASK, 1 << funct3, 'write', b)
            elif opcode == 0x2f and funct3 == 3 and insn >> 27 in (0, 1, 2, 3, 8) and (insn >> 27 != 2 or rs2 == 0):
                self.atomic_operation = insn >> 27
                self.sc_eligible = self.atomic_operation == 3 and self.local_reservation == (a, 8)
                self.local_reservation = None
                value, write = self.access(a, 8, 'atomic', b), True
                if self.atomic_operation == 2:
                    self.local_reservation = a, 8
            elif opcode == 0x0f and funct3 in (0, 1):
                pass
            elif insn == 0x10500073:
                if self.privilege < 3 and self.csrs[0x300] & (1 << 21):
                    raise Fault(2, insn)
            elif opcode == 0x73 and funct3 in (1, 2, 3, 5, 6, 7):
                address = insn >> 20
                update = funct3 & 3 == 1 or rs1 != 0
                source = rs1 if funct3 & 4 else a
                if address not in self.csrs or (address >> 8) & 3 > self.privilege or (update and address >> 10 == 3):
                    raise Fault(2, insn)
                value, write = self.csrs[address], True
                if update:
                    data = source if funct3 & 3 == 1 else value | source if funct3 & 3 == 2 else value & ~source
                    self.write_csr(address, data & MASK)
            elif insn == 0x73:
                raise Fault(8 if self.privilege == 0 else 11, 0)
            elif insn == 0x30200073:
                if self.privilege != 3:
                    raise Fault(2, insn)
                next_pc = self.csrs[0x341]
                status = self.csrs[0x300]
                self.privilege = (status >> 11) & 3
                self.csrs[0x300] = (status & ~0x1888) | 0x80 | ((status >> 4) & 8)
                if self.config.get('enableUserMode'):
                    if self.privilege < 3:
                        self.csrs[0x300] &= ~(1 << 17)
                else:
                    self.csrs[0x300] |= 0x1800
            else:
                raise Fault(2, insn)
            if next_pc & 3:
                raise Fault(0, next_pc)
        except Fault as error:
            trap, cause, tval, write = True, error.cause, error.value, False
            self.trap(pc, cause, tval)
            next_pc = self.csrs[0x305]
        write = write and rd != 0
        value = (value & MASK) if write else 0
        if write:
            self.registers[rd] = value
        self.pc = next_pc
        record = (self.order, pc, insn, next_pc, rd, int(write), value, int(trap), cause, tval)
        self.order += 1
        return record
