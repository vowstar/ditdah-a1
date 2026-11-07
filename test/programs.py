# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Generate instruction streams and memory images at test runtime."""

import random
from copy import deepcopy


def addi(rd, rs, imm):
    return ((imm & 4095) << 20) | (rs << 15) | (rd << 7) | 0x13


def add(rd, a, b):
    return (b << 20) | (a << 15) | (rd << 7) | 0x33


def mul(rd, a, b):
    return muldiv(rd, a, b)


def muldiv(rd, a, b, function=0, word=False):
    return (1 << 25) | (b << 20) | (a << 15) | (function << 12) | (rd << 7) | (0x3b if word else 0x33)


def ld(rd, base, offset=0):
    return ((offset & 4095) << 20) | (base << 15) | (3 << 12) | (rd << 7) | 3


def sd(rs, base, offset=0):
    return (((offset & 4095) >> 5) << 25) | (rs << 20) | (base << 15) | (3 << 12) | ((offset & 31) << 7) | 0x23


def lw(rd, base, offset=0, unsigned=False):
    return (ld(rd, base, offset) & ~(7 << 12)) | ((6 if unsigned else 2) << 12)


def sw(rs, base, offset=0):
    return sd(rs, base, offset) & ~(1 << 12)


def alu(rd, rs1, operand, function, word=False, immediate=False, upper=0):
    opcode = (0x1b if word else 0x13) if immediate else (0x3b if word else 0x33)
    source = (operand & 4095) << 20 if immediate else (upper << 25) | (operand << 20)
    return source | (rs1 << 15) | (function << 12) | (rd << 7) | opcode


def load(rd, base, offset=0, size=3, unsigned=False):
    return (ld(rd, base, offset) & ~(7 << 12)) | ((size + 4 * unsigned) << 12)


def store(rs, base, offset=0, size=3):
    return (sd(rs, base, offset) & ~(7 << 12)) | (size << 12)


def amoadd(rd, base, rs, aqrl=0):
    return (aqrl << 25) | (rs << 20) | (base << 15) | (3 << 12) | (rd << 7) | 0x2f


def amo(operation, rd, base, rs=0, aqrl=0, size=3):
    return ((operation << 27) | amoadd(rd, base, rs, aqrl)) ^ ((3 ^ size) << 12)


def fence(instruction=False, reserved=0):
    return (reserved & 0xffff8f80) | (int(instruction) << 12) | 0x0f


def csr(rd, address, rs, set_bits=False, function=None):
    return (address << 20) | (rs << 15) | (((2 if set_bits else 1) if function is None else function) << 12) | (rd << 7) | 0x73


def jal(rd, offset):
    return (((offset >> 20) & 1) << 31) | (((offset >> 1) & 1023) << 21) | (((offset >> 11) & 1) << 20) | (((offset >> 12) & 255) << 12) | (rd << 7) | 0x6f


def beq(a, b, offset):
    return (((offset >> 12) & 1) << 31) | (((offset >> 5) & 63) << 25) | (b << 20) | (a << 15) | (((offset >> 1) & 15) << 8) | (((offset >> 11) & 1) << 7) | 0x63


def jalr(rd, rs, offset=0):
    return ((offset & 4095) << 20) | (rs << 15) | (rd << 7) | 0x67


class Program:
    def __init__(self, base):
        self.base = base
        self.offset = 0
        self.memory = {}
        self.faults = {}
        self.address(1, 0x800)
        self.emit(csr(0, 0x305, 1))

    def emit(self, *words):
        for word in words:
            for i in range(4):
                self.memory[self.base + self.offset + i] = (word >> (8 * i)) & 255
            self.offset += 4

    def half(self, *parcels):
        for parcel in parcels:
            self.memory[self.base + self.offset] = parcel & 255
            self.memory[self.base + self.offset + 1] = parcel >> 8
            self.offset += 2

    def address(self, rd, target):
        distance = target - self.offset
        upper = (distance + 2048) >> 12
        self.emit(((upper & 0xfffff) << 12) | (rd << 7) | 0x17)
        self.emit(addi(rd, rd, distance - (upper << 12)))

    def finish(self, fixed_return=False, resume_offset=None):
        self.stop = self.base + self.offset
        self.emit(jal(0, 0))
        self.offset = 0x800
        self.emit(csr(24, 0x300, 0, True), csr(20, 0x342, 0, True), csr(21, 0x343, 0, True), csr(22, 0x341, 0, True), addi(23, 23, 1))
        if fixed_return or resume_offset is not None:
            self.address(22, self.stop - self.base if resume_offset is None else resume_offset)
        else:
            self.emit(addi(22, 22, 4))
        self.emit(csr(0, 0x341, 22), 0x30200073)
        return self


def integer_stream(p, name='integer_stream'):
    p.emit(addi(4, 0, 3), addi(5, 0, 7), addi(30, 0, 2))
    loop = p.offset
    destinations = [1, 2, 3, *range(6, 28)]
    for index in range(204):
        rd = destinations[index % len(destinations)] if name == 'integer_stream' else 1 + index % 3 if name == 'dependency_stream' else 1
        p.emit(add(rd, 4 if name == 'integer_stream' else rd, 5))
    p.emit(addi(30, 30, -1), beq(30, 0, 8))
    p.emit(jal(0, loop - p.offset))


def memory_group_cases(base, protection, interrupts, sv39):
    p = Program(base)
    p.address(10, 0x1000)
    p.emit(addi(30, 0, 4))
    p.memory[base + 0x1000] = 9
    groups, loop = {}, p.offset
    for instruction, tail, maximum in ((ld(2, 10), addi(3, 3, 1), 3),
                                       (sd(2, 10, 8), addi(3, 3, 1), 3),
                                       (ld(2, 10), addi(3, 2, 1), 1),
                                       (ld(2, 10), addi(2, 0, 17), 1)):
        groups[base + p.offset] = maximum
        p.emit(instruction, tail, addi(4, 4, 1))
    p.emit(addi(30, 30, -1), beq(30, 0, 8), jal(0, loop - p.offset - 8))
    p.pipeline_groups = groups
    yield 'memory_groups', p.finish()

    for fault in ('alignment', 'bus_read', 'bus_write', *(('pmp',) if protection else ()), *(('page',) if sv39 else ())):
        p = Program(base)
        p.address(10, 0x1001 if fault == 'alignment' else 0x1000)
        p.emit(addi(6, 0, 11), addi(7, 0, 13))
        if fault == 'pmp':
            p.emit(alu(2, 10, 2, 5, immediate=True), csr(0, 0x3b0, 2), addi(2, 0, 0x98), csr(0, 0x3a0, 2))
        if fault == 'page':
            if protection:
                p.emit(addi(2, 0, -1), csr(0, 0x3b0, 2), addi(2, 0, 0x1f), csr(0, 0x3a0, 2))
            p.address(11, 0x600)
            for offset, value in ((0, (8 << 60) | ((base + 0x3000) >> 12)), (8, 0x20800), (16, 0x40000000)):
                p.memory.update((base + 0x600 + offset + byte, (value >> (8 * byte)) & 255) for byte in range(8))
            p.emit(ld(2, 11), csr(0, 0x180, 2), ld(10, 11, 16), ld(2, 11, 8), csr(0, 0x300, 2))
        if fault.startswith('bus_'):
            p.faults[fault[4:]] = base + 0x1000
        while (base + p.offset) // 4 % 4:
            p.emit(addi(0, 0, 0))
        p.pipeline_groups = {base + p.offset: 3}
        p.emit(sd(6, 10) if fault == 'bus_write' else ld(2, 10), addi(6, 0, 99), addi(7, 0, 101))
        resume = p.offset
        p.emit(addi(8, 6, 0), addi(9, 7, 0))
        p.expected_registers = {6: 11, 7: 13, 8: 11, 9: 13, 23: 1}
        yield 'memory_group_' + fault, p.finish(resume_offset=resume)

    if interrupts:
        p = Program(base)
        p.address(10, 0x1000)
        p.address(11, 0x5008)
        p.emit(addi(2, 0, 8), csr(0, 0x304, 2), csr(0, 0x300, 2))
        while (base + p.offset) // 4 % 4:
            p.emit(addi(0, 0, 0))
        target = base + p.offset
        p.emit(ld(2, 10), addi(6, 6, 1), addi(7, 7, 1), sd(6, 10, 8), sd(7, 10, 16))
        p.finish()
        p.offset = 0x800
        p.emit(addi(23, 23, 1), sd(0, 11), 0x30200073)
        p.interrupts = dict(mode=4, mask=1, target=target)
        p.pipeline_groups = {target: 3}
        p.expected_registers = {6: 1, 7: 1, 23: 1}
        yield 'memory_group_interrupt', p


def load_window_program(base, harts=1, cancel=False):
    p = Program(base)
    p.emit(csr(2, 0xf14, 0, True), alu(3, 2, 7, 1, immediate=True))
    p.address(10, 0x1800)
    begin = base + p.offset
    p.emit(add(10, 10, 3), ld(3, 10))
    if cancel:
        p.emit(jal(0, 12), sd(0, 0), 0)
    p.emit(ld(4, 10, 64), add(5, 3, 4))
    end = base + p.offset - 4
    p.address(11, 0x3000)
    p.emit(alu(6, 2, 3, 1, immediate=True), add(11, 11, 6), sd(5, 11), sd(5, 11, 0x100), sd(5, 11, 0x200))
    for hart in range(harts):
        for offset, value in ((0, 11 + hart), (64, 22 + hart)):
            p.memory[base + 0x1800 + 128 * hart + offset] = value
    p.load_window = not cancel
    p.data_cache = dict(minHits=0, finalRegisters=[{3: 11 + hart, 4: 22 + hart, 5: 33 + 2 * hart} for hart in range(harts)])
    p.data_cache['work'] = dict(begin=begin, end=end, reads={8: 2, 64: 2})
    return p.finish()


def cases(base, protection=False, interrupts=False, user=False, local_interrupt_base=None, supervisor=False, sv39=False, writeback=False, compressed=False, floating_point_bits=None, scalar=None):
    if not sv39:
        yield 'load_window', load_window_program(base)
        yield 'load_cancel', load_window_program(base, cancel=True)
        for name in ('branch_window', 'return_window', 'return_switch'):
            returns = name != 'branch_window'
            p = Program(base)
            begin = base + p.offset
            p.emit(addi(2, 0, 32))
            loop = p.offset
            if returns:
                p.emit(jal(1, 0x400 - loop))
                recovery = {base + loop: [base + 0x400], base + 0x404: [base + loop + 4]}
                if name == 'return_switch':
                    p.emit(addi(3, 3, 1))
                    call = p.offset
                    p.emit(jal(1, 0x400 - call))
                    recovery[base + call] = [base + 0x400]
                    recovery[base + 0x404].append(base + call + 4)
            else:
                p.emit(beq(0, 0, 12), sd(0, 0), 0)
                recovery = {base + loop: [base + loop + 12]}
            p.emit(addi(2, 2, -1))
            branch = p.offset
            p.emit(beq(2, 0, loop - branch) ^ (1 << 12))
            recovery[base + branch] = [base + loop, base + branch + 4]
            p.branch_window = dict(begin=begin, end=base + p.offset)
            p.pipeline_recovery = recovery
            p.emit(addi(7, 0, 1))
            if returns:
                end = p.offset
                p.offset = 0x400
                p.emit(addi(5, 5, 1), jalr(0, 1))
                p.offset = end
            yield name, p.finish()
    yield from memory_group_cases(base, protection, interrupts, sv39)
    for fault in (False, True):
        p = Program(base)
        p.address(10, 0x1000)
        p.address(11, 0x1080)
        p.emit(addi(30, 0, 4))
        p.memory[base + 0x1000] = 9
        loop = p.offset
        p.emit(ld(2, 10), addi(3, 3, 1), addi(4, 4, 1))
        branch = base + p.offset
        p.emit(beq(0, 0, 12), sd(2, 11), 0, addi(7, 7, 1), addi(30, 30, -1))
        back = base + p.offset
        p.emit(beq(30, 0, loop - p.offset) ^ (1 << 12))
        direct = base + p.offset
        p.emit(jal(5, 12), sd(2, 11), 0, addi(8, 8, 1))
        p.address(12, p.offset + 20)
        indirect = base + p.offset
        p.emit(jalr(9, 12), sd(2, 11), 0)
        p.pipeline_recovery = {branch: [branch + 12], back: [base + loop, back + 4],
                               direct: [direct + 12], indirect: [indirect + 12]}
        if not fault:
            p.recovery_counts = {branch: (4, 4), back: (3, 1), direct: (1, 0), indirect: (1, 1)}
        resume = p.offset
        p.emit(addi(12, 3, 0), addi(13, 4, 0), addi(14, 7, 0), addi(15, 8, 0))
        p.expected_registers = {7: 0 if fault else 4, 8: 0 if fault else 1, 23: int(fault)}
        if fault:
            p.faults['read'] = base + 0x1000
            p.recovery_fault_pc = base + loop
            p.expected_registers.update({register: 0 for register in range(12, 16)})
        yield 'pipeline_recovery_fault' if fault else 'pipeline_recovery', p.finish(resume_offset=resume if fault else None)
    if not interrupts:
        p = Program(base)
        p.emit(0x10500073, addi(2, 0, 17))
        yield 'wfi_no_interrupts', p.finish()
    p = Program(base)
    p.emit(addi(0, 0, 127), addi(2, 0, -1), (0x80000 << 12) | (3 << 7) | 0x37,
           add(4, 2, 3), addi(5, 0, 7))
    loop = p.offset
    p.emit(addi(5, 5, -1), beq(5, 0, 8), jal(0, loop - (p.offset + 8)))
    p.emit(jal(6, 8), addi(2, 0, 999))
    target = p.offset + 16
    p.address(7, target | 1)
    p.emit(jalr(8, 7), sd(2, 0))
    rng = random.Random(2026)
    for _ in range(120):
        rd, a, b = (rng.randrange(32) for _ in range(3))
        p.emit(add(rd, a, b) if rng.randrange(2) else addi(rd, a, rng.randrange(-2048, 2048)))
    yield 'arithmetic', p.finish()

    p = Program(base)
    p.address(10, 0x1000)
    for i in range(16):
        p.emit(addi(2, 0, -i - 1), sd(2, 10, i * 8), ld(3, 10, i * 8), add(4, 2, 3))
    p.address(10, 0x4000)
    p.emit(ld(3, 10))
    p.address(10, 0x5000)
    p.emit(sd(2, 10), ld(4, 10))
    yield 'memory', p.finish()

    p = Program(base)
    p.address(10, 0x1000)
    values = (0, 1, 0x7fffffff, 0x80000000, 0xffffffff, 0xa5a55a5a)
    for index, value in enumerate(values):
        for byte in range(4):
            p.memory[base + 0x1800 + index * 4 + byte] = (value >> (8 * byte)) & 255
    p.address(11, 0x1800)
    p.emit(addi(2, 0, -1), sd(2, 10))
    for lane in range(0, 64, 4):
        p.emit(lw(2, 11, lane % 24), lw(3, 11, lane % 24, True),
               sw(2, 10, lane), lw(4, 10, lane), lw(5, 10, lane, True))
    p.emit(ld(6, 10), lw(0, 10), lw(0, 10, 2), sw(2, 10, 2))
    for offset in (0x3ffc, 0x4000, 0x4ffc, 0x5000, 0x5ffc, 0x6000, 0x7000, 0x9000):
        p.address(10, offset)
        p.emit(lw(7, 10), lw(8, 10, unsigned=True), sw(2, 10))
    p.emit(addi(10, 0, -4), lw(9, 10), sw(2, 10))
    p.emit(load(9, 10, size=3, unsigned=True), store(2, 10, size=7))
    yield 'memory_word', p.finish()

    for kind in ('read', 'write'):
        p = Program(base)
        p.address(10, 0x1004)
        p.faults[kind] = base + 0x1004
        p.emit(lw(2, 10) if kind == 'read' else sw(1, 10))
        yield 'word_bus_' + kind, p.finish()

    p = Program(base)
    p.emit(addi(1, 0, -1), csr(2, 0x300, 1), csr(3, 0x300, 0, True),
           csr(4, 0x340, 1), csr(5, 0x340, 0, True), csr(6, 0x301, 0, True),
           csr(7, 0xf14, 0, True), csr(8, 0x304, 1), csr(9, 0x304, 0, True))
    p.emit(0, 0x73, csr(4, 0x777, 0, True), csr(5, 0xf14, 0),
           addi(1, 0, 1), beq(0, 1, 2), beq(0, 0, 2), jal(6, 2))
    p.address(10, 0x1002)
    p.emit(jalr(7, 10), ld(4, 10), sd(1, 10))
    for offset in (0x4000, 0x6000, 0x7000, 0x9000):
        p.address(10, offset)
        p.emit(sd(1, 10), ld(4, 10))
    p.emit(addi(10, 0, -8), ld(4, 10), sd(1, 10))
    p.emit(csr(25, 0x300, 0, True))
    yield 'exceptions', p.finish()

    for kind in ('read', 'write', 'fetch'):
        p = Program(base)
        p.address(10, 0x1008)
        p.faults[kind] = base + (p.offset if kind == 'fetch' else 0x1008)
        p.emit(ld(2, 10) if kind != 'write' else sd(1, 10))
        yield 'bus_' + kind, p.finish()

    for offset in (0x5000, 0x6000, 0x7000):
        p = Program(base)
        p.address(10, offset)
        p.emit(jalr(0, 10))
        yield f'fetch_region_{offset:x}', p.finish(fixed_return=True)

    p = Program(base)
    p.address(10, 0x1000)
    p.emit(addi(2, 0, 19), sd(2, 10), ld(2, 10), addi(2, 0, 7),
           add(3, 2, 2), add(4, 3, 2), addi(4, 4, 1),
           csr(5, 0x340, 4), csr(6, 0x340, 0, True),
           csr(7, 0x340, 2), csr(8, 0x340, 0, True),
           csr(9, 0x300, 2), csr(11, 0x300, 0, True))
    yield 'pipeline_dependencies', p.finish()

    p = Program(base)
    p.address(10, 0x5000)
    p.emit(addi(2, 0, 31), csr(0, 0x340, 2))
    for wrong_path in (sd(2, 10), ld(3, 10), csr(0, 0x340, 0), fence(), fence(True), 0):
        p.emit(jal(0, 12), wrong_path, 0)
    p.faults['fetch'] = base + p.offset + 4
    p.emit(beq(0, 0, 12), 0, 0, csr(4, 0x340, 0, True))
    yield 'pipeline_redirect', p.finish()

    p = Program(base)
    p.address(10, 0x1008)
    p.faults['read'] = base + 0x1008
    p.emit(ld(2, 10), csr(0, 0x305, 0), jal(3, 8), sd(1, 10),
           csr(4, 0x342, 0, True), csr(5, 0x343, 0, True))
    yield 'pipeline_older_fault', p.finish()

    p = Program(base)
    p.address(10, 0x1000)
    p.emit(addi(2, 0, 64))
    loop = p.offset
    p.emit(ld(3, 10), addi(3, 3, 1), sd(3, 10), addi(2, 2, -1), beq(2, 0, 8))
    p.emit(jal(0, loop - p.offset))
    yield 'pipeline_reuse', p.finish()

    for name in ('integer_stream', 'dependency_stream', 'dependency_chain'):
        p = Program(base)
        integer_stream(p, name)
        yield 'pipeline_' + name, p.finish()

    p = Program(base)
    p.address(10, 0x1000)
    p.address(11, 0x1800)
    edges = (0, 1, 2, (1 << 64) - 1, 1 << 63, (1 << 63) - 1, 1 << 32, 0xaaaaaaaa55555555)
    pairs = [(a, b) for a in edges for b in edges]
    pairs += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(32)]
    for index, (a, b) in enumerate(pairs):
        for offset, value in ((0, a), (8, b)):
            for byte in range(8):
                p.memory[base + 0x1000 + index * 16 + offset + byte] = (value >> (byte * 8)) & 255
        p.emit(ld(2, 10, index * 16), ld(3, 10, index * 16 + 8), mul(4, 2, 3), sd(4, 11, index * 8))
    p.emit(mul(2, 2, 3), add(4, 2, 2), mul(4, 4, 4), mul(0, 2, 3), addi(5, 0, 9),
           sd(4, 11), mul(6, 0, 4), sd(6, 11, 8),
           mul(7, 2, 3) | (1 << 12), mul(7, 2, 3) | (4 << 12), mul(7, 2, 3) | 8)
    yield 'multiply', p.finish()
    yield from integer_cases(base)
    yield from bitmanip_cases(base)
    if floating_point_bits is not None:
        yield from floating_cases(base, floating_point_bits)
        yield from floating_state_cases(base, floating_point_bits)
        yield from floating_extension_cases(base, floating_point_bits, scalar or {})
        if sv39 and floating_point_bits:
            widths = (16, floating_point_bits) if (scalar or {}).get('enableZfhmin') else (floating_point_bits,)
            for width in widths:
                for name, p in sv39_cases(base, protection, writeback):
                    if name not in ('sv39_data', 'sv39_protection', 'sv39_sum', 'sv39_mxr'):
                        continue
                    for byte in range(8):
                        p.memory[base + 0x610 + byte] = p.memory.get(base + 0x610 + byte, 0) | ((0x2000 >> (byte*8)) & 255)
                    for pc in range(base, p.stop, 4):
                        word = sum(p.memory.get(pc+i, 0) << (8*i) for i in range(4))
                        if (word >> 15) & 31 == 11 and word & 127 in (3, 0x23):
                            word = (word | 4) & ~(7 << 12) | ({16: 1, 32: 2, 64: 3}[width] << 12)
                            p.memory.update((pc+i, (word >> (8*i)) & 255) for i in range(4))
                    p.floating_memory = (1, 2) if name == 'sv39_protection' else (1, 1) if name == 'sv39_mxr' else (2, 0)
                    if width == 16:
                        pc = p.stop - 4
                        p.memory.update((pc + byte, (0xe4000053 | (3 << 15) | (7 << 7)) >> (8 * byte) & 255) for byte in range(4))
                        p.offset = p.stop - base
                        p.emit(csr(0, 0x300, 0), jal(0, 0))
                        p.stop += 4
                        p.expected_registers = {7: 0x5678}
                    yield ('floating_half_' if width == 16 else 'floating_') + name, p
    if compressed:
        yield from compressed_cases(base, protection, sv39, scalar or {})

    yield from synchronization_cases(base, writeback)
    yield 'data_cache', data_cache_program(base)
    yield from data_cache_access_cases(base, protection)
    yield from atomic_cases(base, protection)
    if scalar is not None:
        yield from scalar_cases(base, scalar)
    if protection:
        yield from pmp_cases(base, writeback)
    if interrupts:
        yield from interrupt_cases(base, protection)
    if user:
        yield from user_cases(base, protection, interrupts, local_interrupt_base, floating_point_bits or 0, supervisor)
    if supervisor:
        yield from supervisor_cases(base, protection)
    if sv39:
        yield from sv39_cases(base, protection, writeback)


def sv39_cases(base, protection, writeback=False):
    p = Program(base)
    root, middle, leaf, virtual = base + 0x1000, base + 0x2000, base + 0x3000, 0x40000000
    values = [(root + 8, ((middle >> 12) << 10) | 1), (middle, ((leaf >> 12) << 10) | 1),
              (leaf, ((base >> 12) << 10) | 0xcf), (base + 0x600, (8 << 60) | root >> 12), (base + 0x610, 0x800)]
    if protection:
        p.emit(addi(2, 0, -1), csr(0, 0x3b0, 2), addi(2, 0, 0x1f), csr(0, 0x3a0, 2))
    p.address(10, 0x600)
    p.emit(ld(2, 10), csr(0, 0x180, 2), 0x12000073, ld(2, 10, 16), csr(0, 0x300, 2),
           ld(2, 10, 8), csr(0, 0x341, 2), 0x30200073)
    values.append((base + 0x608, virtual + p.offset))
    integer_stream(p)
    stop = virtual + p.offset
    for address, value in values:
        p.memory.update((address + byte, (value >> (8 * byte)) & 255) for byte in range(8))
    p.finish()
    p.stop = stop
    yield 'sv39_integer_stream', p
    for name, flags, status, address, levels in (
            ('data', 0xcf, 0x20800, 0x40000100, 0),
            ('atomic', 0xcf, 0x20800, 0x40000104, 0),
            ('reuse', 0xcf, 0x20800, 0x40000100, 0),
            ('protection', 0xcf, 0x20800, 0x40000100, 0),
            ('large', 0xcf, 0x20800, 0x40000100, 1),
            ('gigantic', 0xcf, 0x20800, 0x40000100, 2),
            ('accessed', 0x8f, 0x20800, 0x40000100, 0),
            ('dirty', 0x4f, 0x20800, 0x40000100, 0),
            ('user_denied', 0xdf, 0x20800, 0x40000100, 0),
            ('sum', 0xdf, 0x60800, 0x40000100, 0),
            ('mxr', 0xc9, 0xa0800, 0x40000100, 0),
            ('canonical', 0xcf, 0x20800, 1 << 39, 0)):
        if name == 'protection' and not protection:
            continue
        p = Program(base)
        def word(physical, value):
            for byte in range(8):
                p.memory[physical + byte] = (value >> (byte * 8)) & 255
        root, middle, leaf = base + 0x1000, base + 0x2000, base + 0x3000
        word(root + 8, ((base >> 12) << 10) | flags if levels == 2 else ((middle >> 12) << 10) | 1)
        word(middle, ((base >> 12) << 10) | flags if levels == 1 else ((leaf >> 12) << 10) | 1)
        word(leaf, ((base >> 12) << 10) | flags)
        word(base + 0x100, 0x12345678)
        if protection:
            p.emit(addi(2, 0, -1), csr(0, 0x3b0, 2), addi(2, 0, 0x1f), csr(0, 0x3a0, 2))
        p.address(10, 0x600)
        word(base + 0x600, (8 << 60) | (root >> 12))
        word(base + 0x608, address)
        word(base + 0x610, status)
        p.emit(ld(2, 10), csr(0, 0x180, 2), 0x12000073, ld(11, 10, 8), ld(2, 10, 16), csr(0, 0x300, 2))
        if name == 'reuse':
            p.emit(addi(4, 0, 32), ld(3, 11), addi(4, 4, -1), beq(4, 0, -8) ^ (1 << 12))
        else:
            p.emit(load(3, 11, size=2) if name == 'atomic' else ld(3, 11))
        if name == 'atomic':
            p.emit(addi(4, 0, -1))
            for operation in (0, 1, 4, 8, 12, 16, 20, 24, 28):
                p.emit(amo(operation, 5, 11, 4, 3, 2))
            p.emit(amo(2, 6, 11, aqrl=2, size=2), amo(3, 7, 11, 4, 1, 2))
        if name == 'protection':
            p.address(12, 0x1000)
            p.emit(csr(0, 0x300, 0), alu(12, 12, 2, 5, immediate=True), csr(0, 0x3b0, 12),
                   addi(12, 0, 0xf), csr(0, 0x3a0, 12), csr(0, 0x300, 2), ld(4, 11))
        p.emit(store(3, 11, size=2) if name == 'atomic' else sd(3, 11), csr(0, 0x300, 0))
        if name == 'atomic': p.required_atomics = 11
        yield 'sv39_' + name, p.finish()
    p = Program(base)
    root, middle, leaf, virtual = base + 0x1000, base + 0x2000, base + 0x3000, 0x40000000
    def word(physical, value):
        p.memory.update((physical + byte, (value >> (byte * 8)) & 255) for byte in range(8))
    word(root + 8, (middle >> 2) | 1)
    word(middle, (leaf >> 2) | 1)
    for page in range(4):
        word(leaf + page * 8, ((base + page * 4096) >> 2) | 0xcf)
    for page, value in ((1, 0x1111), (2, 0x2222), (3, 0x3333)):
        word(base + page * 4096 + 0x100, value)
        word(base + 0x610 + page * 8, virtual + page * 4096 + 0x100)
    word(base + 0x600, (8 << 60) | root >> 12)
    word(base + 0x610, 0x800)
    if protection:
        p.emit(addi(2, 0, -1), csr(0, 0x3b0, 2), addi(2, 0, 0x1f), csr(0, 0x3a0, 2))
    p.address(10, 0x600)
    p.emit(ld(11, 10, 24), ld(12, 10, 32), ld(13, 10, 40), ld(2, 10), csr(0, 0x180, 2), 0x12000073,
           ld(2, 10, 16), csr(0, 0x300, 2), ld(2, 10, 8), csr(0, 0x341, 2), 0x30200073)
    word(base + 0x608, virtual + p.offset)
    p.emit(addi(6, 0, 32))
    loop = p.offset
    p.emit(ld(3, 11), ld(4, 12), ld(5, 13), addi(6, 6, -1), beq(6, 0, loop - p.offset - 16) ^ (1 << 12))
    stop = virtual + p.offset
    p.finish()
    p.stop = stop
    p.expected_registers = {3: 0x1111, 4: 0x2222, 5: 0x3333, 6: 0}
    yield 'sv39_working_set', p
    p = Program(base)
    root, other, middle, alternate, leaf = (base + offset for offset in (0x1000, 0, 0x2000, 0x3000, 0x7000))
    def word(physical, value):
        p.memory.update((physical + byte, (value >> (byte * 8)) & 255) for byte in range(8))
    for physical, value in ((root + 255 * 8, middle >> 2 | 1), (other + 255 * 8, alternate >> 2 | 1),
            (middle + 8, leaf >> 2 | 1), (alternate + 8, middle >> 2 | 1),
            (leaf, root >> 2 | 0xcf), (middle, middle >> 2 | 0xcf),
            (root + 0x100, 0x11), (middle + 0x100, 0x22),
            (base + 0x600, 8 << 60 | 1 << 44 | root >> 12), (base + 0x608, 8 << 60 | 2 << 44 | other >> 12),
            (base + 0x610, 255 << 30 | 1 << 21 | 0x100), (base + 0x618, 0x20800),
            (base + 0x620, 1 << 63 | 2)):
        word(physical, value)
    if protection:
        p.emit(addi(2, 0, -1), csr(0, 0x3b0, 2), addi(2, 0, 0x1f), csr(0, 0x3a0, 2))
    p.address(10, 0x600)
    p.emit(ld(2, 10), ld(3, 10, 8), ld(11, 10, 16), ld(12, 10, 24), ld(14, 10, 32), addi(15, 0, 0), 0x12000073)
    def access(context):
        p.emit(csr(0, 0x180, context), csr(0, 0x300, 12), ld(14 + context, 11), csr(0, 0x300, 0))
    for context in (2, 3, 2, 2):
        access(context)
    for selectors in ((15, 0), (0, 15), (0, 14), (0, 0)):
        p.emit(0x12000073 | selectors[0] << 15 | selectors[1] << 20)
        for context in ((2, 3, 2) if selectors == (0, 14) else (2, 3)):
            access(context)
    p.translation = {16: 0x11, 17: 0x22}
    p.translation_accesses = 13
    yield 'sv39_asid', p.finish()
    p = Program(base)
    root, other, middle, alternate, leaf, changed = (base + offset for offset in (0x1000, 0, 0x2000, 0x3000, 0x4000, 0x7000))
    if writeback:
        changed = root
    def word(physical, value):
        for byte in range(8):
            p.memory[physical + byte] = (value >> (8 * byte)) & 255
    for address, value in ((root + 255 * 8, ((middle >> 12) << 10) | 1), (other + 255 * 8, ((alternate >> 12) << 10) | 1),
                           (middle, ((leaf >> 12) << 10) | 1), (alternate, ((changed >> 12) << 10) | 1),
                           (leaf, ((root >> 12) << 10) | 0xcf), (changed, ((middle >> 12) << 10) | 0xcf),
                           (root + 0x100, 0x11), (middle + 0x100, 0x22), (alternate + 0x100, 0x33),
                           (base + 0x600, (8 << 60) | root >> 12), (base + 0x608, (8 << 60) | other >> 12),
                           (base + 0x610, (255 << 30) | 0x100), (base + 0x618, 0x20800),
                           (base + 0x620, ((alternate >> 12) << 10) | 0xcf)):
        word(address, value)
    if protection:
        p.emit(addi(2, 0, -1), csr(0, 0x3b0, 2), addi(2, 0, 0x1f), csr(0, 0x3a0, 2))
    p.address(10, 0x600)
    p.address(13, changed - base)
    p.emit(ld(2, 10), ld(3, 10, 8), ld(11, 10, 16), ld(12, 10, 24), ld(14, 10, 32),
           csr(0, 0x180, 2), 0x12000073, csr(0, 0x300, 12), ld(4, 11), csr(0, 0x300, 0),
           csr(0, 0x180, 3), 0x12358073, csr(0, 0x300, 12), ld(5, 11), csr(0, 0x300, 0))
    if writeback:
        p.emit(ld(15, 13))
        p.dirty_pte = changed, ((alternate >> 12) << 10) | 0xcf
    p.emit(sd(14, 13), 0x12000073, csr(0, 0x300, 12), ld(6, 11), csr(0, 0x300, 0), csr(0, 0x180, 0))
    p.translation = {4: 0x11, 5: 0x22, 6: 0x33}
    yield 'sv39_context', p.finish()


def user_protection(p, execute_top=0x1000, data_top=0x1008):
    for index, top in enumerate((execute_top, data_top)):
        p.address(1, top)
        p.emit(alu(1, 1, 2, 5, immediate=True), csr(0, 0x3b0 + index, 1))
    p.emit(addi(1, 0, 0xb), alu(1, 1, 8, 1, immediate=True), addi(1, 1, 0xc), csr(0, 0x3a0, 1))


def supervisor_cases(base, protection=False):
    for name in ('traps', 'csr', 'mprv'):
        p = Program(base)
        p.address(10, 0x1000)
        if protection:
            user_protection(p)
        p.address(1, 0x600)
        p.emit(csr(0, 0x105, 1), addi(1, 0, 0x108 if name == 'traps' else 0x100), csr(0, 0x302, 1),
               addi(1, 0, 0x222), csr(0, 0x303, 1))
        if name == 'mprv':
            p.emit(ld(6, 10, 8), addi(1, 0, 0x3ff), csr(0, 0x302, 1), addi(1, 0, 1), alu(1, 1, 17, 1, immediate=True),
                   addi(1, 1, 0x400), addi(1, 1, 0x400), csr(0, 0x300, 1),
                   ld(3, 10), ld(4, 10, 8), csr(5, 0x342, 0, True), csr(0, 0x300, 0))
            yield 'supervisor_' + name, p.finish()
            continue
        p.address(1, 0x200)
        p.emit(csr(0, 0x341, 1), addi(1, 0, 1), alu(1, 1, 11, 1, immediate=True),
               csr(0, 0x300, 1), 0x30200073)
        p.offset = 0x200
        p.emit(csr(2, 0x100, 0, True), csr(3, 0x180, 10), csr(4, 0x180, 0, True),
               csr(5, 0x106, 10), csr(6, 0x10a, 10), addi(2, 0, 17), sd(2, 10), ld(3, 10))
        p.emit(0x00100073)
        if name == 'csr':
            p.emit(addi(2, 0, 0x222), csr(0, 0x104, 2), csr(4, 0x104, 0, True),
                   csr(0, 0x104, 0), csr(0, 0x144, 2), csr(5, 0x144, 0, True),
                   csr(0, 0x144, 0), csr(6, 0x300, 0, True))
        p.address(1, 0x400)
        p.emit(csr(0, 0x141, 1), csr(0, 0x100, 0), 0x10200073)
        p.offset = 0x400
        p.emit(csr(7, 0x100, 0, True), 0x00100073, 0x10200073, 0x10500073, ld(8, 10),
               ld(9, 10, 8), 0x73, addi(11, 0, 23))
        p.stop = base + p.offset
        p.emit(jal(0, 0))
        p.offset = 0x600
        p.emit(csr(26, 0x142, 0, True), csr(27, 0x143, 0, True),
               csr(28, 0x141, 0, True), addi(29, 29, 1), csr(30, 0x100, 0, True),
               csr(2, 0x300, 0, True), addi(28, 28, 4), csr(0, 0x141, 28))
        p.emit(addi(2, 0, 8), beq(26, 2, 8), 0x10200073, 0x73, 0x10200073)
        p.offset = 0x800
        p.emit(csr(24, 0x300, 0, True), csr(20, 0x342, 0, True),
               csr(21, 0x343, 0, True), csr(22, 0x341, 0, True), addi(23, 23, 1),
               addi(2, 0, 9), beq(20, 2, 16), addi(22, 22, 4), csr(0, 0x341, 22), 0x30200073)
        p.address(1, p.stop - base)
        p.emit(csr(0, 0x341, 1), addi(1, 0, 3), alu(1, 1, 11, 1, immediate=True),
               csr(0, 0x300, 1), 0x30200073)
        yield 'supervisor_' + name, p


def user_cases(base, protection=False, interrupts=False, local_interrupt_base=None, floating_point_bits=0, supervisor=False):
    for name in ('access', 'system', 'wait', *(['protection', 'fetch'] if protection else []),
                 *(['interrupt'] if interrupts else []),
                 *(['device'] if protection and local_interrupt_base is not None else []),
                 *(['floating', 'floating_off', *(['floating_s', 'floating_s_off'] if supervisor else [])] if floating_point_bits else [])):
        p = Program(base)
        p.address(10, 0x1000)
        if protection:
            user_protection(p, 0x200 if name == 'fetch' else 0x1000)
        if name == 'fetch':
            p.address(8, p.offset + 20)
            p.address(1, 0x200)
            p.emit(jalr(0, 1))
        if name == 'device':
            p.emit(csr(2, 0xf14, 0, True), addi(3, 0, 4), mul(2, 2, 3))
            p.address(11, int(local_interrupt_base) - base)
            p.emit(add(11, 11, 2), addi(3, 0, 1), sw(3, 11), lw(27, 11), sw(0, 11))
        if name == 'system':
            p.emit(csr(26, 0xf15, 0, True), csr(27, 0x306, 10), csr(28, 0x306, 0, True),
                   csr(29, 0x30a, 10), csr(30, 0x30a, 0, True), csr(0, 0xf15, 0))
        p.address(1, 0x200)
        if name == 'interrupt':
            p.emit(addi(2, 0, 8), csr(0, 0x304, 2))
        fp = name.startswith('floating')
        status = (0 if name.endswith('off') else 4) + int('_s' in name) if fp else int(name == 'wait')
        p.emit(csr(0, 0x341, 1), addi(1, 0, status),
               alu(1, 1, 11 if fp else 21, 1, immediate=True), csr(0, 0x300, 1), 0x30200073)
        p.offset = 0x200
        if fp:
            p.emit(0x3f8000b7, 0xf0008053, 0x00000053, 0xe00002d3, csr(6, 3, 0, True))
            p.expected_registers = {5: 0 if name.endswith('off') else 0x40000000, 23: 5 if name.endswith('off') else 1}
        elif name == 'access':
            p.emit(addi(2, 0, 17), sd(2, 10), ld(3, 10), amo(8, 4, 10, 2), amo(2, 5, 10), amo(3, 6, 10, 2))
            if not interrupts:
                p.emit(0x10500073)
        elif name == 'system':
            p.emit(csr(2, 0x300, 0, True), csr(0, 0x340, 10), csr(0, 0xf14, 0),
                   0x30200073, csr(3, 0x180, 0, True), csr(4, 0x306, 0, True), csr(0, 0x306, 10),
                   csr(5, 0x30a, 0, True), csr(0, 0x30a, 10), csr(6, 0xf15, 0, True), fence(), fence(True), 0x00100073)
        elif name == 'wait':
            p.emit(0x10500073)
        elif name == 'protection':
            p.address(11, 0x200)
            p.emit(ld(2, 11), ld(3, 10, 8), sd(10, 10, 8), addi(11, 10, 8), amoadd(4, 11, 10))
        elif name == 'device':
            p.emit(addi(3, 0, 1), sd(3, 10), ld(28, 10), lw(2, 11), sw(3, 11))
            p.address(12, int(local_interrupt_base) - base + 0xbff8)
            p.emit(amoadd(4, 12, 3))
        if name == 'fetch':
            p.emit(jalr(0, 8))
        elif name == 'interrupt':
            p.emit(ld(9, 10), addi(7, 0, 11), *[addi(7, 7, 1) for _ in range(8)])
        else:
            p.emit(0x73, addi(7, 0, 29))
        p.finish(fixed_return=name == 'fetch')
        if name == 'fetch':
            p.offset -= 4
            p.emit(addi(1, 0, 3), alu(1, 1, 11, 1, immediate=True), csr(0, 0x300, 1), 0x30200073)
        if name == 'device':
            p.offset -= 4
            p.emit(lw(26, 11), 0x30200073)
        if name == 'interrupt':
            p.offset = 0x800
            p.address(11, 0x5008)
            p.emit(csr(24, 0x300, 0, True), csr(20, 0x342, 0, True), csr(22, 0x341, 0, True), sd(0, 11), 0x30200073)
            p.interrupts = dict(mode=4, mask=1, target=base + 0x200)
        yield 'user_' + name, p
    if protection:
        p = Program(base)
        p.address(10, 0x1000)
        p.emit(addi(2, 0, 31), sd(2, 10), alu(1, 10, 2, 5, immediate=True), csr(0, 0x3b0, 1),
               addi(1, 0, 0x1b), csr(0, 0x3a0, 1), addi(1, 0, 1), alu(1, 1, 17, 1, immediate=True),
               csr(0, 0x300, 1), ld(3, 10), sd(2, 10), amoadd(4, 10, 2),
               ld(7, 10, 8), sd(2, 10, 8), addi(11, 10, 8), amoadd(8, 11, 2),
               csr(5, 0x300, 0, True), csr(0, 0x300, 0), ld(6, 10))
        yield 'user_mprv', p.finish()


def compressed_cases(base, protection=False, sv39=False, config=None):
    p = Program(base)
    p.address(2, 0x1800)
    p.half(0x4485, 0x0495, 0x8526, 0x9526, 0x157d, 0x0505)
    p.emit(addi(11, 10, 3), sd(11, 2))
    p.half(0x6582, 0x0585, 0xe42e, 0x6122)
    p.expected_registers = {9: 6, 10: 12, 11: 16, 2: 16}
    yield 'compressed_integer', p.finish()

    p = Program(base)
    p.offset = 0x3c
    # The initial stream jumps over the sparse bytes to the mixed-width loop.
    p.memory.update((base + 12 + n, (jal(0, 0x3c - 12) >> (8*n)) & 255) for n in range(4))
    p.half(0x4485)
    p.emit(addi(10, 9, 7))
    p.half(0x0505)
    p.expected_registers = {9: 1, 10: 9}
    yield 'compressed_boundary', p.finish()

    for name, parcel in (('illegal', 0), ('breakpoint', 0x9002)):
        p = Program(base)
        p.half(0x4485, parcel, 0x0485)
        p.expected_registers = {9: 2, 23: 1}
        yield 'compressed_' + name, p.finish(resume_offset=p.offset - 2)

    p = Program(base)
    p.emit(addi(20, 0, -1), addi(21, 0, 7), muldiv(22, 20, 21, 5))
    p.pipeline_groups = {base+p.offset: 3}
    p.half(0x4485, 0x4509, 0x458d)
    p.expected_registers = {9: 1, 10: 2, 11: 3}
    yield 'compressed_groups', p.finish()

    p = Program(base)
    p.address(8, 0x100)
    link = base+p.offset+2
    p.half(0x9402, 0x8506)
    p.emit(addi(11, 0, 3))
    p.half(0x15fd, 0xfdfd)
    p.finish()
    p.offset = 0x100
    p.half(0x0485, 0x8082)
    p.expected_registers = {1: link, 9: 1, 10: link, 11: 0}
    yield 'compressed_control', p

    if sv39:
        virtual = 0x40000000
        for kind in ('page', 'success', 'pma', *(('pmp',) if protection else ())):
            p = Program(base)
            def data(address, value, size=8):
                p.memory.update((address + n, value >> (8*n) & 255) for n in range(size))
            for address, value in ((base+0x1008, ((base+0x2000)>>2)|1),
                                   (base+0x2000, ((base+0x3000)>>2)|1),
                                   (base+0x3000, ((base+0x4000)>>2)|0xcb),
                                   (base+0x3008, 0 if kind=='page' else ((base+(0x7000 if kind=='pma' else 0x8000))>>2)|0xcb),
                                   (base+0x600, (8<<60)|((base+0x1000)>>12)),
                                   (base+0x608, virtual+0xffc), (base+0x610, 0x800)):
                data(address, value)
            if protection:
                if kind == 'pmp':
                    p.address(2, 0x8000)
                    p.emit(alu(2, 2, 2, 5, immediate=True), csr(0, 0x3b0, 2), addi(2, 0, 0xf), csr(0, 0x3a0, 2))
                else:
                    p.emit(addi(2, 0, -1), csr(0, 0x3b0, 2), addi(2, 0, 0x1f), csr(0, 0x3a0, 2))
            p.address(10, 0x600)
            p.emit(ld(2, 10), csr(0, 0x180, 2), ld(2, 10, 16), csr(0, 0x300, 2), ld(2, 10, 8), csr(0, 0x341, 2), 0x30200073)
            p.finish(fixed_return=True)
            p.offset = 0x800
            p.emit(csr(20, 0x342, 0, True), csr(21, 0x343, 0, True), csr(25, 0x341, 0, True), addi(23, 23, 1),
                   csr(0, 0x180, 0), 0x00002637, addi(12, 12, -2048), csr(0, 0x300, 12))
            p.address(22, p.stop-base)
            p.emit(csr(0, 0x341, 22), 0x30200073)
            data(base+0x4ffc, 0x85134485, 4)
            if kind == 'success':
                data(base+0x8000, 0x05050074, 4)
                data(base+0x8004, 0x73, 4)
            p.expected_registers = {9: 1, 10: 9 if kind=='success' else base+0x600, 20: 9 if kind=='success' else 12 if kind=='page' else 1,
                                    21: 0 if kind=='success' else virtual+0x1000, 25: virtual+(0x1004 if kind=='success' else 0xffe), 23: 1}
            p.required_fetch = (virtual+0xffc, 0x4485)
            yield 'compressed_page_' + kind, p
            if (config or {}).get('enableZcb'):
                q = deepcopy(p)
                q.memory.update((base + 0x4ffc + byte, (0x9d61 >> (8 * byte)) & 255) for byte in range(2))
                q.required_fetch = (virtual + 0xffc, 0x9d61)
                q.expected_registers.update({9: 0, 10: 8 if kind == 'success' else 0})
                yield 'zcb_page_' + kind, q




def floating_cases(base, flen):
    from floating import FLOATING_ENCODINGS, FLOATING_FEATURES
    for width in ((32,) if flen == 32 else (32, 64)):
        for seed in (range(3) if not flen else (-1,)):
            p = Program(base)
            p.emit(0x000020b7, csr(0, 0x300, 1, True))
            p.address(10, 0x3000)
            p.address(11, 0x2800)
            size = 2 if width == 32 else 3
            values = ((0x3f800000, 0x40000000, 0x40400000), (0xff800001, 0, 0x7f800000), (0x80000000, 0x3f800000, 0x80000000)) if width == 32 else (
                (0x3ff0000000000000, 0x4000000000000000, 0x4008000000000000), (0xfff0000000000001, 0, 0x7ff0000000000000), (0x8000000000000000, 0x3ff0000000000000, 0x8000000000000000))
            for index, operands in enumerate(values):
                if seed >= 0 and index != seed:
                    continue
                for source, value in enumerate(operands, 1):
                    offset = index * 32 + (source - 1) * 8
                    for byte in range(8):
                        p.memory[base + 0x3000 + offset + byte] = (value >> (8 * byte)) & 255
                    p.emit((offset << 20) | (10 << 15) | (size << 12) | (source << 7) | 7)
                p.emit(ld(1, 10, index * 32))
                for name, (encoding, mask, rounding, fp_write, integer_source, minimum) in FLOATING_ENCODINGS.items():
                    if name in FLOATING_FEATURES or minimum > (flen or 64) or encoding & 127 in (7, 0x27) or ((encoding >> 25) & 1) != int(width == 64):
                        continue
                    word = encoding | (1 << 15) | ((2 << 20) & ~mask) | ((3 << 27) & ~mask) | ((0 if fp_write else 6) << 7)
                    p.emit(word, csr(8, 3, 0, True))
                    if fp_write:
                        result_size = 2 if not word & (1 << 25) else 3
                        p.emit((11 << 15) | (result_size << 12) | 0x27, load(7, 11, 0, result_size, True if result_size == 2 else False))
            assert p.offset < 0x800
            yield 'floating_' + str(width) + (f'_disabled_{seed}' if seed >= 0 else ''), p.finish()



def floating_state_cases(base, flen):
    if not flen:
        return
    for width in ((32,) if flen == 32 else (32, 64)):
        size = 2 if width == 32 else 3
        one = 0x3f800000 if width == 32 else 0x3ff0000000000000
        half = 0x33800000 if width == 32 else 0x3ca0000000000000
        def setup():
            p = Program(base)
            p.emit(0x000020b7, csr(0, 0x300, 1, True))
            p.address(10, 0x3000); p.address(11, 0x2800)
            for offset, value in ((0, one), (8, half)):
                for byte in range(8):
                    p.memory[base + 0x3000 + offset + byte] = (value >> (8 * byte)) & 255
            p.emit(load(1, 10, 0, size) | 4, load(2, 10, 8, size) | 4)
            return p
        p = setup()
        for frm in range(8):
            p.emit(csr(0, 2, frm, function=5))
            for mode in (0, 1, 2, 3, 4, 7):
                p.emit(csr(0, 1, 0, function=5), 0x00004fb7, csr(0, 0x300, 31),
                       (int(width == 64) << 25) | (2 << 20) | (1 << 15) | (mode << 12) | 0x53,
                       store(0, 11, 0, size) | 4, load(7, 11, 0, size, size == 2), csr(8, 3, 0, True), csr(9, 0x300, 0, True))
        assert p.offset < 0x800
        yield f'floating_rounding_{width}', p.finish()
        for fault in ('read', 'write'):
            p = setup()
            p.emit(load(0, 10, 0, size) | 4, 0x00004fb7, csr(0, 0x300, 31))
            p.emit((load(0, 10, 256, size) if fault == 'read' else store(0, 10, 256, size)) | 4,
                   store(0, 11, 0, size) | 4, load(7, 11, 0, size, size == 2), csr(8, 0x300, 0, True), csr(9, 3, 0, True))
            p.faults[fault] = base + 0x3100
            p.expected_registers = {7: one, 23: 1}
            yield f'floating_{fault}_fault_{width}', p.finish()
    p = Program(base)
    p.emit(load(0, 0, 1, 2) | 4, store(0, 0, 1, 2) | 4, csr(6, 3, 0, True),
           0x000020b7, csr(0, 0x300, 1, True), 0x3f8000b7, 0xf0008053,
           0x00004fb7, csr(0, 0x300, 31), 0xe0001353, csr(7, 0x300, 0, True),
           0x04000053, 0x00005053, 0x00006053)
    p.expected_registers = {23: 6}
    yield 'floating_state', p.finish()


def floating_extension_cases(base, flen, config):
    from floating import FLOATING_ENCODINGS, FLOATING_FEATURES
    for extension in ('Zfa', 'Zfhmin'):
        names = [name for name, feature in FLOATING_FEATURES.items() if feature == extension and FLOATING_ENCODINGS[name][5] <= (flen or 32)]
        if not flen or not config.get('enable' + extension):
            p = Program(base)
            p.emit(0x000020b7, csr(0, 0x300, 1, True))
            raw = FLOATING_ENCODINGS[names[0]][0]
            p.required_traps = [(base + p.offset, raw)]
            p.emit(raw)
            p.expected_registers = {20: 2, 21: raw, 23: 1}
            yield 'floating_disabled_' + extension.lower(), p.finish()
            continue
        for fmt in (0, 1, 2):
            selected = [name for name in names if (FLOATING_ENCODINGS[name][0] >> 25) & 3 == fmt and FLOATING_ENCODINGS[name][0] & 127 == 0x53]
            if not selected:
                continue
            p = Program(base)
            p.emit(0x000020b7, csr(0, 0x300, 1, True), csr(0, 2, 3, function=5))
            p.address(10, 0x3000); p.address(11, 0x2800)
            offset = 0
            for name in selected:
                encoding, mask, rounding, fp_write, integer_source, _ = FLOATING_ENCODINGS[name]
                source_fmt = (encoding >> 20) & 31 if name.startswith('fcvt.') else fmt
                source_width = {0: 32, 1: 64, 2: 16}[source_fmt]
                values = {16: (0x3e00, 0x7c01, 0x8000), 32: (0x3fc00000, 0x7f800001, 0x80000000), 64: (0x3ff8000000000000, 0x7ff0000000000001, 0x8000000000000000)}[source_width]
                for index in (range(32) if name.startswith('fli.') else range(3)):
                    if not name.startswith('fli.'):
                        raw = values[index] | (((1 << flen) - (1 << source_width)) if source_width < flen else 0)
                        for byte in range(8):
                            p.memory[base + 0x3000 + offset + byte] = (raw >> (8 * byte)) & 255
                        p.emit(ld(1, 10, offset) if integer_source else load(1, 10, offset, 2 if flen == 32 else 3) | 4,
                               load(2, 10, offset, 2 if flen == 32 else 3) | 4)
                        offset += 8
                    word = encoding | (5 << 7) | ((index if name.startswith('fli.') else 1) << 15) | ((2 << 20) & ~mask)
                    word |= (0, 1, 7)[index % 3] << 12 if rounding else 0
                    p.emit(csr(0, 1, 0, function=5), word, csr(6, 3, 0, True))
                    if fp_write:
                        p.emit(store(5, 11, 0, 2 if flen == 32 else 3) | 4, load(7, 11, 0, 2 if flen == 32 else 3, flen == 32))
            assert p.offset < 0x800
            yield f'floating_{extension.lower()}_{fmt}', p.finish()
    if config.get('enableZfhmin'):
        p = Program(base)
        p.emit(0x000020b7, csr(0, 0x300, 1, True))
        p.address(10, 0x3000); p.address(11, 0x2800)
        p.memory.update((base + 0x2802 + byte, 0x5a) for byte in range(6))
        for index, value in enumerate((0x7d01, 0x8000, 0x0001, 0x3c00)):
            p.memory.update((base + 0x3000 + 2 * index + byte, (value >> (8 * byte)) & 255) for byte in range(2))
            p.emit(load(1, 10, 2 * index, 1) | 4, store(1, 11, 0, 1) | 4,
                   ld(7, 11), 0xe4008453, csr(6, 3, 0, True))
            p.emit(0x40208153 | (int(flen == 64) << 25), 0xe00104d3 | (int(flen == 64) << 25))
        p.expected_registers = {6: 16, 7: 0x5a5a5a5a5a5a3c00, 8: 0x3c00, 9: 0x3f800000 if flen == 32 else 0x3ff0000000000000}
        yield 'floating_half_memory', p.finish()
        for fault in ('read', 'write'):
            p = Program(base)
            p.emit(0x000020b7, csr(0, 0x300, 1, True))
            p.address(10, 0x3000)
            p.memory.update({base + 0x3000: 1, base + 0x3001: 0x7d})
            p.emit(load(0, 10, 0, 1) | 4, 0x00004fb7, csr(0, 0x300, 31),
                   (load(0, 10, 256, 1) if fault == 'read' else store(0, 10, 256, 1)) | 4,
                   0xe40003d3, csr(8, 0x300, 0, True))
            p.faults[fault] = base + 0x3100
            p.expected_registers = {7: 0x7d01, 23: 1}
            yield 'floating_half_' + fault + '_fault', p.finish()
        p = Program(base)
        p.emit(0x000020b7, csr(0, 0x300, 1, True))
        p.address(10, 0x3000)
        p.memory.update({base + 0x3000: 0, base + 0x3001: 0x3c})
        p.emit(load(1, 10, 0, 1) | 4, 0x00008137, addi(2, 2, -767),
               0x3f800a37, 0xf00a0053, 0xf00a0153, 0x182001d3)
        wrong = 0xf40100d3
        p.cancelled_value = (base + p.offset + 4, wrong, base + p.offset + 8)
        p.emit(jal(0, 8), wrong, 0xe40083d3, csr(8, 3, 0, True))
        p.expected_registers = {7: 0x3c00, 8: 0, 23: 0}
        yield 'floating_half_cancel', p.finish()


def scalar_cases(base, config):
    from model import SCALAR_ENCODINGS
    for extension in ('Zicond', 'Zimop', 'Zcb', 'Zcmop', 'Zihintpause', 'Zihintntl'):
        if extension not in ('Zihintpause', 'Zihintntl') and not config.get('enable' + extension):
            raw = next(encoding for owner, encoding, _ in SCALAR_ENCODINGS.values() if owner == extension)
            p = Program(base)
            p.required_traps = [(base + p.offset, raw)]
            p.emit(raw)
            p.expected_registers = {20: 2, 21: raw, 23: 1}
            yield 'scalar_' + extension.lower() + '_disabled', p.finish()
            continue
        p = Program(base)
        p.address(8, 0x2800)
        p.emit(addi(9, 0, -128), sd(9, 8))
        for name, (owner, encoding, mask) in SCALAR_ENCODINGS.items():
            if owner != extension or name.startswith('c.') and not config.get('enableC'):
                continue
            dependency = 'M' if name == 'c.mul' else 'Zba' if name == 'c.zext.w' else 'Zbb' if name in ('c.sext.b', 'c.sext.h', 'c.zext.h') else None
            if dependency and not config.get('enable' + dependency, dependency == 'M'):
                continue
            if extension == 'Zicond':
                for condition in (0, 1, -1):
                    p.emit(addi(3, 0, -17), addi(4, 0, condition), encoding | (3 << 15) | (4 << 20) | (6 << 7), add(7, 6, 6))
            elif extension == 'Zimop':
                p.emit(addi(6, 0, 17), encoding | (3 << 15) | ((4 << 20) & ~mask) | (6 << 7), addi(7, 6, 1))
            elif extension == 'Zcb':
                if name in ('c.lbu', 'c.lhu', 'c.lh', 'c.sb', 'c.sh'):
                    p.half(encoding | (1 << 2))
                else:
                    p.emit(addi(8, 0, -128), addi(9, 0, 7))
                    p.half(encoding | ((1 << 2) if name == 'c.mul' else 0))
            elif extension == 'Zcmop':
                register = (encoding >> 7) & 31
                p.emit(addi(register, 0, 17))
                p.half(encoding)
            elif name.startswith('c.'):
                p.half(encoding)
            else:
                p.emit(encoding)
        yield 'scalar_' + extension.lower(), p.finish()
        if extension == 'Zcb':
            for dependency, names in (('M', ('c.mul',)), ('Zba', ('c.zext.w',)), ('Zbb', ('c.sext.b', 'c.sext.h', 'c.zext.h'))):
                if config.get('enable' + dependency, dependency == 'M'):
                    continue
                p = Program(base)
                p.required_traps = []
                for name in names:
                    raw = SCALAR_ENCODINGS[name][1]
                    p.required_traps.append((base + p.offset, raw))
                    p.half(raw, 1)
                p.expected_registers = {20: 2, 21: raw, 23: len(names)}
                yield 'scalar_zcb_requires_' + dependency.lower(), p.finish()


def bitmanip_cases(base):
    from model import BITMANIP_ENCODINGS
    for extension in ('Zba', 'Zbb', 'Zbs'):
        p = Program(base)
        p.address(10, 0x3000)
        for index, value in enumerate((0, -1, 0x8000000080000000, 0x0123456789abcdef)):
            for byte in range(8):
                p.memory[base + 0x3000 + 8 * index + byte] = (value >> (8 * byte)) & 255
            p.emit(ld(1, 10, index * 8), addi(2, 0, (0, 31, 32, 63)[index]))
            for name, (owner, encoding, mask) in BITMANIP_ENCODINGS.items():
                if owner != extension:
                    continue
                for amount in ((0, 31, 32, 63) if mask == 0xfc00707f else (0, 31) if name == 'roriw' else (0,)):
                    rs2 = amount if mask == 0xfc00707f or name == 'roriw' else 0 if mask == 0xfff0707f else 2
                    p.emit(encoding | (1 << 15) | (6 << 7) | (rs2 << 20), add(7, 6, 6))
            p.emit(addi(0, 0, 1))
        assert p.offset < 0x800
        yield 'bitmanip_' + extension.lower(), p.finish()


def integer_cases(base):
    values = (0, 1, -1, 1 << 63, (1 << 63) - 1, 0x80000000, 0xffffffff, 0x80000001)
    for name in ('register', 'immediate', 'word', 'branch'):
        p = Program(base)
        p.address(10, 0x3000)
        for index, value in enumerate(values):
            other = (0, 63, 64, 65, 127, -1, 32, 31)[index]
            for offset, number in ((0, value), (8, other)):
                for byte in range(8):
                    p.memory[base + 0x3000 + 16 * index + offset + byte] = (number >> (8 * byte)) & 255
            p.emit(ld(1, 10, 16 * index), ld(2, 10, 16 * index + 8))
            if name == 'register':
                p.emit(*(alu(6, 1, 2, function) for function in range(8)),
                       alu(6, 1, 2, 0, upper=32), alu(6, 1, 2, 5, upper=32))
            elif name == 'immediate':
                p.emit(*(alu(6, 1, immediate, function, immediate=True) for function in (0, 2, 3, 4, 6, 7)
                         for immediate in (-2048, -1, 0, 1, 2047)))
                p.emit(*(alu(6, 1, amount | upper, function, immediate=True) for function, upper in ((1, 0), (5, 0), (5, 0x400))
                         for amount in (0, 1, 31, 32, 63)))
            elif name == 'word':
                p.emit(*(alu(6, 1, 2, function, word=True, upper=upper) for function, upper in ((0, 0), (0, 32), (1, 0), (5, 0), (5, 32))))
                p.emit(*(alu(6, 1, immediate, 0, word=True, immediate=True) for immediate in (-2048, -1, 0, 1, 2047)))
                p.emit(*(alu(6, 1, amount | upper, function, word=True, immediate=True) for function, upper in ((1, 0), (5, 0), (5, 0x400))
                         for amount in (0, 1, 15, 31)))
            else:
                for function in (0, 1, 4, 5, 6, 7):
                    p.emit(beq(1, 2, 8) | (function << 12), addi(6, 6, 1),
                           beq(1, 1, 8) | (function << 12), addi(7, 7, 1))
                p.emit(beq(1, 1, 2) | (1 << 12), beq(1, 1, 2) | (7 << 12))
        yield 'integer_' + name, p.finish()
    p = Program(base)
    for word in (False, True):
        for function in (1, 5):
            p.emit(*(alu(6, 1, immediate, function, word, True) for immediate in ((32, 0x800) if word else (64, 0x800))))
        p.emit(*(alu(6, 1, 2, function, word, upper=32) for function in (1, 2, 3, 4, 6, 7)))
    p.emit(*(alu(6, 1, 2, function, True) for function in (2, 3, 4, 6, 7)),
           *(alu(6, 1, 1, function, True, True) for function in (2, 3, 4, 6, 7)),
           alu(6, 1, 2, 0, True, upper=2), alu(6, 1, 2, 4, upper=2),
           beq(1, 2, 8) | (2 << 12), beq(1, 2, 8) | (3 << 12), 0x00200073)
    yield 'integer_reserved', p.finish()
    p = Program(base)
    p.emit(0x00100073, addi(7, 0, 29))
    yield 'integer_breakpoint', p.finish()
    for word in (False, True):
        for function in ((0, 4, 5, 6, 7) if word else range(8)):
            p = Program(base)
            p.address(10, 0x3000)
            for index, value in enumerate(values):
                other = (0, -1, 1, -1, 3, 0x80000000, 0xffffffff, 0)[index]
                for offset, number in ((0, value), (8, other)):
                    p.memory.update((base + 0x3000 + 16 * index + offset + byte, (number >> (8 * byte)) & 255) for byte in range(8))
                p.emit(ld(1, 10, 16 * index), ld(2, 10, 16 * index + 8),
                       muldiv(3, 1, 2, function, word), addi(4, 3, 1), muldiv(0, 1, 2, function, word))
            yield f'muldiv_{function}{"w" if word else ""}', p.finish()
    for size in (2, 3):
        for operation in (0, 1, 4, 8, 12, 16, 20, 24, 28):
            p = Program(base)
            p.address(10, 0x1000 + (4 if size == 2 else 0))
            p.address(11, 0x3000)
            p.emit(addi(2, 0, -91), sd(2, 10, -4 if size == 2 else 8), sd(2, 10, 4 if size == 2 else 16))
            for order, (old, operand) in enumerate(((0, -1), (0x80000000, 1), (0xffffffff, 0x80000000), (0x8000000000000000, -1))):
                for offset, number in ((0, old), (8, operand)):
                    for byte in range(8):
                        p.memory[base + 0x3000 + 16 * order + offset + byte] = (number >> (8 * byte)) & 255
                p.emit(ld(2, 11, 16 * order), ld(3, 11, 16 * order + 8), store(2, 10, size=size), amo(operation, 4, 10, 3, order, size),
                       load(5, 10, size=size), amo(operation, 0, 10, 3, order, size))
            p.emit(ld(6, 10, -4 if size == 2 else 8), ld(7, 10, 4 if size == 2 else 16))
            yield f'atomic_{operation}_{size}', p.finish()
    for size in (2, 3):
        p = Program(base)
        p.address(10, 0x1000)
        p.emit(addi(2, 0, -1), sd(2, 10), sd(2, 10, 8))
        for order in range(4):
            p.emit(amo(2, 4, 10, aqrl=order, size=size), amo(3, 5, 10, 2, order, size), amo(3, 6, 10, 2, order, size),
                   amo(2, 4, 10, size=size), amo(3, 5, 10, 2, size=5-size),
                   amo(2, 4, 10, size=size), store(2, 10, size=size), amo(3, 5, 10, 2, size=size))
        yield f'atomic_reservation_{size}', p.finish()
    p = Program(base)
    p.address(10, 0x1000)
    p.emit(addi(2, 0, -1), *(sd(2, 10, offset) for offset in range(0, 64, 8)))
    for size in (0, 1):
        for lane in range(0, 64, 1 << size):
            p.emit(addi(2, 0, -128 if lane % 3 else 127), store(2, 10, lane, size),
                   load(3, 10, lane, size), load(4, 10, lane, size, True))
        p.emit(*(ld(5, 10, lane) for lane in range(0, 64, 8)))
    p.emit(load(3, 10, 1, 1), store(2, 10, 1, 1))
    for offset in (0x3ffe, 0x4ffe, 0x5ffe, 0x6000, 0x9000):
        p.address(10, offset)
        p.emit(load(3, 10, 1, 0), store(2, 10, 1, 0), load(4, 10, 0, 1), store(2, 10, 0, 1))
    yield 'narrow_memory', p.finish()
    for kind in ('read', 'write'):
        p = Program(base)
        p.address(10, 0x1002)
        p.faults[kind] = base + 0x1002
        p.emit(load(2, 10, size=0) if kind == 'read' else store(1, 10, size=1))
        yield 'narrow_bus_' + kind, p.finish()
    p = Program(base)
    for function in (1, 2, 3, 5, 6, 7):
        p.emit(addi(1, 0, 0), csr(6, 0x340, 1, function=function), csr(7, 0x340, 0, True),
               csr(6, 0xf14, 0, function=function), csr(6, 0xf14, 1, function=function),
               addi(1, 0, -1), csr(1, 0x340, 1, function=function), csr(0, 0x340, 31, function=function),
               csr(7, 0x340, 0, True), csr(6, 0x777, 0, function=function))
    p.emit(csr(6, 0x340, 0, function=4))
    yield 'csr_variants', p.finish()


def atomic_cases(base, protection=False):
    p = Program(base)
    p.address(10, 0x1000)
    p.emit(addi(2, 0, -1), sd(2, 10), addi(2, 0, 1))
    for aqrl in range(4):
        p.emit(sd(2, 10, 8), amoadd(3, 10, 2, aqrl), ld(4, 10), ld(5, 10, 8), add(6, 3, 4))
    p.emit(amoadd(0, 10, 2), amoadd(7, 10, 0, 2), amoadd(2, 10, 2, 3), amoadd(10, 10, 2, 1))
    yield 'atomic_ordering', p.finish()
    p = Program(base)
    for offset in (0x4000, 0x5000, 0x6000, 0x7000, 0x9000, 0x1002):
        p.address(10, offset)
        p.emit(amoadd(3, 10, 1))
    p.emit(addi(10, 0, -8), amoadd(3, 10, 1), amoadd(3, 10, 1) | (5 << 27), amoadd(3, 10, 1) ^ (1 << 12))
    yield 'atomic_denied', p.finish()
    for kind in ('read', 'write', 'exclusive', 'retry'):
        p = Program(base)
        p.address(10, 0x1000)
        p.emit(addi(2, 0, 7), amoadd(3, 10, 2, 3), addi(4, 3, 1))
        if kind == 'retry':
            p.exclusive_failures, p.interference = 2, 0
        else:
            p.faults[kind] = base + 0x1000
        yield 'atomic_' + ('retry' if kind == 'retry' else 'fault_' + kind), p.finish()
    p = Program(base)
    p.address(10, 0x1000)
    p.address(11, 0x1800)
    operands = ((0, 0), (0, -1), (-1, 1), (1 << 63, 0x5555555555555555))
    for operation in (1, 8):
        for index, (old, operand) in enumerate(operands):
            for offset, value in ((16 * index, old), (16 * index + 8, operand)):
                p.memory.update((base + 0x1800 + offset + byte, (value >> (8 * byte)) & 255) for byte in range(8))
            p.emit(ld(2, 11, 16 * index), ld(3, 11, 16 * index + 8), sd(2, 10),
                   amo(operation, 4, 10, 3, index), ld(5, 10))
        p.emit(amo(operation, 0, 10, 3), amo(operation, 3, 10, 3), amo(operation, 10, 10, 0))
        p.address(10, 0x1000)
    yield 'amo_operations', p.finish()
    p = Program(base)
    p.address(10, 0x1000)
    p.address(11, 0x1008)
    p.emit(addi(2, 0, 9), amo(3, 3, 10, 2), amo(2, 3, 10), amo(3, 4, 10, 2),
           amo(3, 5, 10, 2), amo(2, 0, 10), amo(3, 0, 10, 2),
           amo(2, 6, 10), amo(2, 7, 11), amo(3, 8, 10, 2), amo(3, 9, 11, 2),
           amo(2, 6, 10), amo(3, 7, 11, 2), amo(3, 8, 10, 2))
    for operation in (0, 1, 8):
        p.emit(amo(2, 6, 10), amo(operation, 7, 11, 2), amo(3, 8, 10, 2))
    p.emit(amo(2, 6, 10), sd(2, 10), amo(3, 7, 10, 2),
           amo(2, 6, 10), sw(2, 10, 4), amo(3, 7, 10, 2),
           amo(2, 6, 10), beq(0, 0, 8), addi(9, 0, 99), amo(3, 7, 10, 2),
           amo(2, 6, 10), amo(2, 7, 10) ^ (1 << 12), amo(3, 8, 10, 2))
    yield 'lrsc_pairing', p.finish()
    p = Program(base)
    for offset in (0x4000, 0x5000, 0x6000, 0x9000, 0x1002):
        p.address(10, offset)
        p.emit(amo(2, 3, 10), amo(3, 4, 10, 2))
    p.emit(addi(10, 0, -8), amo(2, 3, 10), amo(3, 4, 10, 2))
    for operation in (2, 3, 4, 5, 12, 16, 20, 24, 28):
        p.emit(amo(operation, 3, 10, 1) if operation != 3 else amo(operation, 3, 10, 1) ^ (1 << 12))
    yield 'lrsc_denied', p.finish()
    for kind in ('read', 'exclusive', 'write'):
        p = Program(base)
        p.address(10, 0x1000)
        p.emit(addi(2, 0, 13), amo(2, 3, 10), amo(3, 4, 10, 2), amo(3, 5, 10, 2))
        p.faults[kind] = base + 0x1000
        yield 'lrsc_fault_' + kind, p.finish()
    if protection:
        p = Program(base)
        p.address(10, 0x1000)
        p.emit(alu(1, 10, 2, 5, immediate=True), csr(0, 0x3b0, 1), addi(1, 0, 0x99), csr(0, 0x3a0, 1),
               amo(2, 3, 10), amo(3, 4, 10, 2), amo(3, 5, 10, 2), amo(0, 6, 10, 2), amo(1, 7, 10, 2), amo(8, 8, 10, 2))
        yield 'lrsc_pmp', p.finish()


def synchronization_cases(base, writeback=False):
    p = Program(base)
    p.address(10, 0x1000)
    p.emit(addi(2, 0, 11), sd(2, 10), fence(), ld(3, 10), fence(),
           amoadd(4, 10, 2), fence(), ld(5, 10), fence(True))
    for reserved in (0, 0x83328880, 0xffff8f80):
        p.emit(fence(False, reserved), fence(True, reserved), addi(6, 6, 1))
    p.emit(0x200f, 0x700f)
    yield 'fence_ordering', p.finish()
    for instruction in (False, True):
        p = Program(base)
        p.faults['fetch'] = base + p.offset
        p.emit(fence(instruction), addi(6, 0, 37))
        yield 'fence_fetch_fault_' + str(int(instruction)), p.finish()
    p = Program(base)
    p.address(11, 0x3000)
    p.emit(ld(2, 11))
    target = p.offset + 16
    p.address(10, target)
    p.emit(sd(2, 10), fence(True), addi(6, 0, 3), addi(7, 6, 1))
    word = addi(6, 0, 9) | (addi(7, 6, 1) << 32)
    for byte in range(8):
        p.memory[base + 0x3000 + byte] = (word >> (8 * byte)) & 255
    yield 'fence_i_prefetch', p.finish()
    p = Program(base)
    p.address(10, 0x1000)
    p.address(11, 0x3000)
    for _ in range(4):
        p.emit(jalr(29, 10), add(6, 6, 28), jalr(29, 11), add(6, 6, 28))
    for offset, value in ((0x1000, 3), (0x3000, 7)):
        word = addi(28, 0, value) | (jalr(0, 29) << 32)
        for byte in range(8):
            p.memory[base + offset + byte] = (word >> (8 * byte)) & 255
    yield 'cache_replacement', p.finish()
    yield 'synchronization', synchronization_program(base, 1, writeback=writeback)


def pmp_cases(base, writeback=False):
    for name in ('permissions', 'tor_lock', 'partial', 'word', 'fetch', 'update', 'atomic_readonly', 'atomic_none'):
        p = Program(base)
        constant_offset = 0x3000

        def constant(rd, value):
            nonlocal constant_offset
            for byte in range(8):
                p.memory[base + constant_offset + byte] = (value >> (byte * 8)) & 255
            p.address(rd, constant_offset)
            p.emit(ld(rd, rd))
            constant_offset += 8

        p.address(10, 0x1000)
        point = 0x200 if name == 'update' else 0x1004 if name in ('partial', 'word') else 0x1000
        constant(2, ((base + point) >> 2) | (1 if name in ('permissions', 'fetch') else 0))
        p.emit(csr(0, 0x3b0, 2))
        if name == 'tor_lock':
            constant(2, (base + 0x1020) >> 2)
            p.emit(csr(0, 0x3b1, 2))
        constant(3, 0x8900 if name == 'tor_lock' else 0x10 if name == 'partial' else 0x90 if name == 'update' else 0x98 if name == 'atomic_none' else 0x99)
        if name == 'update':
            p.address(1, 0x1fc)
            p.emit(jalr(0, 1))
            p.offset = 0x1fc
        if writeback and name == 'permissions':
            p.emit(ld(16, 10), sd(2, 10))
            p.dirty_permission = base + 0x1000
            p.permission_update_pc = base + p.offset
        p.emit(csr(4, 0x3a0, 3))
        if name == 'word':
            p.emit(lw(5, 10, 4), lw(6, 10, 4, True), ld(7, 10), sw(2, 10, 4))
        elif name.startswith('atomic_'):
            p.emit(amoadd(5, 10, 2, 3), ld(6, 10))
        elif name in ('fetch', 'update'):
            p.emit(jalr(0, 10) if name == 'fetch' else sd(2, 10), mul(5, 2, 3))
        else:
            p.emit(ld(5, 10), sd(2, 10), ld(6, 10))
            p.emit(csr(7, 0x3b0, 0), csr(8, 0x3b1, 0), csr(9, 0x3a0, 0))
            p.emit(csr(11, 0x3b0, 0, True), csr(12, 0x3b1, 0, True), csr(13, 0x3a0, 0, True))
            p.emit(csr(14, 0x3a1, 0, True), csr(15, 0x3a4, 0, True), csr(16, 0x3ef, 0, True))
        if hasattr(p, 'dirty_permission'):
            p.emit(amo(2, 17, 10), ld(18, 10))
        yield 'pmp_' + name, p.finish(fixed_return=name in ('fetch', 'update'))


def interrupt_cases(base, protection):
    names = ('priority', 'store_blocked', 'address_first', 'data_first', 'read_pending', 'fetch_pending',
             'multiply', 'pmp_restart', 'read_fault', 'write_fault', 'fetch_fault', 'branch', 'atomic', 'fence', 'fence_i')
    for mode, name, function in ((mode, name, function) for mode, name in enumerate(names)
                                 for function in ((0, 5) if name == 'multiply' else (0,))):
        if mode == 7 and not protection:
            continue
        p = Program(base)
        p.address(10, 0x1000 if name == 'atomic' else 0x5000)
        p.address(11, 0x5008)
        p.emit(addi(2, 0, -1), csr(0, 0x304, 2), csr(3, 0x344, 0, True),
               csr(4, 0x344, 0), csr(5, 0x344, 0, True), addi(3, 0, 8), csr(0, 0x300, 3))
        if name in ('fetch_pending', 'fetch_fault'):
            p.emit(jal(0, 0x400 - p.offset))
            p.offset = 0x400
        target = base + p.offset
        if name == 'atomic':
            p.emit(amoadd(9, 10, 2, 3))
        if name in ('fence', 'fence_i'):
            p.emit(fence(name == 'fence_i'))
        if mode == 7:
            p.emit(csr(0, 0x3a0, 0))
        if mode == 11:
            p.emit(jal(0, 8), sd(2, 10))
        if mode == 10:
            p.faults['fetch'] = target
        if mode in (8, 9):
            p.faults['read' if mode == 8 else 'write'] = base + 0x5000
        p.emit(sd(2, 10), ld(4, 10), muldiv(6, 2, 2, function), addi(7, 6, 3), jal(0, 8), sd(7, 10))
        p.emit(*[addi(8, 8, 1) for _ in range(16)])
        p.finish()
        p.offset = 0x800
        p.emit(csr(24, 0x300, 0, True), csr(20, 0x342, 0, True), csr(21, 0x343, 0, True),
               csr(22, 0x341, 0, True), csr(25, 0x344, 0, True), addi(23, 23, 1))
        if mode in (8, 9, 10):
            p.emit(addi(26, 0, {8: 5, 9: 7, 10: 1}[mode]), beq(20, 26, 12))
        p.emit(sd(0, 11), 0x30200073)
        if mode in (8, 9, 10):
            p.emit(addi(22, 22, 4), csr(0, 0x341, 22), 0x30200073)
        p.interrupts = dict(mode={8: 4, 9: 1, 10: 5, 11: 7, 12: 8, 13: 7, 14: 7}.get(mode, mode), mask=7 if mode == 0 else 1 << ((mode - 1) % 3), target=target)
        yield 'interrupt_' + ('divide' if function else name), p


def multicore_cases(base, harts, protection=False, interrupts=False, user=False, writeback=False):
    yield 'load_window', load_window_program(base, harts)
    yield 'load_cancel', load_window_program(base, harts, cancel=True)
    if writeback:
        yield from ((name, program) for name, program in data_cache_access_cases(base, protection) if name == 'cache_conflict')
    p = Program(base)
    p.emit(csr(2, 0xf14, 0, True), alu(3, 2, 3, 1, immediate=True))
    p.address(10, 0x1800)
    p.emit(add(10, 10, 3), addi(4, 0, 16))
    p.address(11, 0x2000)
    p.emit(add(11, 11, 3), add(11, 11, 3), addi(7, 2, 1))
    loop = p.offset
    p.emit(ld(5, 10), add(6, 6, 5), addi(10, 10, 8 * harts), addi(4, 4, -1), beq(4, 0, 8), jal(0, loop - p.offset - 20))
    p.emit(sd(6, 11), sd(7, 11, 8))
    for hart in range(harts):
        for iteration in range(16):
            p.memory[base + 0x1800 + 8 * (iteration * harts + hart)] = hart + 1
    p.parallel_reads = dict(rounds=16, results=base + 0x2000)
    yield 'parallel_reads', p.finish()
    if user:
        p = Program(base)
        if protection:
            user_protection(p, data_top=0x1800)
        p.emit(csr(2, 0xf14, 0, True), addi(3, 0, 64), mul(3, 2, 3))
        p.address(10, 0x1000)
        p.emit(add(10, 10, 3))
        p.address(1, 0x200)
        p.emit(csr(0, 0x341, 1), csr(0, 0x300, 0), beq(2, 0, 0x200 - p.offset - 8), 0x30200073)
        p.offset = 0x200
        p.emit(csr(7, 0x340, 0, True), addi(4, 2, 1), sd(4, 10), ld(5, 10), 0x73, addi(6, 5, 1))
        yield 'user_isolation', p.finish()
    yield 'synchronization', synchronization_program(base, harts, writeback)
    yield 'data_coherence', data_coherence_program(base, harts)
    if writeback:
        retry = data_coherence_program(base, harts)
        retry.writeback_failures = 2
        yield 'writeback_retry', retry
        p = Program(base)
        p.emit(csr(2, 0xf14, 0, True), addi(14, 0, 1), addi(7, 0, 0x22), addi(15, 0, 0x33))
        for register, address in ((10, 0x1800), (11, 0x1880), (12, 0x18c0), (13, 0x2000)):
            p.address(register, address)
        p.emit(ld(4, 11))
        dispatch = p.offset
        p.emit(beq(2, 0, 0x100 - dispatch), beq(2, 14, 0x180 - dispatch - 4), jal(0, 0x280 - dispatch - 8))
        p.offset = 0x100
        p.emit(amo(2, 6, 10), sd(14, 11))
        loop = p.offset
        p.emit(ld(5, 12), beq(5, 0, loop - p.offset - 4))
        p.emit(amo(3, 8, 10, 15), ld(9, 10), sd(6, 13), sd(8, 13, 8), sd(9, 13, 16))
        p.emit(jal(0, 0x280 - p.offset))
        p.offset = 0x180
        loop = p.offset
        p.emit(ld(5, 11), beq(5, 0, loop - p.offset - 4), ld(6, 10), store(7, 10, 0, 0), sd(14, 12))
        p.emit(jal(0, 0x280 - p.offset))
        p.offset = 0x280
        p.memory[base + 0x1800] = 0x11
        p.data_cache = dict(minHits=0, minReservedStores=1,
            finalRegisters=[{'6': 0x11, '8': 1, '9': 0x22}, {'6': 0x11, '7': 0x22}, *({} for _ in range(harts - 2))])
        yield 'cache_reservation', p.finish()
    yield from atomic_multicore_cases(base, harts, interrupts)
    for name in ('exchange', *(('protection',) if protection else ()), *(('interrupt',) if interrupts else ())):
        p = Program(base)
        p.emit(csr(2, 0xf14, 0, True), addi(3, 0, 64), mul(3, 2, 3))
        p.address(10, 0x1000)
        p.emit(add(10, 10, 3), addi(4, 2, 1), sd(4, 10), addi(5, 0, harts), beq(4, 5, 12),
               addi(6, 4, 0), jal(0, 8), addi(6, 0, 0), addi(7, 0, 64), mul(7, 6, 7))
        p.address(11, 0x1000)
        p.emit(add(11, 11, 7))
        loop = p.offset
        p.emit(ld(8, 11), beq(8, 0, loop - p.offset - 4))
        p.emit(addi(9, 0, 8))
        loop = p.offset
        p.emit(sd(9, 10, 8), ld(12, 10, 8), addi(9, 9, -1), beq(9, 0, 8), jal(0, loop - p.offset - 16))
        p.address(13, 0x5100)
        p.emit(sd(4, 13), ld(14, 13), jal(0, 8), sd(0, 13))
        if name == 'protection':
            p.emit(beq(2, 0, 8), jal(0, 36))
            constant = (base + 0x1800) >> 2
            for i in range(8):
                p.memory[base + 0x3000 + i] = (constant >> (8 * i)) & 255
            p.address(15, 0x3000)
            p.emit(ld(15, 15), csr(0, 0x3b0, 15), addi(16, 0, 0x99), csr(0, 0x3a0, 16))
            p.emit(csr(17, 0x3a0, 0, True), csr(18, 0x3b0, 0, True))
            p.address(15, 0x1800)
            p.emit(sd(4, 15), ld(19, 15))
        elif name == 'interrupt':
            p.emit(addi(15, 0, -1), csr(0, 0x304, 15), addi(15, 0, 8), csr(0, 0x300, 15))
            target = base + p.offset
            p.emit(sd(4, 10, 16), addi(14, 0, harts - 1), beq(2, 14, 12), beq(2, 0, 16),
                   jal(0, 28), beq(23, 0, 0), jal(0, 20))
            p.address(15, 0x1808)
            loop = p.offset
            p.emit(ld(16, 15), beq(16, 0, loop - p.offset - 4))
            p.emit(ld(19, 10, 16), mul(19, 19, 4), *[addi(19, 19, 1) for _ in range(8)])
            p.interrupts = dict(mode=9, mask=4, target=target, hart=harts - 1)
        else:
            p.emit(beq(2, 0, 8), jal(0, 16))
            p.address(15, 0x1800)
            p.faults['read'] = base + 0x1800
            p.emit(ld(19, 15))
        p.emit(csr(17, 0xf14, 0, True))
        if name != 'interrupt':
            p.emit(csr(18, 0xf14, 0), csr(19, 0xf14, 0, True))
        p.finish()
        if name == 'interrupt':
            p.offset = 0x800
            p.emit(csr(20, 0x342, 0, True), csr(21, 0x343, 0, True), csr(22, 0x341, 0, True), addi(23, 23, 1))
            p.address(25, 0x5008)
            p.emit(sd(0, 25))
            p.address(26, 0x1808)
            p.emit(addi(27, 0, 1), sd(27, 26), 0x30200073)
        yield name, p


def data_cache_program(base):
    p = Program(base)
    initial = 0x1122334455667788
    for offset, value in ((0x1000, initial), (0x1008, 23), (0x1038, 47), (0x3000, 91)):
        p.memory.update((base + offset + byte, (value >> (8 * byte)) & 255) for byte in range(8))
    p.address(10, 0x1000)
    p.address(11, 0x3000)
    p.emit(ld(3, 10), ld(4, 10), ld(5, 10, 8), ld(6, 10, 8), ld(7, 10, 56), ld(8, 10, 56),
           ld(9, 10), ld(12, 11), ld(13, 10), ld(14, 10), addi(2, 0, 0x5a), store(2, 10, 1, 0),
           ld(15, 10), ld(16, 10), addi(2, 0, 0x123), store(2, 10, 2, 1), ld(17, 10), ld(18, 10),
           addi(2, 0, 1), amoadd(19, 10, 2), ld(20, 10), ld(21, 10), amo(2, 22, 10),
           addi(22, 22, 1), amo(3, 24, 10, 22), ld(25, 10), ld(26, 10))
    narrowed = 0x1122334401235a88
    p.data_cache = dict(minHits=9, addresses=[base + 0x1000, base + 0x1008, base + 0x1038],
                        expectedRegisters={'3': initial, '4': initial, '5': 23, '6': 23, '7': 47, '8': 47,
                                           '9': initial, '12': 91, '13': initial, '14': initial,
                                           '15': 0x1122334455665a88, '16': 0x1122334455665a88,
                                           '17': narrowed, '18': narrowed, '19': narrowed,
                                           '20': narrowed + 1, '21': narrowed + 1, '24': 0,
                                           '25': narrowed + 2, '26': narrowed + 2})
    return p.finish()


def data_cache_access_cases(base, protection):
    p = Program(base)
    p.address(10, 0x1000)
    p.address(11, 0x3000)
    p.memory.update({base + 0x1000: 11, base + 0x3000: 17})
    p.emit(addi(3, 0, 0))
    begin = base + p.offset
    p.emit(fence())
    for _ in range(8):
        p.emit(ld(2, 10), add(3, 3, 2), ld(2, 11), add(3, 3, 2))
    end = base + p.offset
    p.emit(fence())
    p.data_cache = dict(minHits=0, conflict=True, expectedRegisters={'3': 224},
                        work=dict(begin=begin, end=end))
    yield 'cache_conflict', p.finish()

    for name, repeats, stride in (('cold', 1, 8), ('warm', 4, 8), ('sparse', 1, 64)):
        p = Program(base)
        p.address(10, 0x1000)
        for index in range(8):
            p.memory[base + 0x1000 + index * stride] = index + 1
        if name == 'warm':
            p.emit(*(ld(2, 10, index * stride) for index in range(8)))
        p.emit(addi(3, 0, 0))
        begin = base + p.offset
        p.emit(fence())
        for _ in range(repeats):
            for index in range(8):
                p.emit(ld(2, 10, index * stride), add(3, 3, 2))
        end = base + p.offset
        p.emit(fence())
        p.data_cache = dict(minHits=0, expectedRegisters={'3': 36 * repeats},
            work=dict(begin=begin, end=end, reads={8: 0 if name == 'warm' else 8,
                                                64: 0 if name == 'warm' else 1 if name == 'cold' else 8}))
        yield 'data_cache_' + name, p.finish()

    p = Program(base)
    initial = 0x8877665544332211
    for size in range(3):
        offset = 0x1000 + 64 * size
        p.memory.update((base + offset + byte, (initial >> (8 * byte)) & 255) for byte in range(8))
        p.address(10, offset)
        p.emit(load(2, 10, 8 - (1 << size), size))
        for width in range(3):
            p.emit(load(3 + 2 * width, 10, 8 - (1 << width), width),
                   load(4 + 2 * width, 10, 8 - (1 << width), width, True))
        p.emit(ld(9, 10))
    p.data_cache = dict(minHits=21, minExpandedReads=3,
                        expectedRegisters={'3': (1 << 64) - 120, '4': 0x88,
                                           '5': (1 << 64) - 0x7789, '6': 0x8877,
                                           '7': (1 << 64) - 0x778899ab, '8': 0x88776655, '9': initial})
    yield 'data_cache_narrow', p.finish()

    p = Program(base)
    p.address(10, 0x1000)
    p.memory[base + 0x1001] = 0x5a
    p.faults['read'] = base + 0x1007
    p.emit(load(3, 10, 1, 0), load(4, 10, 1, 0))
    p.data_cache = dict(minHits=0, minRefillRetries=2, maxExpandedReads=0,
                        expectedRegisters={'3': 0x5a, '4': 0x5a})
    yield 'data_cache_retry', p.finish()

    if protection:
        p = Program(base)
        p.address(10, 0x1000)
        p.memory[base + 0x1039] = 0x5a
        p.emit(alu(2, 10, 2, 5, immediate=True), csr(0, 0x3b0, 2),
               addi(2, 0, 0x90), csr(0, 0x3a0, 2),
               load(3, 10, 57, 0), ld(4, 10, 56), load(5, 10, 57, 0))
        p.data_cache = dict(minHits=2, maxLineReads=0, minExpandedReads=1,
                            expectedRegisters={'3': 0x5a, '4': 0x5a00, '5': 0x5a})
        yield 'data_cache_word_boundary', p.finish()

        p = Program(base)
        p.address(10, 0x1000)
        p.memory[base + 0x1004] = 0x5a
        p.emit(alu(2, 10, 2, 5, immediate=True), csr(0, 0x3b0, 2),
               addi(2, 2, 1), csr(0, 0x3b1, 2), (9 << 12) | (2 << 7) | 0x37,
               addi(2, 2, 0x190), csr(0, 0x3a0, 2),
               lw(3, 10, 4), lw(4, 10, 4), lw(5, 10))
        p.data_cache = dict(minHits=0, maxExpandedReads=0, expectedRegisters={'3': 0x5a, '4': 0x5a})
        yield 'data_cache_boundary', p.finish()


def data_coherence_program(base, harts):
    p = Program(base)
    initial = 0x1122334455667788
    p.memory.update((base + 0x1000 + byte, (initial >> (8 * byte)) & 255) for byte in range(8))
    p.emit(csr(2, 0xf14, 0, True), addi(3, 0, 64), mul(3, 2, 3), addi(4, 0, 1))
    p.address(10, 0x1000)
    p.address(11, 0x2000)
    p.emit(add(11, 11, 3), addi(14, 0, harts))
    for iteration, (size, value, offset) in enumerate(((0, 0x5a, 1), (1, 0x123, 2), (3, 1, 0))):
        p.address(12, 0x1800 + iteration * 64)
        p.address(13, 0x1a00 + iteration * 64)
        p.emit(ld(5, 10), ld(6, 10), amoadd(6, 12, 4))
        loop = p.offset
        p.emit(ld(6, 12), beq(6, 14, 8), jal(0, loop - p.offset - 8), fence(), beq(2, 0, 8))
        skip = p.offset
        p.emit(0, addi(7, 0, value))
        p.emit(amoadd(7, 10, 7) if size == 3 else store(7, 10, offset, size))
        p.emit(fence(), sd(4, 13))
        resume = p.offset
        p.memory.update((base + skip + byte, (jal(0, resume - skip) >> (8 * byte)) & 255) for byte in range(4))
        loop = p.offset
        p.emit(ld(6, 13), beq(6, 0, loop - p.offset - 4), fence(), ld(8, 10), ld(9, 10), sd(8, 11, iteration * 8))
    values = [0x1122334455665a88, 0x1122334401235a88, 0x1122334401235a89]
    p.data_cache = dict(minHits=6, addresses=[base + 0x1000], witnesses=base + 0x2000, stride=64,
                        values=values, finalRegisters=[{'8': values[-1], '9': values[-1]} for _ in range(harts)])
    return p.finish()


def platform_program(base, harts, local_base, wait=False):
    p = Program(base)
    p.emit(csr(2, 0xf14, 0, True), addi(3, 0, 4), mul(3, 2, 3))
    p.address(10, local_base - base)
    p.emit(add(10, 10, 3), addi(3, 0, 8), mul(3, 2, 3))
    p.address(11, local_base - base + 0x4000)
    p.emit(add(11, 11, 3))
    p.address(12, local_base - base + 0xbff8)
    p.address(13, 0x1800)
    p.emit(addi(3, 0, 64), mul(3, 2, 3))
    p.address(14, 0x2000)
    p.emit(add(14, 14, 3), addi(3, 2, 1), addi(4, 0, harts), beq(3, 4, 8), jal(0, 8), addi(3, 0, 0),
           addi(4, 0, 4), mul(3, 3, 4))
    p.address(15, local_base - base)
    p.emit(add(15, 15, 3), addi(5, 0, 1), addi(3, 0, 128), addi(3, 3, 8),
           csr(0, 0x304, 3), addi(3, 0, 8), csr(0, 0x300, 3), amoadd(6, 13, 5))

    def barrier(offset):
        if offset:
            p.emit(addi(9, 13, offset), amoadd(6, 9, 5))
        p.emit(addi(7, 0, harts))
        loop = p.offset
        p.emit(ld(6, 13, offset), beq(6, 7, 8), jal(0, loop - p.offset - 8), fence())

    barrier(0)
    p.address(16, 0x1810)
    p.address(17, 0x2400)
    p.emit(addi(18, 0, 0))
    for iteration in range(3):
        if wait:
            p.emit(csr(0, 0x300, 0), addi(28, 0, 128), csr(0, 0x304, 28))
        p.emit(amoadd(6, 16, 5), addi(7, 6, 1), addi(8, 0, 8), mul(8, 6, 8),
               add(8, 17, 8), sd(7, 8), add(18, 18, 7), fence(), ld(6, 12))
        if wait:
            delay = 2000 * harts
            p.emit((((delay + 2048) >> 12) << 12) | (28 << 7) | 0x37,
                   addi(28, 28, delay - (((delay + 2048) >> 12) << 12)), add(6, 6, 28))
        else:
            p.emit(addi(6, 6, 32))
        p.emit(sd(6, 11), sw(5, 15))
        if wait:
            if iteration == 1:
                p.emit(addi(28, 0, 8), csr(0, 0x300, 28))
            p.emit(0x10500073, addi(28, 0, 136), csr(0, 0x304, 28), addi(28, 0, 8), csr(0, 0x300, 28))
        p.emit(addi(7, 0, iteration + 1))
        loop = p.offset
        p.emit(beq(23, 7, 8), jal(0, loop - p.offset - 4), beq(24, 7, 8), jal(0, loop - p.offset - 12))
        barrier(0x20 + 8 * iteration)
    p.emit(sd(23, 14), sd(24, 14, 8), sd(18, 14, 16), addi(19, 0, 0))
    for ticket in range(3 * harts):
        p.emit(ld(6, 17, 8 * ticket), add(19, 19, 6))
    p.platform = dict(rounds=3, base=local_base, wait=wait)
    p.finish()
    p.offset = 0x800
    p.emit(csr(20, 0x342, 0, True))
    p.address(25, 0x3000)
    p.emit(ld(25, 25), beq(20, 25, 20), addi(25, 0, -1), sd(25, 11), addi(24, 24, 1), 0x30200073,
           sw(0, 10), addi(23, 23, 1), 0x30200073)
    cause = (1 << 63) | 3
    for byte in range(8):
        p.memory[base + 0x3000 + byte] = (cause >> (8 * byte)) & 255
    return p


def synchronization_program(base, harts, writeback=False):
    p = Program(base)
    p.emit(csr(2, 0xf14, 0, True), addi(3, 0, 64), mul(3, 2, 3), addi(5, 0, 1))
    p.address(10, 0x1800)
    p.address(11, 0x2400)
    p.emit(add(11, 11, 3))
    p.address(27, 0x1000)
    p.emit(jalr(29, 27), sd(28, 11), amoadd(6, 10, 5), addi(7, 0, harts))
    loop = p.offset
    p.emit(ld(6, 10), beq(6, 7, 8), jal(0, loop - p.offset - 8), beq(2, 0, 8))
    skip = p.offset
    p.emit(0)
    p.address(26, 0x3000)
    p.emit(ld(26, 26))
    if writeback:
        p.emit(ld(24, 27))
    p.emit(sd(26, 27), fence(), sd(5, 10, 8))
    resume = p.offset
    for byte in range(4):
        p.memory[base + skip + byte] = (jal(0, resume - skip) >> (8 * byte)) & 255
    loop = p.offset
    p.emit(ld(6, 10, 8), beq(6, 0, loop - p.offset - 4), fence(True), jalr(29, 27), sd(28, 11, 8))
    p.address(12, 0x1810)
    p.address(13, 0x2000)
    for iteration in range(3):
        p.emit(amoadd(6, 12, 5), addi(7, 6, 1), addi(8, 0, 8), mul(8, 6, 8),
               add(8, 13, 8), sd(7, 8), add(18, 18, 7), fence())
        p.address(14, 0x1818 + 8 * iteration)
        p.emit(amoadd(6, 14, 5), addi(7, 0, harts))
        loop = p.offset
        p.emit(ld(6, 14), beq(6, 7, 8), jal(0, loop - p.offset - 8), fence())
    p.emit(sd(18, 11, 16))
    p.address(14, 0x1830)
    p.emit(fence(), amoadd(6, 14, 5))
    loop = p.offset
    p.emit(ld(6, 14), beq(6, 7, 8), jal(0, loop - p.offset - 8), fence())
    p.address(12, 0x2410)
    for peer in range(harts):
        p.emit(ld(17, 12, peer * 64), add(19, 19, 17))
    for offset, value in ((0x1000, 3), (0x3000, 9)):
        word = addi(28, 0, value) | (jalr(0, 29) << 32)
        for byte in range(8):
            p.memory[base + offset + byte] = (word >> (8 * byte)) & 255
    p.synchronization = dict(rounds=3, code=base + 0x1000, dirtyCode=writeback)
    return p.finish()


def atomic_multicore_cases(base, harts, interrupts):
    for size, shared in ((size, shared) for size in (2, 3) for shared in (True, False)):
        p = Program(base)
        p.emit(csr(2, 0xf14, 0, True))
        p.address(10, 0x1804 if size == 2 else 0x1800)
        if not shared:
            p.emit(alu(3, 2, 3, 1, immediate=True), add(10, 10, 3))
        if size == 2:
            p.emit(ld(5, 10, -4), addi(4, 0, 87), sw(4, 10, -4))
        p.address(11, 0x2000)
        p.emit(alu(3, 2, 5, 1, immediate=True), add(11, 11, 3))
        for iteration in range(2):
            loop = p.offset
            p.emit(amo(2, 6, 10, aqrl=2, size=size), addi(7, 6, 1), amo(3, 8, 10, 7, 1, size),
                   beq(8, 0, 8), jal(0, loop - (p.offset + 16)), sd(6, 11, iteration * 8))
        p.lrsc = dict(shared=shared, rounds=2, counter=base + (0x1804 if size == 2 else 0x1800), size=1 << size, witnesses=base + 0x2000, stride=32)
        yield 'atomic_lrsc_' + ('shared' if shared else 'private') + ('_word' if size == 2 else ''), p.finish()
    for name in ('atomic', *(('atomic_interrupt',) if interrupts else ())):
        p = Program(base)
        p.emit(csr(2, 0xf14, 0, True), addi(3, 0, 64), mul(3, 2, 3), addi(4, 2, 1), addi(5, 0, 1))
        p.address(10, 0x1800)
        p.address(11, 0x2000)
        p.emit(add(11, 11, 3))
        if name == 'atomic_interrupt':
            p.emit(addi(15, 0, -1), csr(0, 0x304, 15), addi(15, 0, 8), csr(0, 0x300, 15))
            p.interrupts = dict(mode=8, mask=4, target=base + p.offset, hart=harts - 1)
        for iteration in range(4):
            if iteration == 3:
                p.emit(sd(4, 11, 32))
            p.emit(amoadd(6, 10, 5, iteration), sd(6, 11, iteration * 8))
        p.emit(addi(7, 0, 4 * harts + 14))
        loop = p.offset
        p.emit(amoadd(6, 10, 0, 2), beq(6, 7, 8), jal(0, loop - p.offset - 8))
        p.address(12, 0x2020)
        for peer in range(harts):
            p.emit(ld(17, 12, peer * 64), add(18, 18, 17))
        p.exclusive_failures, p.interference = 2, 7
        p.finish()
        if name == 'atomic_interrupt':
            p.offset = 0x800
            p.emit(csr(20, 0x342, 0, True), csr(21, 0x343, 0, True), csr(22, 0x341, 0, True), addi(23, 23, 1))
            p.address(25, 0x5008)
            p.emit(sd(0, 25), 0x30200073)
        yield name, p
