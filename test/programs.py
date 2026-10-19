# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Generate instruction streams and memory images at test runtime."""

import random


def addi(rd, rs, imm):
    return ((imm & 4095) << 20) | (rs << 15) | (rd << 7) | 0x13


def add(rd, a, b):
    return (b << 20) | (a << 15) | (rd << 7) | 0x33


def mul(rd, a, b):
    return add(rd, a, b) | (1 << 25)


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


def amo(operation, rd, base, rs=0, aqrl=0):
    return (operation << 27) | amoadd(rd, base, rs, aqrl)


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

    def address(self, rd, target):
        distance = target - self.offset
        upper = (distance + 2048) >> 12
        self.emit(((upper & 0xfffff) << 12) | (rd << 7) | 0x17)
        self.emit(addi(rd, rd, distance - (upper << 12)))

    def finish(self, fixed_return=False):
        self.stop = self.base + self.offset
        self.emit(jal(0, 0))
        self.offset = 0x800
        self.emit(csr(24, 0x300, 0, True), csr(20, 0x342, 0, True), csr(21, 0x343, 0, True), csr(22, 0x341, 0, True), addi(23, 23, 1))
        if fixed_return:
            self.address(22, self.stop - self.base)
        else:
            self.emit(addi(22, 22, 4))
        self.emit(csr(0, 0x341, 22), 0x30200073)
        return self


def cases(base, protection=False, interrupts=False, user=False, local_interrupt_base=None):
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
    p.emit(jal(0, 12), 0, 0, csr(4, 0x340, 0, True))
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
    yield from synchronization_cases(base)
    yield 'data_cache', data_cache_program(base)
    yield from atomic_cases(base, protection)
    if protection:
        yield from pmp_cases(base)
    if interrupts:
        yield from interrupt_cases(base, protection)
    if user:
        yield from user_cases(base, protection, interrupts, local_interrupt_base)


def user_protection(p, execute_top=0x1000, data_top=0x1008):
    for index, top in enumerate((execute_top, data_top)):
        p.address(1, top)
        p.emit(alu(1, 1, 2, 5, immediate=True), csr(0, 0x3b0 + index, 1))
    p.emit(addi(1, 0, 0xb), alu(1, 1, 8, 1, immediate=True), addi(1, 1, 0xc), csr(0, 0x3a0, 1))


def user_cases(base, protection=False, interrupts=False, local_interrupt_base=None):
    for name in ('access', 'system', 'wait', *(['protection', 'fetch'] if protection else []),
                 *(['interrupt'] if interrupts else []),
                 *(['device'] if protection and local_interrupt_base is not None else [])):
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
        p.emit(csr(0, 0x341, 1), addi(1, 0, 1 if name == 'wait' else 0),
               alu(1, 1, 21, 1, immediate=True), csr(0, 0x300, 1), 0x30200073)
        p.offset = 0x200
        if name == 'access':
            p.emit(addi(2, 0, 17), sd(2, 10), ld(3, 10), amo(8, 4, 10, 2), amo(2, 5, 10), amo(3, 6, 10, 2))
            if not interrupts:
                p.emit(0x10500073)
        elif name == 'system':
            p.emit(csr(2, 0x300, 0, True), csr(0, 0x340, 10), csr(0, 0xf14, 0),
                   0x30200073, csr(3, 0x180, 0, True), csr(4, 0x306, 0, True), csr(0, 0x306, 10),
                   csr(5, 0x30a, 0, True), csr(0, 0x30a, 10), csr(6, 0xf15, 0, True), fence(), fence(True))
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
           alu(6, 1, 2, 0, True, upper=1), alu(6, 1, 2, 4, upper=1),
           beq(1, 2, 8) | (2 << 12), beq(1, 2, 8) | (3 << 12), 0x00100073)
    yield 'integer_reserved', p.finish()
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


def synchronization_cases(base):
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
    yield 'synchronization', synchronization_program(base, 1)


def pmp_cases(base):
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
        yield 'pmp_' + name, p.finish(fixed_return=name in ('fetch', 'update'))


def interrupt_cases(base, protection):
    names = ('priority', 'store_blocked', 'address_first', 'data_first', 'read_pending', 'fetch_pending',
             'multiply', 'pmp_restart', 'read_fault', 'write_fault', 'fetch_fault', 'branch', 'atomic', 'fence', 'fence_i')
    for mode, name in enumerate(names):
        if mode == 7 and not protection:
            continue
        p = Program(base)
        p.address(10, 0x1000 if name == 'atomic' else 0x5000)
        p.address(11, 0x5008)
        p.emit(addi(2, 0, -1), csr(0, 0x304, 2), csr(3, 0x344, 0, True),
               csr(4, 0x344, 0), csr(5, 0x344, 0, True), addi(3, 0, 8), csr(0, 0x300, 3))
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
        p.emit(sd(2, 10), ld(4, 10), mul(6, 2, 2), addi(7, 6, 3), jal(0, 8), sd(7, 10))
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
        yield 'interrupt_' + name, p


def multicore_cases(base, harts, protection=False, interrupts=False, user=False):
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
    yield 'synchronization', synchronization_program(base, harts)
    yield 'data_coherence', data_coherence_program(base, harts)
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


def synchronization_program(base, harts):
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
    p.emit(ld(26, 26), sd(26, 27), fence(), sd(5, 10, 8))
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
    p.synchronization = dict(rounds=3, code=base + 0x1000)
    return p.finish()


def atomic_multicore_cases(base, harts, interrupts):
    for shared in (True, False):
        p = Program(base)
        p.emit(csr(2, 0xf14, 0, True))
        p.address(10, 0x1800)
        if not shared:
            p.emit(alu(3, 2, 3, 1, immediate=True), add(10, 10, 3))
        p.address(11, 0x2000)
        p.emit(alu(3, 2, 5, 1, immediate=True), add(11, 11, 3))
        for iteration in range(2):
            loop = p.offset
            p.emit(amo(2, 6, 10, aqrl=2), addi(7, 6, 1), amo(3, 8, 10, 7, 1),
                   beq(8, 0, 8), jal(0, loop - (p.offset + 16)), sd(6, 11, iteration * 8))
        p.lrsc = dict(shared=shared, rounds=2, counter=base + 0x1800, witnesses=base + 0x2000, stride=32)
        yield 'atomic_lrsc_' + ('shared' if shared else 'private'), p.finish()
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
