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


def csr(rd, address, rs, set_bits=False):
    return (address << 20) | (rs << 15) | ((2 if set_bits else 1) << 12) | (rd << 7) | 0x73


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


def cases(base, protection=False, interrupts=False):
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
    p.emit(addi(1, 0, -1), csr(2, 0x300, 1), csr(3, 0x300, 0, True),
           csr(4, 0x340, 1), csr(5, 0x340, 0, True), csr(6, 0x301, 0, True),
           csr(7, 0xf14, 0, True), csr(8, 0x304, 1), csr(9, 0x304, 0, True))
    p.emit(0, 0x73, csr(4, 0x777, 0, True), csr(5, 0xf14, 0),
           addi(1, 0, 1), beq(0, 1, 2), beq(0, 0, 2), jal(6, 2))
    p.address(10, 0x1002)
    p.emit(jalr(7, 10), ld(4, 10), sd(1, 10))
    for offset in (0x4000, 0x6000, 0x7000):
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
    for wrong_path in (sd(2, 10), ld(3, 10), csr(0, 0x340, 0), 0):
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
    if protection:
        yield from pmp_cases(base)
    if interrupts:
        yield from interrupt_cases(base, protection)


def pmp_cases(base):
    for name in ('permissions', 'tor_lock', 'partial', 'fetch', 'update'):
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
        point = 0x200 if name == 'update' else 0x1004 if name == 'partial' else 0x1000
        constant(2, ((base + point) >> 2) | (1 if name in ('permissions', 'fetch') else 0))
        p.emit(csr(0, 0x3b0, 2))
        if name == 'tor_lock':
            constant(2, (base + 0x1020) >> 2)
            p.emit(csr(0, 0x3b1, 2))
        constant(3, 0x8900 if name == 'tor_lock' else 0x10 if name == 'partial' else 0x90 if name == 'update' else 0x99)
        if name == 'update':
            p.address(1, 0x1fc)
            p.emit(jalr(0, 1))
            p.offset = 0x1fc
        p.emit(csr(4, 0x3a0, 3))
        if name in ('fetch', 'update'):
            p.emit(jalr(0, 10) if name == 'fetch' else sd(2, 10), mul(5, 2, 3))
        else:
            p.emit(ld(5, 10), sd(2, 10), ld(6, 10))
            p.emit(csr(7, 0x3b0, 0), csr(8, 0x3b1, 0), csr(9, 0x3a0, 0))
            p.emit(csr(11, 0x3b0, 0, True), csr(12, 0x3b1, 0, True), csr(13, 0x3a0, 0, True))
            p.emit(csr(14, 0x3a1, 0, True), csr(15, 0x3a4, 0, True), csr(16, 0x3ef, 0, True))
        yield 'pmp_' + name, p.finish(fixed_return=name in ('fetch', 'update'))


def interrupt_cases(base, protection):
    names = ('priority', 'store_blocked', 'address_first', 'data_first', 'read_pending', 'fetch_pending',
             'multiply', 'pmp_restart', 'read_fault', 'write_fault', 'fetch_fault', 'branch')
    for mode, name in enumerate(names):
        if mode == 7 and not protection:
            continue
        p = Program(base)
        p.address(10, 0x5000)
        p.address(11, 0x5008)
        p.emit(addi(2, 0, -1), csr(0, 0x304, 2), csr(3, 0x344, 0, True),
               csr(4, 0x344, 0), csr(5, 0x344, 0, True), addi(3, 0, 8), csr(0, 0x300, 3))
        target = base + p.offset
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
        p.interrupts = dict(mode={8: 4, 9: 1, 10: 5, 11: 7}.get(mode, mode), mask=7 if mode == 0 else 1 << ((mode - 1) % 3), target=target)
        yield 'interrupt_' + name, p


def multicore_cases(base, harts, protection=False, interrupts=False):
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
            p.emit(sd(4, 10, 16), ld(19, 10, 16), mul(19, 19, 4), *[addi(19, 19, 1) for _ in range(8)])
            p.interrupts = dict(mode=7, mask=4, target=target, hart=harts - 1)
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
            p.emit(sd(0, 25), 0x30200073)
        yield name, p
