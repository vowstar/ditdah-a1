# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Instruction-level oracle for the implemented scalar operations."""

from floating import floating_decode, floating_value

MASK = (1 << 64) - 1
ATOMIC_OPERATIONS = (0, 1, 4, 8, 12, 16, 20, 24, 28)


def signed(value, bits):
    return (value & ((1 << (bits - 1)) - 1)) - (value & (1 << (bits - 1)))


SCALAR_ENCODINGS = {
    'czero.eqz': ('Zicond', 0x0e005033, 0xfe00707f),
    'czero.nez': ('Zicond', 0x0e007033, 0xfe00707f),
    'pause': ('Zihintpause', 0x0100000f, 0xffffffff),
    **{f'cbo.{name}': ('Zicboz' if operation == 4 else 'Zicbom', operation << 20 | 0x200f, 0xfff07fff)
       for operation, name in ((0, 'inval'), (1, 'clean'), (2, 'flush'), (4, 'zero'))},
    **{f'wrs.{name}': ('Zawrs', encoding, 0xffffffff) for name, encoding in (('nto', 0x00d00073), ('sto', 0x01d00073))},
    **{f'mop.r.{n}': ('Zimop', 0x81c04073 | ((n & 3) << 20) | ((n & 12) << 24) | ((n & 16) << 26), 0xfff0707f) for n in range(32)},
    **{f'mop.rr.{n}': ('Zimop', 0x82004073 | ((n & 3) << 26) | ((n & 4) << 28), 0xfe00707f) for n in range(8)},
    **{f'ntl.{name}': ('Zihintntl', (n << 20) | 0x33, 0xffffffff) for n, name in enumerate(('p1', 'pall', 's1', 'all'), 2)},
    **{f'c.ntl.{name}': ('Zihintntl', 0x9002 | (n << 2), 0xffff) for n, name in enumerate(('p1', 'pall', 's1', 'all'), 2)},
    **{f'c.mop.{n}': ('Zcmop', 0x6001 | (n << 7), 0xffff) for n in range(1, 16, 2)},
    **{name: ('Zcb', value, mask) for name, value, mask in (
        ('c.lbu', 0x8000, 0xfc03), ('c.lhu', 0x8400, 0xfc43), ('c.lh', 0x8440, 0xfc43),
        ('c.sb', 0x8800, 0xfc03), ('c.sh', 0x8c00, 0xfc43), ('c.mul', 0x9c41, 0xfc63),
        ('c.zext.b', 0x9c61, 0xfc7f), ('c.sext.b', 0x9c65, 0xfc7f), ('c.zext.h', 0x9c69, 0xfc7f),
        ('c.sext.h', 0x9c6d, 0xfc7f), ('c.zext.w', 0x9c71, 0xfc7f), ('c.not', 0x9c75, 0xfc7f))}
}


def is_mop(instruction):
    return instruction & 0xb3c0707f == 0x81c04073 or instruction & 0xb200707f == 0x82004073


def compressed_instruction(c, double_precision=False, config=None):
    from programs import add, addi, alu, beq, jal, jalr, ld, load, lw, mul, sd, store, sw
    config = config or {}
    quadrant, function = c & 3, c >> 13
    rd, rs2, a, b = (c >> 7) & 31, (c >> 2) & 31, 8 + ((c >> 7) & 7), 8 + ((c >> 2) & 7)
    bit = lambda n: (c >> n) & 1
    field = lambda low, width: (c >> low) & ((1 << width) - 1)
    immediate = signed((bit(12) << 5) | rs2, 6)
    shift = (bit(12) << 5) | rs2
    if config.get('enableZcmop') and c & 0xf8ff == 0x6081:
        return addi(0, 0, 0)
    if config.get('enableZcb'):
        if c & 0xfc03 == 0x8000:
            return load(b, a, (bit(5) << 1) | bit(6), 0, True)
        if c & 0xfc03 == 0x8400:
            return load(b, a, bit(5) << 1, 1, not bit(6))
        if c & 0xfc03 == 0x8800:
            return store(b, a, (bit(5) << 1) | bit(6), 0)
        if c & 0xfc43 == 0x8c00:
            return store(b, a, bit(5) << 1, 1)
        if c & 0xfc63 == 0x9c41:
            return mul(a, a, b) if config.get('enableM', True) else 0
        unary = c & 0xfc7f
        if unary in (0x9c61, 0x9c75):
            return alu(a, a, 255 if unary == 0x9c61 else -1, 7 if unary == 0x9c61 else 4, immediate=True)
        if unary in (0x9c65, 0x9c69, 0x9c6d) and config.get('enableZbb'):
            return {0x9c65: 0x60401013, 0x9c69: 0x0800403b, 0x9c6d: 0x60501013}[unary] | (a << 15) | (a << 7)
        if unary == 0x9c71 and config.get('enableZba'):
            return 0x0800003b | (a << 15) | (a << 7)
    if double_precision and quadrant in (0, 2) and function in (1, 5):
        if quadrant == 0:
            offset = (field(5, 2) << 6) | (field(10, 3) << 3)
            return ((offset << 20) | (a << 15) | (3 << 12) | (b << 7) | 7) if function == 1 else store(b, a, offset, 3) | 4
        if function == 1:
            offset = (field(2, 3) << 6) | (bit(12) << 5) | (field(5, 2) << 3)
            return (offset << 20) | (2 << 15) | (3 << 12) | (rd << 7) | 7
        offset = (field(7, 3) << 6) | (field(10, 3) << 3)
        return store(rs2, 2, offset, 3) | 4
    if quadrant == 0:
        offset = (field(7, 4) << 6) | (field(11, 2) << 4) | (bit(5) << 3) | (bit(6) << 2)
        if function == 0 and offset:
            return addi(b, 2, offset)
        if function in (2, 3, 6, 7):
            word = function & 1 == 0
            offset = ((bit(5) << 6) | (field(10, 3) << 3) | (bit(6) << 2) if word else
                      (field(5, 2) << 6) | (field(10, 3) << 3))
            return (lw(b, a, offset) if word else ld(b, a, offset)) if function < 4 else (sw(b, a, offset) if word else sd(b, a, offset))
    elif quadrant == 1:
        if function in (0, 1, 2):
            if function == 1:
                return alu(rd, rd, immediate, 0, word=True, immediate=True) if rd else 0
            return addi(rd, rd if function == 0 else 0, immediate)
        if function == 3 and immediate:
            if rd == 2:
                offset = signed((bit(12) << 9) | (field(3, 2) << 7) | (bit(5) << 6) | (bit(2) << 5) | (bit(6) << 4), 10)
                return addi(2, 2, offset)
            return ((immediate & 0xfffff) << 12) | (rd << 7) | 0x37
        if function == 4:
            kind = field(10, 2)
            if kind < 2:
                return alu(a, a, shift | (0x400 if kind else 0), 5, immediate=True)
            if kind == 2:
                return alu(a, a, immediate, 7, immediate=True)
            kind = field(5, 2)
            if not bit(12):
                return alu(a, a, b, (0, 4, 6, 7)[kind]) | ((1 << 30) if kind == 0 else 0)
            if kind < 2:
                return alu(a, a, b, 0, word=True) | ((1 << 30) if kind == 0 else 0)
        if function == 5:
            offset = signed((bit(12) << 11) | (bit(8) << 10) | (field(9, 2) << 8) | (bit(6) << 7) | (bit(7) << 6) | (bit(2) << 5) | (bit(11) << 4) | (field(3, 3) << 1), 12)
            return jal(0, offset)
        if function in (6, 7):
            offset = signed((bit(12) << 8) | (field(5, 2) << 6) | (bit(2) << 5) | (field(10, 2) << 3) | (field(3, 2) << 1), 9)
            return beq(a, 0, offset) | ((function & 1) << 12)
    elif quadrant == 2:
        if function == 0:
            return alu(rd, rd, shift, 1, immediate=True)
        if function in (2, 3) and rd:
            offset = ((field(2, 2) << 6) | (bit(12) << 5) | (field(4, 3) << 2) if function == 2 else
                      (field(2, 3) << 6) | (bit(12) << 5) | (field(5, 2) << 3))
            return lw(rd, 2, offset) if function == 2 else ld(rd, 2, offset)
        if function == 4:
            if rs2:
                return add(rd, rd if bit(12) else 0, rs2)
            if rd:
                return jalr(bit(12), rd, 0)
            if bit(12):
                return 0x00100073
        if function in (6, 7):
            offset = ((field(7, 2) << 6) | (field(9, 4) << 2) if function == 6 else
                      (field(7, 3) << 6) | (field(10, 3) << 3))
            return sw(rs2, 2, offset) if function == 6 else sd(rs2, 2, offset)
    return 0


def atomic_value(operation, old, operand, size):
    assert size in (4, 8) and operation in ATOMIC_OPERATIONS
    mask = (1 << (8 * size)) - 1
    a, b = old & mask, operand & mask
    less = signed(a, 8 * size) < signed(b, 8 * size)
    return {0: a + b, 1: b, 4: a ^ b, 8: a | b, 12: a & b,
            16: a if less else b, 20: b if less else a, 24: min(a, b), 28: max(a, b)}[operation] & mask


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


def muldiv_value(insn, a, b):
    function, word = (insn >> 12) & 7, insn & 127 == 0x3b
    width = 32 if word else 64
    if word and function in (1, 2, 3):
        raise Fault(2, insn)
    if function < 4:
        left = signed(a, 64) if function in (1, 2) else a
        right = signed(b, 64) if function == 1 else b
        value = left * right
        if function:
            value >>= 64
    else:
        left, right = a & ((1 << width) - 1), b & ((1 << width) - 1)
        if not function & 1:
            left, right = signed(left, width), signed(right, width)
        quotient = ((abs(left) // abs(right)) * (-1 if (left < 0) != (right < 0) else 1)
                    if right else (1 << width) - 1)
        value = left - quotient * right if function & 2 else quotient
    return signed(value, 32) if word else value & MASK



BITMANIP_ENCODINGS = {
    name: (extension, ((upper << 25) | (function << 12) | opcode), 0xfe00707f)
    for extension, name, opcode, function, upper in
    [('Zba', f'sh{n}add{suffix}', op, n * 2, 16) for op, suffix in ((0x33, ''), (0x3b, '.uw')) for n in (1, 2, 3)] +
    [('Zba', 'add.uw', 0x3b, 0, 4)] +
    [('Zbb', name, 0x33, function, upper) for name, function, upper in
     (('andn', 7, 32), ('orn', 6, 32), ('xnor', 4, 32), ('min', 4, 5), ('minu', 5, 5), ('max', 6, 5), ('maxu', 7, 5))] +
    [('Zbb', name + suffix, opcode, function, 48) for opcode, suffix in ((0x33, ''), (0x3b, 'w')) for name, function in (('rol', 1), ('ror', 5))] +
    [('Zbb', 'roriw', 0x1b, 5, 48)] +
    [('Zbs', name, 0x33, function, upper) for name, function, upper in (('bclr', 1, 36), ('bext', 5, 36), ('binv', 1, 52), ('bset', 1, 20))]
}
BITMANIP_ENCODINGS.update({name + suffix: ('Zbb', (imm << 20) | 0x1013 | opcode, 0xfff0707f)
    for opcode, suffix in ((0, ''), (8, 'w')) for name, imm in (('clz', 0x600), ('ctz', 0x601), ('cpop', 0x602))})
BITMANIP_ENCODINGS.update({name: ('Zbb', (imm << 20) | function | opcode, 0xfff0707f)
    for name, imm, function, opcode in (('sext.b', 0x604, 0x1000, 0x13), ('sext.h', 0x605, 0x1000, 0x13),
    ('zext.h', 0x080, 0x4000, 0x3b), ('orc.b', 0x287, 0x5000, 0x13), ('rev8', 0x6b8, 0x5000, 0x13))})
BITMANIP_ENCODINGS.update({name: (ext, (upper << 26) | (function << 12) | opcode, 0xfc00707f)
    for name, ext, upper, function, opcode in (('slli.uw', 'Zba', 2, 1, 0x1b), ('rori', 'Zbb', 24, 5, 0x13),
    ('bclri', 'Zbs', 18, 1, 0x13), ('bexti', 'Zbs', 18, 5, 0x13), ('binvi', 'Zbs', 26, 1, 0x13), ('bseti', 'Zbs', 10, 1, 0x13))})


def bitmanip_value(insn, a, b, config):
    for name, (extension, encoding, mask) in BITMANIP_ENCODINGS.items():
        if insn & mask != encoding:
            continue
        if not config.get('enable' + extension):
            raise Fault(2, insn)
        width = 32 if name.endswith('w') and not name.endswith('.uw') else 64
        x = a & ((1 << width) - 1)
        shift = ((insn >> 20) if insn & 127 in (0x13, 0x1b) else b) & (width - 1)
        if name.startswith('sh'):
            value = ((a & 0xffffffff if name.endswith('.uw') else a) << int(name[2])) + b
        elif name in ('add.uw', 'slli.uw'):
            value = (a & 0xffffffff) + b if name == 'add.uw' else (a & 0xffffffff) << shift
        elif name in ('andn', 'orn', 'xnor'):
            value = a & ~b if name == 'andn' else a | ~b if name == 'orn' else ~(a ^ b)
        elif name.startswith(('clz', 'ctz', 'cpop')):
            return width - x.bit_length() if name.startswith('clz') else ((x & -x).bit_length() - 1 if x else width) if name.startswith('ctz') else x.bit_count()
        elif name in ('min', 'minu', 'max', 'maxu'):
            key = (lambda n: n) if name.endswith('u') else (lambda n: signed(n, 64))
            value = (min if name.startswith('min') else max)((a, b), key=key)
        elif name in ('sext.b', 'sext.h', 'zext.h'):
            value = a & 65535 if name == 'zext.h' else signed(a, 8 if name == 'sext.b' else 16)
        elif name in ('orc.b', 'rev8'):
            octets = a.to_bytes(8, 'little')
            value = int.from_bytes(bytes(255 if n else 0 for n in octets), 'little') if name == 'orc.b' else int.from_bytes(octets, 'big')
        elif name.startswith('ro'):
            value = (x << shift) | (x >> ((width - shift) % width)) if name.startswith('rol') else (x >> shift) | (x << ((width - shift) % width))
        else:
            bit = 1 << shift
            value = a & ~bit if name.startswith('bclr') else a ^ bit if name.startswith('binv') else a | bit if name.startswith('bset') else (a >> shift) & 1
        return (signed(value, 32) if width == 32 else value) & MASK
    return None


def integer_value(insn, a, b, config=None):
    config = config or {}
    if insn & 0xfe00707f in (0x0e005033, 0x0e007033):
        if not config.get('enableZicond'):
            raise Fault(2, insn)
        return (0 if (b == 0) == ((insn >> 12) & 7 == 5) else a) & MASK
    bitmanip = bitmanip_value(insn, a, b, config or {})
    if bitmanip is not None:
        return bitmanip

    opcode, function, upper = insn & 127, (insn >> 12) & 7, insn >> 25
    word, immediate = opcode in (0x1b, 0x3b), opcode in (0x13, 0x1b)
    width = 32 if word else 64
    left, right = a & ((1 << width) - 1), signed(insn >> 20, 12) & MASK if immediate else b
    shift = (insn >> 20 if immediate else b) & (width - 1)
    if function == 0 and (immediate or upper in (0, 32)):
        value = left - right if not immediate and upper == 32 else left + right
    elif not immediate and upper == 1:
        return muldiv_value(insn, a, b)
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


def fragment_ranges(address, size):
    offset = 0
    while offset < size:
        length = 1
        while 2 * length <= size - offset and (address + offset) % (2 * length) == 0:
            length *= 2
        yield offset, length
        offset += length


def pmp_allowed(configs, addresses, address, size, kind, pa, privilege=3):
    permission = {'fetch': 4, 'read': 1, 'write': 2, 'atomic': 3, 'management': 3}[kind]
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
            permitted = bool(config & permission) if kind == 'management' else config & permission == permission
            return all(matches) and (privilege == 3 and not config & 128 or permitted)
    return privilege == 3 or not configs


def cache_block_allowed(config, protection, address, zero, privilege):
    base = address & -64
    regions = [next((r for r in config['memoryRegions'] if int(r['base']) <= base + offset and
                    base + offset + 8 <= int(r['base']) + int(r['size'])), None) for offset in range(0, 64, 8)]
    if any(region is None for region in regions):
        return False
    attributes = [{key: value for key, value in region.items() if key not in ('base', 'size')} for region in regions]
    if any(value != attributes[0] for value in attributes[1:]):
        return False
    region = regions[0]
    if not region['readable'] or zero and (not region['writable'] or region['device']):
        return False
    return all(pmp_allowed(*protection, base + offset, 8, 'write' if zero else 'management',
                           config['physicalAddressBits'], privilege) for offset in range(0, 64, 8))


class Fault(Exception):
    def __init__(self, cause, value):
        self.cause, self.value = cause, value


def sv39_walk(address, kind, privilege, satp, status, read_pte):
    if privilege == 3 or satp >> 60 == 0:
        return address
    page_cause, access_cause = {'fetch': (12, 1), 'read': (13, 5), 'write': (15, 7), 'atomic': (15, 7), 'management': (15, 7)}[kind]
    if (signed(address, 39) & MASK) != address:
        raise Fault(page_cause, address)
    table = (satp & ((1 << 44) - 1)) << 12
    for level in (2, 1, 0):
        try:
            pte = read_pte(table + ((address >> (12 + 9 * level)) & 511) * 8)
        except Fault:
            raise Fault(access_cause, address) from None
        flags, ppn = pte & 1023, pte >> 10
        if pte >> 54 or not flags & 1 or flags & 6 == 4:
            raise Fault(page_cause, address)
        if flags & 10:
            user = bool(flags & 16)
            permitted = (bool(flags & 8) if kind == 'fetch' else bool(flags & 4) if kind in ('write', 'atomic')
                         else bool(flags & 2 or flags & 8 and status & (1 << 19)))
            if kind == 'management':
                permitted |= bool(flags & 4)
            permitted &= (user if privilege == 0 else not user or kind != 'fetch' and bool(status & (1 << 18)))
            if not permitted or not flags & 64 or kind in ('write', 'atomic') and not flags & 128 or ppn & ((1 << (9 * level)) - 1):
                raise Fault(page_cause, address)
            offset_bits = 12 + 9 * level
            return (ppn << 12) | (address & ((1 << offset_bits) - 1))
        if not level or flags & 0xd0:
            raise Fault(page_cause, address)
        table = ppn << 12
    raise AssertionError('Unterminated page walk')


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
        self.external_translation = None
        self.monitor = ExclusiveMonitor()
        self.local_reservation = None
        self.atomic_operation, self.sc_eligible = 0, False
        self.pc = int(config['resetVector'])
        self.privilege = 3
        self.registers = [0] * 32
        self.fp_registers = [0] * 32 if config.get("floatingPointBits", 0) else []
        self.fp_state = 0
        self.csrs = {address: 0 for address in (0x300, 0x301, 0x304, 0x305, 0x340,
                                               0x341, 0x342, 0x343, 0x344,
                                               0xf11, 0xf12, 0xf13, 0xf14, 0xf15)}
        if config.get('enableJtag'):
            extensions = dict(I=True, A=config.get('enableA', True), M=config.get('enableM', True),
                C=config.get('enableC', False), F=bool(self.fp_registers), D=config.get('floatingPointBits') == 64,
                S=config.get('enableSupervisorMode', False), U=config.get('enableUserMode', False),
                B=all(config.get('enable'+name) for name in ('Zba', 'Zbb', 'Zbs')))
            self.csrs[0x301] = (2 << 62) | sum(1 << (ord(letter)-ord('A')) for letter, enabled in extensions.items() if enabled)
        if self.fp_registers:
            self.csrs.update({1: 0, 2: 0, 3: 0})
        if config.get('enableUserMode'):
            self.csrs.update({0x306: 0, 0x30a: 0})
        if config.get('enableSupervisorMode'):
            self.csrs.update({address: 0 for address in (0x100, 0x104, 0x105, 0x106, 0x10a,
                0x140, 0x141, 0x142, 0x143, 0x144, 0x180, 0x302, 0x303)})
        self.csrs[0x300] = 2 << 32 if config.get('enableUserMode') else 0x1800
        if config.get('enableSupervisorMode'):
            self.csrs[0x300] |= 2 << 34
        self.csrs[0xf14] = hart_id
        if config['pmpEntries']:
            self.csrs.update({address: 0 for address in (*range(0x3a0, 0x3b0, 2), *range(0x3b0, 0x3f0))})
        self.local_fetch_faults = set()
        self.bus = []
        self.requests = []
        self.request_privileges = []
        self.order = 0
        self.counter_cycle, self.counter_retired, self.counter_request, self.counter_mode = -1, 0, 0, 3
        self.counter_written, self.counter_control, self.time_value = set(), None, 0
        if config.get('enableCounters'):
            self.csrs.update({address: 0 for address in (0xb00, 0xb02, 0x320, *range(0xb03, 0xb20),
                                                       *range(0x323, 0x340), *range(0xc00, 0xc20))})
        if config.get('hpmCounters') and config.get('enableSupervisorMode'):
            self.csrs[0xda0] = 0
        if config.get('enableSstc'):
            self.csrs[0x14d] = MASK

    def begin_cycle(self, cycle, time_value):
        if not self.config.get('enableCounters'):
            return
        assert cycle == self.counter_cycle + 1, 'Missing or repeated counter cycle'
        count = self.config.get('hpmCounters', 0)
        if self.counter_control is not None:
            inhibit, events, mode = self.counter_control
            request = False
            for index, event in ((0, 1), (2, 2), *((n + 3, e) for n, e in enumerate(events))):
                delta = 1 if event & 3 == 1 else self.counter_retired if event & 3 == 2 else 0
                if inhibit >> index & 1 or index >= 3 and event >> {3: 62, 1: 61, 0: 60}[mode] & 1:
                    delta = 0
                address = 0xb00 + index
                if address not in self.counter_written:
                    total = self.csrs[address] + delta
                    self.csrs[address] = total & MASK
                    if index >= 3 and total > MASK:
                        request |= not bool(event >> 63)
                        if 0x320 + index not in self.counter_written:
                            self.csrs[0x320 + index] |= 1 << 63
            self.csrs[0x344] |= self.counter_request << 13
            self.counter_request = int(request)
        self.counter_cycle, self.counter_retired, self.time_value = cycle, 0, time_value & MASK
        self.counter_written.clear()
        self.counter_control = self.csrs[0x320], [self.csrs[0x323 + n] for n in range(count)], self.counter_mode

    def observe_retirement(self, record):
        if self.config.get('enableCounters'):
            self.counter_retired += int(not record[7])
            assert self.counter_retired <= self.config['issueWidth'], 'Too many successful retirements in one cycle'
            self.counter_mode = self.privilege

    def translate(self, address, kind, privilege=None):
        if self.config.get('virtualAddressBits') != 39:
            return address
        privilege = (self.privilege if kind == 'fetch' else self.data_privilege()) if privilege is None else privilege
        if kind != 'fetch' and self.external_translation is not None:
            return self.external_translation(address, kind, privilege)
        def read_pte(physical):
            if not pmp_allowed([self.pmp_config(i) for i in range(self.config['pmpEntries'])],
                    [self.csrs[0x3b0 + i] for i in range(self.config['pmpEntries'])],
                    physical, 8, 'read', self.config['physicalAddressBits'], 1) or not any(
                    int(r['base']) <= physical and physical + 8 <= int(r['base']) + int(r['size'])
                    and r['readable'] and not r['device'] for r in self.config['memoryRegions']):
                raise Fault(5, physical)
            if physical <= self.faults.get('read', -1) < physical + 8:
                raise Fault(5, physical)
            return sum(self.memory.get(physical + i, 0) << (8 * i) for i in range(8))
        return sv39_walk(address, kind, privilege, self.csrs[0x180], self.csrs[0x300], read_pte)

    def access(self, address, size, kind, data=0, fragment=False):
        virtual = address
        permission_kind = {2: 'read', 3: 'write'}.get(self.atomic_operation, 'atomic') if kind == 'atomic' else kind
        data &= (1 << (8 * size)) - 1
        if address % size:
            if self.config.get('enableMisaligned') and kind in ('read', 'write'):
                result = 0
                for offset, length in fragment_ranges(address, size):
                    result |= self.access((address + offset) & MASK, length, kind,
                                          data >> (8 * offset), fragment=True) << (8 * offset)
                return result
            raise Fault({'fetch': 0, 'read': 4, 'write': 6, 'atomic': 6}[permission_kind], address)
        try:
            address = self.translate(address, permission_kind)
        except Fault:
            if kind == 'fetch':
                self.local_fetch_faults.add(self.order)
            raise
        return self.physical_access(virtual, address, size, kind, data, fragment)

    def physical_access(self, virtual, address, size, kind, data=0, fragment=False):
        permission_kind = {2: 'read', 3: 'write'}.get(self.atomic_operation, 'atomic') if kind == 'atomic' else kind
        cause = {'fetch': 1, 'read': 5, 'write': 7, 'atomic': 7, 'management': 7}[permission_kind]
        if fragment and not any(not r['device'] and int(r['base']) <= address and
                                address + size <= int(r['base']) + int(r['size']) for r in self.config['memoryRegions']):
            raise Fault(cause, virtual)
        self.last_physical_address = address
        if kind == 'atomic' and self.atomic_operation == 3:
            self.sc_eligible = self.reservation_candidate == (address, size)
        if self.config['pmpEntries'] and not pmp_allowed(
                [self.pmp_config(i) for i in range(self.config['pmpEntries'])],
                [self.csrs[0x3b0 + i] for i in range(self.config['pmpEntries'])],
                address, size, permission_kind, self.config['physicalAddressBits'],
                self.privilege if kind == 'fetch' else self.data_privilege()):
            if kind == 'fetch':
                self.local_fetch_faults.add(self.order)
            raise Fault(cause, virtual)
        self.requests.append((kind, address, size, data if kind in ('write', 'atomic') else 0))
        self.request_privileges.append(self.privilege if kind == 'fetch' else self.data_privilege())
        permission = {'fetch': 'executable', 'read': 'readable', 'write': 'writable', 'atomic': 'atomic', 'management': 'readable'}[kind]
        allowed = any(int(r['base']) <= address and address + size <= int(r['base']) + int(r['size'])
                      and r.get(permission, False) and (kind != 'atomic' or (r['readable'] and r['writable'] and not r['device']))
                      for r in self.config['memoryRegions'])
        if not allowed:
            raise Fault(cause, virtual)
        if kind != 'management':
            self.bus.append((kind, address, size, data if kind in ('write', 'atomic') else 0))
        if kind != 'fetch' and self.external_access is not None:
            try:
                return self.external_access(address, size, kind, data)
            except Fault as error:
                raise Fault(error.cause, virtual) from None
        if kind == 'atomic' and self.atomic_operation == 3 and not self.sc_eligible:
            return 1
        stages = ('read', 'exclusive') if self.atomic_operation == 2 else ('write',) if self.atomic_operation == 3 else ('read', 'write', 'exclusive')
        failed = address <= self.faults.get(kind, -1) < address + size if kind in ('read', 'fetch') else address == self.faults.get(kind)
        if failed or (kind == 'atomic' and any(
                address <= self.faults.get(k, -1) < address + size if k == 'read' else address == self.faults.get(k) for k in stages)):
            raise Fault(cause, virtual)
        if kind == 'management':
            return 0
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
            if self.local_reservation and self.csrs[0xf14] not in self.monitor.reservations:
                self.local_reservation = None
            for i in range(size):
                self.memory[address + i] = (data >> (8 * i)) & 255
            return old if kind == 'atomic' and self.atomic_operation != 3 else 0
        return old

    def set_interrupts(self, levels):
        self.csrs[0x344] = (self.csrs[0x344] & (0x222 | (0x2000 if self.config.get('hpmCounters') else 0))) | sum(
            ((levels >> index) & 1) << bit for index, bit in enumerate((3, 7, 11)))

    def interrupt_cause(self):
        pending = self.csrs[0x304] & self.read_csr(0x344)
        delegated = self.csrs.get(0x303, 0)
        machine = pending & ~delegated if self.privilege < 3 or self.csrs[0x300] & 8 else 0
        supervisor = pending & delegated if self.privilege == 0 or self.privilege == 1 and self.csrs[0x300] & 2 else 0
        return next(((1 << 63) | bit for mask in (machine, supervisor)
                     for bit in (11, 3, 7, 9, 1, 5, 13) if mask & (1 << bit)), 0)

    def data_privilege(self):
        return (self.csrs[0x300] >> 11) & 3 if self.privilege == 3 and self.csrs[0x300] & (1 << 17) else self.privilege

    def trap(self, pc, cause, value):
        code = cause & ((1 << 63) - 1)
        delegated = self.csrs.get(0x303 if cause >> 63 else 0x302, 0)
        supervisor = self.privilege != 3 and code < 64 and delegated & (1 << code)
        bank = 0x100 if supervisor else 0x300
        self.csrs[bank + 0x41], self.csrs[bank + 0x42], self.csrs[bank + 0x43] = pc & ~(1 if self.config.get('enableC') else 3), cause, value
        status = self.csrs[0x300]
        self.csrs[0x300] = ((status & ~0x122) | (int(self.privilege == 1) << 8) | ((status & 2) << 4)
                           if supervisor else (status & ~0x1888) | (self.privilege << 11) | ((status & 8) << 4))
        self.privilege = 1 if supervisor else 3
        return self.csrs[bank + 5]

    def interrupt(self):
        cause = self.interrupt_cause()
        assert cause, 'Interrupt without independently eligible source'
        pc = self.pc
        target = self.trap(pc, cause, 0)
        self.pc = target
        record = (self.order, pc, 0, target, 0, 0, 0, 1, cause, 0)
        self.order += 1
        return record

    def pmp_config(self, index):
        return (self.csrs[0x3a0 + (index // 8) * 2] >> ((index % 8) * 8)) & 255

    def csr_legal(self, address):
        enabled = self.csrs.get(0x306, 0) & (self.csrs.get(0x106, 0) if self.privilege == 0 and self.config.get('enableSupervisorMode') else MASK)
        return address in self.csrs and (address not in (1, 2, 3) or self.fp_state != 0) and (address >> 8) & 3 <= self.privilege and not (
            address == 0x180 and self.privilege == 1 and self.csrs[0x300] & (1 << 20)) and not (
            0xc00 <= address < 0xc20 and self.privilege < 3 and not enabled >> (address - 0xc00) & 1) and not (
            address == 0x14d and self.privilege < 3 and not (self.csrs.get(0x30a, 0) >> 63 and self.csrs.get(0x306, 0) & 2))

    def read_csr(self, address):
        if 0xc00 <= address < 0xc20:
            return self.time_value if address == 0xc01 else self.csrs[0xb00 + address - 0xc00]
        if address == 0xda0:
            return sum((self.csrs[0x320 + n] >> 63) << n for n in range(3, 32)) & (MASK if self.privilege == 3 else self.csrs[0x306])
        if address == 0x344 and self.config.get('enableSstc') and self.csrs[0x30a] >> 63:
            return (self.csrs[address] & ~32) | (int(self.time_value >= self.csrs[0x14d]) << 5)
        if address in (1, 2, 3):
            return self.csrs[3] & 31 if address == 1 else self.csrs[3] >> 5 if address == 2 else self.csrs[3]
        fp_status = (self.fp_state << 13) | ((1 << 63) if self.fp_state == 3 else 0)
        if address == 0x300:
            return self.csrs[address] | fp_status
        if address == 0x100:
            return (self.csrs[0x300] & ((3 << 32) | 0x122 | (0xc0000 if self.config.get('virtualAddressBits') == 39 else 0))) | fp_status
        if address in (0x104, 0x144):
            return self.read_csr(address + 0x200) & self.csrs[0x303]
        return self.csrs[address]

    def return_from_trap(self, supervisor=False):
        status = self.csrs[0x300]
        if supervisor:
            self.privilege = int(bool(status & 0x100))
            self.csrs[0x300] = (status & ~0x122) | 0x20 | ((status >> 4) & 2)
        else:
            self.privilege = (status >> 11) & 3
            self.csrs[0x300] = (status & ~0x1888) | 0x80 | ((status >> 4) & 8)
        if self.config.get('enableUserMode'):
            if self.privilege < 3:
                self.csrs[0x300] &= ~(1 << 17)
        else:
            self.csrs[0x300] |= 0x1800
        return self.csrs[0x141 if supervisor else 0x341]

    def write_csr(self, address, value):
        if self.config.get('enableCounters'):
            self.counter_written.add(address)
            hpm = ((1 << self.config.get('hpmCounters', 0)) - 1) << 3
            if address in (0x106, 0x306, 0x320):
                self.csrs[address] = value & (hpm | (5 if address == 0x320 else 7))
                return
            if address in (0xb00, 0xb02) or 0xb03 <= address < 0xb20:
                if address in (0xb00, 0xb02) or hpm >> (address - 0xb00) & 1:
                    self.csrs[address] = value & MASK
                return
            if 0x323 <= address < 0x340:
                if hpm >> (address - 0x320) & 1:
                    modes = (1 << 62) | (int(self.config.get('enableSupervisorMode', False)) << 61) | (int(self.config.get('enableUserMode', False)) << 60)
                    self.csrs[address] = (value & ((1 << 63) | modes)) | (value & 3 if value & 3 != 3 else 0)
                return
        if address == 0x14d:
            self.csrs[address] = value & MASK
            return
        if address in (0x10a, 0x30a):
            mask = (0x80 if self.config.get('enableZicboz') else 0) | (0x70 if self.config.get('enableZicbom') else 0)
            if address == 0x30a and self.config.get('enableSstc'):
                mask |= 1 << 63
            if value >> 4 & 3 == 2:
                value &= ~0x30
            self.csrs[address] = value & mask
            return
        if address in (1, 2, 3):
            self.csrs[3] = ((self.csrs[3] & 0xe0) | (value & 31)) if address == 1 else ((self.csrs[3] & 31) | ((value & 7) << 5)) if address == 2 else value & 255
            self.fp_state = 3
            return
        if self.fp_registers and address in (0x100, 0x300):
            self.fp_state = (value >> 13) & 3
        if address == 0x300:
            previous = (value >> 11) & 3
            if self.config.get('enableSupervisorMode'):
                self.csrs[address] = (10 << 32) | (value & (0x7e01aa if self.config.get('virtualAddressBits') == 39 else 0x7201aa)) | ((previous if previous in (0, 1, 3) else 0) << 11)
            else:
                self.csrs[address] = ((2 << 32) | (value & 0x220088) | (0x1800 if previous == 3 else 0)
                                      if self.config.get('enableUserMode') else 0x1800 | (value & 0x88))
        elif address == 0x100:
            mask = 0xc0122 if self.config.get('virtualAddressBits') == 39 else 0x122
            self.csrs[0x300] = (self.csrs[0x300] & ~mask) | (value & mask)
        elif address in (0x302, 0x303):
            self.csrs[address] = value & ((0xb3ff if self.config.get('virtualAddressBits') == 39 else 0x3ff) if address == 0x302 else 0x222 | (0x2000 if self.config.get('hpmCounters') else 0))
        elif address == 0x180 and self.config.get('virtualAddressBits') == 39:
            if value >> 60 == 0:
                self.csrs[address] = 0
            elif value >> 60 == 8 and value & ((1 << 44) - 1) < 1 << (self.config['physicalAddressBits'] - 12):
                self.csrs[address] = (8 << 60) | (value & ((1 << (44 + self.config.get('asidBits', 0))) - 1))
        elif address == 0x304 and self.config.get('enableInterrupts', False):
            self.csrs[address] = value & ((0xaaa if self.config.get('enableSupervisorMode') else 0x888) | (0x2000 if self.config.get('hpmCounters') else 0))
        elif address == 0x104:
            mask = self.csrs[0x303]
            self.csrs[0x304] = (self.csrs[0x304] & ~mask) | (value & mask)
        elif address == 0x344:
            mask = (0x222 if self.config.get('enableSupervisorMode') else 0) | (0x2000 if self.config.get('hpmCounters') else 0)
            if self.config.get('enableSstc') and self.csrs[0x30a] >> 63:
                mask &= ~32
            self.csrs[address] = (self.csrs[address] & ~mask) | (value & mask)
        elif address == 0x144:
            mask = self.csrs[0x303] & (2 | (0x2000 if self.config.get('hpmCounters') else 0))
            self.csrs[0x344] = (self.csrs[0x344] & ~mask) | (value & mask)
        elif address in (0x105, 0x141, 0x305, 0x341):
            self.csrs[address] = value & ~(1 if address in (0x141, 0x341) and self.config.get('enableC') else 3)
        elif address in (0x140, 0x142, 0x143, 0x340, 0x342, 0x343):
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

    def step(self, instruction=None):
        pc, insn, raw = self.pc, 0, 0
        length = 4
        fp_write, fp_value, fp_flags = False, 0, 0
        next_pc = (pc + length) & MASK
        rd, write, value, trap, cause, tval = 0, False, 0, False, 0, 0
        try:
            if instruction is not None:
                raw = instruction
                length = 2 if self.config.get('enableC') and raw & 3 != 3 else 4
                insn = compressed_instruction(raw, self.config.get('floatingPointBits') == 64, self.config) if length == 2 else raw
            elif self.config.get('enableC'):
                first = self.access(pc, 2, 'fetch')
                length = 4 if first & 3 == 3 else 2
                raw = first | (self.access((pc + 2) & MASK, 2, 'fetch') << 16) if length == 4 else first
                insn = compressed_instruction(raw, self.config.get("floatingPointBits") == 64, self.config) if length == 2 else raw
            else:
                raw = insn = self.access(pc, 4, 'fetch')
            next_pc = (pc + length) & MASK
            opcode, rd, funct3 = insn & 127, (insn >> 7) & 31, (insn >> 12) & 7
            rs1, rs2 = (insn >> 15) & 31, (insn >> 20) & 31
            a, b = self.registers[rs1], self.registers[rs2]
            immediate = signed(insn >> 20, 12)
            if opcode == 0x37:
                value, write = signed(insn & 0xfffff000, 32), True
            elif opcode == 0x17:
                value, write = pc + signed(insn & 0xfffff000, 32), True
            elif opcode in (0x13, 0x1b, 0x33, 0x3b):
                if opcode in (0x33, 0x3b) and insn >> 25 == 1 and not self.config.get('enableM', True):
                    raise Fault(2, insn)
                value, write = integer_value(insn, a, b, self.config), True
            elif opcode in (7, 0x27, 0x43, 0x47, 0x4b, 0x4f, 0x53):
                decoded = floating_decode(insn, self.config.get('floatingPointBits', 0), self.config)
                if decoded is None or not self.fp_state:
                    raise Fault(2, insn)
                fp_write, integer_source = decoded[3:5]
                if opcode in (7, 0x27):
                    displacement = immediate if opcode == 7 else signed(((insn >> 25) << 5) | ((insn >> 7) & 31), 12)
                    if opcode == 7:
                        fp_value = self.access((a + displacement) & MASK, 1 << funct3, 'read')
                        width = 8 << funct3
                        if width < self.config['floatingPointBits']:
                            fp_value |= (1 << self.config['floatingPointBits']) - (1 << width)
                    else:
                        self.access((a + displacement) & MASK, 1 << funct3, 'write', self.fp_registers[rs2])
                else:
                    mode = self.csrs[3] >> 5 if funct3 == 7 else funct3
                    try:
                        value, fp_flags = floating_value(insn, a if integer_source else self.fp_registers[rs1],
                            self.fp_registers[rs2], self.fp_registers[insn >> 27], mode, self.config['floatingPointBits'])
                    except ValueError:
                        raise Fault(2, insn) from None
                    fp_value, write = value, not fp_write
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
                value, write, next_pc = pc + length, True, (pc + displacement) & MASK
            elif opcode == 0x67 and funct3 == 0:
                value, write, next_pc = pc + length, True, ((a + immediate) & MASK) & ~1
            elif opcode == 0x03 and funct3 != 7:
                size = 1 << (funct3 & 3)
                value = self.access((a + immediate) & MASK, size, 'read')
                value, write = signed(value, size * 8) if funct3 < 4 else value, True
            elif opcode == 0x23 and funct3 < 4:
                offset = signed(((insn >> 25) << 5) | ((insn >> 7) & 31), 12)
                self.access((a + offset) & MASK, 1 << funct3, 'write', b)
            elif opcode == 0x2f and self.config.get('enableA', True) and funct3 in (2, 3) and insn >> 27 in (*ATOMIC_OPERATIONS, 2, 3) and (insn >> 27 != 2 or rs2 == 0):
                self.atomic_operation = insn >> 27
                self.reservation_candidate = self.local_reservation
                self.sc_eligible = False
                self.local_reservation = None
                value, write = signed(self.access(a, 1 << funct3, 'atomic', b), 8 << funct3), True
                if self.atomic_operation == 2:
                    self.local_reservation = self.last_physical_address, 1 << funct3
            elif opcode == 0x0f and funct3 == 2:
                operation = insn >> 20
                zero = operation == 4
                if insn & 0x00007fff != 0x200f or not (
                        zero and self.config.get('enableZicboz') or operation < 3 and self.config.get('enableZicbom')):
                    raise Fault(2, insn)
                controls = [self.csrs.get(0x30a, 0)] if self.privilege < 3 else []
                if self.privilege == 0 and self.config.get('enableSupervisorMode'):
                    controls.append(self.csrs[0x10a])
                permission = 0x80 if zero else 0x30 if operation == 0 else 0x40
                if any(not control & permission for control in controls):
                    raise Fault(2, insn)
                physical = self.translate(a, 'write' if zero else 'management')
                protection = ([self.pmp_config(i) for i in range(self.config['pmpEntries'])],
                              [self.csrs[0x3b0 + i] for i in range(self.config['pmpEntries'])])
                if not cache_block_allowed(self.config, protection, physical, zero, self.data_privilege()):
                    raise Fault(7, a)
                for offset in (range(0, 64, 8) if zero else (0,)):
                    self.physical_access(a, (physical & -64) + offset, 8, 'write' if zero else 'management')
            elif opcode == 0x0f and funct3 in (0, 1):
                pass
            elif insn & 0xfe007fff == 0x12000073 and self.config.get('virtualAddressBits') == 39:
                if self.privilege == 0 or self.privilege == 1 and self.csrs[0x300] & (1 << 20):
                    raise Fault(2, insn)
            elif insn in (0x00d00073, 0x01d00073) and self.config.get('enableZawrs'):
                if (insn == 0x00d00073 and self.local_reservation and self.privilege < 3
                        and self.csrs[0x300] & (1 << 21)
                        and not self.csrs[0x304] & self.read_csr(0x344)):
                    raise Fault(2, insn)
            elif insn == 0x10500073:
                if (self.config.get('enableSupervisorMode') and self.privilege == 0 or
                        self.privilege < 3 and self.csrs[0x300] & (1 << 21)):
                    raise Fault(2, insn)
            elif is_mop(insn):
                if not self.config.get('enableZimop'):
                    raise Fault(2, insn)
                value, write = 0, True
            elif opcode == 0x73 and funct3 in (1, 2, 3, 5, 6, 7):
                address = insn >> 20
                update = funct3 & 3 == 1 or rs1 != 0
                source = rs1 if funct3 & 4 else a
                if not self.csr_legal(address) or (update and address >> 10 == 3):
                    raise Fault(2, insn)
                value, write = self.read_csr(address), True
                if update:
                    data = source if funct3 & 3 == 1 else value | source if funct3 & 3 == 2 else value & ~source
                    self.write_csr(address, data & MASK)
            elif insn == 0x73:
                raise Fault({0: 8, 1: 9, 3: 11}[self.privilege], 0)
            elif insn == 0x00100073:
                raise Fault(3, pc)
            elif insn == 0x30200073:
                if self.privilege != 3:
                    raise Fault(2, insn)
                next_pc = self.return_from_trap()
            elif insn == 0x10200073 and self.config.get('enableSupervisorMode'):
                if self.privilege == 0 or self.privilege == 1 and self.csrs[0x300] & (1 << 22):
                    raise Fault(2, insn)
                next_pc = self.return_from_trap(True)
            else:
                raise Fault(2, insn)
            if next_pc & (1 if self.config.get('enableC') else 3):
                raise Fault(0, next_pc)
        except Fault as error:
            trap, cause, tval, write = True, error.cause, raw if error.cause == 2 else error.value, False
            next_pc = self.trap(pc, cause, tval)
        if not trap and (fp_write or fp_flags):
            self.fp_state = 3
            self.csrs[3] |= fp_flags
            if fp_write:
                self.fp_registers[rd] = fp_value & ((1 << self.config['floatingPointBits']) - 1)
        write = write and rd != 0
        value = (value & MASK) if write else 0
        if write:
            self.registers[rd] = value
        self.pc = next_pc
        record = (self.order, pc, raw, next_pc, rd, int(write), value, int(trap), cause, tval)
        self.order += 1
        return record
