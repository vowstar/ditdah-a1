# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Exact rational oracle for scalar binary floating-point operations."""

from fractions import Fraction
from math import isqrt

MASK = (1 << 64) - 1


def instruction_encodings():
    entries = {}
    for fmt, suffix in ((0, 's'), (1, 'd')):
        minimum = 32 if fmt == 0 else 64
        def put(name, function, selector=None, source=None, fp_write=True, integer_source=False, required=minimum):
            encoding = (function << 27) | (fmt << 25) | 0x53
            mask = 0xfe00007f
            if selector is not None:
                encoding |= selector << 12
                mask |= 0x7000
            if source is not None:
                encoding |= source << 20
                mask |= 0x1f00000
            entries[name] = encoding, mask, selector is None, fp_write, integer_source, required
        for store in (False, True):
            name = ('fs' if store else 'fl') + ('w' if fmt == 0 else 'd')
            entries[name] = ((2 + fmt) << 12) | (0x27 if store else 7), 0x707f, False, not store, True, minimum
        for name, opcode in (('fmadd', 0x43), ('fmsub', 0x47), ('fnmsub', 0x4b), ('fnmadd', 0x4f)):
            entries[name + '.' + suffix] = (fmt << 25) | opcode, 0x0600007f, True, True, False, minimum
        for name, function in (('fadd', 0), ('fsub', 1), ('fmul', 2), ('fdiv', 3), ('fsqrt', 11)):
            put(name + '.' + suffix, function, source=0 if function == 11 else None)
        for function, names in ((4, ('fsgnj', 'fsgnjn', 'fsgnjx')), (5, ('fmin', 'fmax')), (20, ('fle', 'flt', 'feq'))):
            for selector, name in enumerate(names):
                put(name + '.' + suffix, function, selector, fp_write=function != 20)
        put('fclass.' + suffix, 28, 1, 0, False)
        word = 'w' if fmt == 0 else 'd'
        put('fmv.x.' + word, 28, 0, 0, False)
        put('fmv.' + word + '.x', 30, 0, 0, True, True)
        for kind, integer in enumerate(('w', 'wu', 'l', 'lu')):
            put(f'fcvt.{integer}.{suffix}', 24, source=kind, fp_write=False)
            put(f'fcvt.{suffix}.{integer}', 26, source=kind, integer_source=True)
        put('fcvt.' + suffix + ('.s' if fmt else '.d'), 8, source=1-fmt, required=64)
        put('fli.' + suffix, 30, 0, 1)
        for selector, name in ((2, 'fminm'), (3, 'fmaxm'), (4, 'fleq'), (5, 'fltq')):
            put(name + '.' + suffix, 20 if selector > 3 else 5, selector, fp_write=selector < 4)
        for source, name in ((4, 'fround'), (5, 'froundnx')):
            put(name + '.' + suffix, 8, source=source)
        put('fcvt.' + suffix + '.h', 8, source=2)
    entries['fcvtmod.w.d'] = 0xc2801053, 0xfff0707f, False, False, False, 64
    for name, encoding, mask, rounding, fp_write, integer_source, minimum in (
        ('flh', 0x1007, 0x707f, False, True, True, 32),
        ('fsh', 0x1027, 0x707f, False, False, True, 32),
        ('fmv.x.h', 0xe4000053, 0xfff0707f, False, False, False, 32),
        ('fmv.h.x', 0xf4000053, 0xfff0707f, False, True, True, 32),
        ('fcvt.h.s', 0x44000053, 0xfff0007f, True, True, False, 32),
        ('fcvt.h.d', 0x44100053, 0xfff0007f, True, True, False, 64)):
        entries[name] = encoding, mask, rounding, fp_write, integer_source, minimum
    return entries


FLOATING_ENCODINGS = instruction_encodings()
FLOATING_FEATURES = {name: 'Zfa' for name in FLOATING_ENCODINGS if name.startswith(('fli.', 'fminm.', 'fmaxm.', 'fround.', 'froundnx.', 'fleq.', 'fltq.', 'fcvtmod.'))}
FLOATING_FEATURES.update({name: 'Zfhmin' for name in FLOATING_ENCODINGS if name in ('flh', 'fsh', 'fmv.x.h', 'fmv.h.x') or name.startswith('fcvt.') and (name.endswith('.h') or name.startswith('fcvt.h.'))})


def floating_decode(instruction, flen, config=None):
    for name, entry in FLOATING_ENCODINGS.items():
        if name in FLOATING_FEATURES and not (config or {}).get('enable' + FLOATING_FEATURES[name]):
            continue
        encoding, mask, rounding, _, _, minimum = entry
        if flen >= minimum and instruction & mask == encoding and (not rounding or (instruction >> 12) & 7 in (0, 1, 2, 3, 4, 7)):
            return entry
    return None


def parts(raw, width, flen):
    fraction = {16: 10, 32: 23, 64: 52}[width]
    exponent = width - fraction - 1
    canonical = (((1 << exponent) - 1) << fraction) | (1 << (fraction - 1))
    raw = canonical if width < flen and raw >> width != (1 << (flen - width)) - 1 else raw & ((1 << width) - 1)
    sign, field, tail = raw >> (width - 1), (raw >> fraction) & ((1 << exponent) - 1), raw & ((1 << fraction) - 1)
    kind = 'nan' if tail else 'inf' if field == (1 << exponent) - 1 else 'finite'
    if field != (1 << exponent) - 1:
        kind = 'finite'
    power = (field or 1) - ((1 << (exponent - 1)) - 1) - fraction
    magnitude = (tail | ((1 << fraction) if field else 0)) * (Fraction(2) ** power)
    value = -magnitude if sign else magnitude
    return raw, sign, kind, value, bool(kind == 'nan' and not tail & (1 << (fraction - 1)))


def rounded(q, remainder, divisor, mode, sign):
    increment = (remainder * 2 > divisor or remainder * 2 == divisor and q & 1) if mode == 0 else (
        False if mode == 1 else bool(sign) if mode == 2 else not sign if mode == 3 else remainder * 2 >= divisor)
    return q + int(bool(remainder) and increment)


def round_float(value, width, mode, zero_sign=0, root=False):
    fraction = {16: 10, 32: 23, 64: 52}[width]
    exponent_bits = width - fraction - 1
    bias = (1 << (exponent_bits - 1)) - 1
    sign = int(value < 0) if value else zero_sign
    magnitude = abs(value)
    if not magnitude:
        return sign << (width - 1), 0
    numerator, denominator = magnitude.numerator, magnitude.denominator
    exponent = numerator.bit_length() - denominator.bit_length()
    if (numerator < denominator << exponent) if exponent >= 0 else (numerator << -exponent) < denominator:
        exponent -= 1
    if root:
        exponent //= 2
    quantum = max(exponent, 1 - bias) - fraction
    def at(power):
        shift = power * (2 if root else 1)
        n, d = (numerator, denominator << shift) if shift >= 0 else (numerator << -shift, denominator)
        if root:
            q = isqrt(n // d)
            exact = q * q * d == n
            midpoint = 4 * n - (2 * q + 1) ** 2 * d
            increment = mode == 3 or mode in (0, 4) and (midpoint > 0 or midpoint == 0 and (mode == 4 or q & 1))
            return q + int(not exact and increment), not exact
        q, remainder = divmod(n, d)
        return rounded(q, remainder, d, mode, sign), remainder != 0
    q, inexact = at(quantum)
    if q >= 1 << (fraction + 1):
        q >>= 1
        quantum += 1
    if quantum + fraction > bias:
        infinity = mode in (0, 4) or mode == 2 and sign or mode == 3 and not sign
        return (sign << (width - 1)) | (((1 << exponent_bits) - 1) << fraction if infinity else (((1 << exponent_bits) - 2) << fraction) | ((1 << fraction) - 1)), 5
    encoded_exponent = quantum + fraction + bias if q >= 1 << fraction else 0
    # Tininess uses precision rounding with an unbounded exponent range.
    tiny = exponent + int(at(exponent - fraction)[0] >= 1 << (fraction + 1)) < 1 - bias if exponent < 1 - bias else False
    return ((sign << (width - 1)) | (encoded_exponent << fraction) | (q & ((1 << fraction) - 1))), int(inexact) | (2 if inexact and tiny else 0)


def floating_value(instruction, a, b, c, mode, flen):
    opcode, function, fmt, kind = instruction & 127, instruction >> 27, (instruction >> 25) & 3, (instruction >> 20) & 31
    width = {0: 32, 1: 64, 2: 16}.get(fmt, 128)
    if fmt > 2 or width > flen:
        raise ValueError('Unsupported floating-point format')
    fraction = {16: 10, 32: 23, 64: 52}[width]
    exponent_bits = width - fraction - 1
    nan = (((1 << exponent_bits) - 1) << fraction) | (1 << (fraction - 1))
    infinity = ((1 << exponent_bits) - 1) << fraction
    sign_bit = 1 << (width - 1)
    box = lambda x: x | (((1 << flen) - (1 << width)) if width < flen else 0)
    if opcode != 0x53 or function in (0, 1, 2, 3, 8, 11, 24, 26):
        if mode not in range(5):
            raise ValueError('Reserved rounding mode')
    if opcode == 0x53 and function == 30 and kind == 1:
        index = (instruction >> 15) & 31
        if index >= 30:
            return box(infinity if index == 30 else nan), 0
        constants = (Fraction(-1), Fraction(2) ** (-(1 << (exponent_bits - 1)) + 2),
            *[Fraction(2) ** n for n in (-16, -15, -8, -7, -4, -3, -2)],
            Fraction(5, 16), Fraction(3, 8), Fraction(7, 16), Fraction(1, 2), Fraction(5, 8), Fraction(3, 4), Fraction(7, 8),
            1, Fraction(5, 4), Fraction(3, 2), Fraction(7, 4), 2, Fraction(5, 2), 3, 4, 8, 16, 128, 256, 32768, 65536)
        return box(round_float(Fraction(constants[index]), width, 0)[0]), 0
    if opcode == 0x53 and function in (26, 30):
        if function == 30:
            return box(a & (sign_bit * 2 - 1)), 0
        integer_width = 64 if kind & 2 else 32
        integer = a & ((1 << integer_width) - 1)
        if not kind & 1 and integer >> (integer_width - 1):
            integer -= 1 << integer_width
        value, flags = round_float(Fraction(integer), width, mode)
        return box(value), flags
    if opcode == 0x53 and function == 28 and not instruction & 0x1000:
        return ((a & (sign_bit - 1)) - (a & sign_bit)) & MASK, 0
    if opcode == 0x53 and function == 8 and kind in (4, 5):
        source = parts(a, width, flen)
        if source[2] == 'nan':
            return box(nan), 16 if source[4] else 0
        if source[2] == 'inf':
            return box(source[0]), 0
        q, remainder = divmod(abs(source[3].numerator), source[3].denominator)
        integer = rounded(q, remainder, source[3].denominator, mode, source[1]) * (-1 if source[1] else 1)
        return box(round_float(Fraction(integer), width, 0, source[1])[0]), int(kind == 5 and bool(remainder))
    if opcode == 0x53 and function == 8:
        source = parts(a, {0: 32, 1: 64, 2: 16}[kind], flen)
        value, flags = (nan, 16 if source[4] else 0) if source[2] == 'nan' else ((infinity | source[1] * sign_bit, 0) if source[2] == 'inf' else round_float(source[3], width, mode, source[1]))
        return box(value), flags
    pa, pb, pc = (parts(x, width, flen) for x in (a, b, c))
    raw_a, sign_a, kind_a, va, signaling_a = pa
    raw_b, sign_b, kind_b, vb, signaling_b = pb
    if opcode == 0x53 and function == 4:
        selector = (instruction >> 12) & 7
        sign = sign_b if selector == 0 else 1 - sign_b if selector == 1 else sign_a ^ sign_b
        return box((raw_a & (sign_bit - 1)) | sign * sign_bit), 0
    if opcode == 0x53 and function == 28:
        exponent = (raw_a >> fraction) & ((1 << exponent_bits) - 1)
        index = (8 if signaling_a else 9) if kind_a == 'nan' else (0 if sign_a else 7) if kind_a == 'inf' else (3 if sign_a else 4) if not va else (2 if sign_a else 5) if not exponent else (1 if sign_a else 6)
        return 1 << index, 0
    if opcode == 0x53 and function in (5, 20):
        unordered = kind_a == 'nan' or kind_b == 'nan'
        key = lambda p: (0 if p[1] else 2) if p[2] == 'inf' else 1
        less = key(pa) < key(pb) or key(pa) == key(pb) == 1 and va < vb
        equal = not unordered and (va == vb if kind_a == kind_b == 'finite' else kind_a == kind_b == 'inf' and sign_a == sign_b)
        selector = (instruction >> 12) & 7
        if function == 20:
            return int(not unordered and (equal if selector == 2 else less if selector in (1, 5) else less or equal)), 16 if signaling_a or signaling_b or unordered and selector not in (2, 4, 5) else 0
        if selector >= 2 and unordered:
            return box(nan), 16 if signaling_a or signaling_b else 0
        selector &= 1
        value = nan if kind_a == kind_b == 'nan' else raw_b if kind_a == 'nan' else raw_a if kind_b == 'nan' else (
            ((sign_a & sign_b) if selector else (sign_a | sign_b)) * sign_bit if not va and not vb and kind_a == kind_b == 'finite' else raw_a if less != bool(selector) else raw_b)
        return box(value), 16 if signaling_a or signaling_b else 0
    if opcode == 0x53 and function == 24 and kind == 8:
        if fmt != 1 or (instruction >> 12) & 7 != 1:
            raise ValueError('Reserved modular conversion encoding')
        if kind_a != 'finite':
            return 0, 16
        q, remainder = divmod(abs(va.numerator), va.denominator)
        integer = -q if sign_a else q
        flags = 16 if not -(1 << 31) <= integer < 1 << 31 else int(bool(remainder))
        return ((integer & 0x7fffffff) - (integer & 0x80000000)) & MASK, flags
    if opcode == 0x53 and function == 24:
        integer_width, unsigned = (64 if kind & 2 else 32), bool(kind & 1)
        minimum, maximum = (0, (1 << integer_width) - 1) if unsigned else (-(1 << (integer_width - 1)), (1 << (integer_width - 1)) - 1)
        if kind_a != 'finite':
            integer, flags = (minimum if kind_a == 'inf' and sign_a else maximum), 16
        else:
            q, remainder = divmod(abs(va.numerator), va.denominator)
            integer = rounded(q, remainder, va.denominator, mode, sign_a) * (-1 if sign_a else 1)
            flags = 16 if not minimum <= integer <= maximum else int(bool(remainder))
            integer = min(maximum, max(minimum, integer))
        if integer_width == 32:
            integer = (integer & 0x7fffffff) - (integer & 0x80000000)
        return integer & MASK, flags
    if opcode == 0x53 and function in (3, 11):
        if kind_a == 'nan' or function == 3 and kind_b == 'nan':
            return box(nan), 16 if signaling_a or function == 3 and signaling_b else 0
        if function == 11:
            if sign_a and (va or kind_a == 'inf'):
                return box(nan), 16
            value, flags = (infinity, 0) if kind_a == 'inf' else round_float(va, width, mode, sign_a, root=True)
        elif kind_a == kind_b == 'inf' or kind_a == kind_b == 'finite' and not va and not vb:
            value, flags = nan, 16
        elif kind_a == 'inf' or kind_b == 'finite' and not vb:
            value, flags = infinity | (sign_a ^ sign_b) * sign_bit, 8 if kind_a == 'finite' else 0
        elif kind_b == 'inf':
            value, flags = (sign_a ^ sign_b) * sign_bit, 0
        else:
            value, flags = round_float(va / vb, width, mode, sign_a ^ sign_b)
        return box(value), flags
    if opcode == 0x53 and function in (0, 1):
        operands = (pa, pb)
        left, right = va, -vb if function else vb
        left_sign, right_sign = sign_a, sign_b ^ function
        left_inf, right_inf, invalid = kind_a == 'inf', kind_b == 'inf', False
    else:
        operands = (pa, pb) if opcode == 0x53 else (pa, pb, pc)
        product_sign = sign_a ^ sign_b ^ int(opcode != 0x53 and bool(opcode & 8))
        invalid = (kind_a == 'inf' and kind_b == 'finite' and not vb) or (kind_b == 'inf' and kind_a == 'finite' and not va)
        left = va * vb * (-1 if opcode != 0x53 and opcode & 8 else 1)
        left_sign, left_inf = product_sign, 'nan' not in (kind_a, kind_b) and 'inf' in (kind_a, kind_b)
        right, right_sign, right_inf = (Fraction(0), product_sign, False) if opcode == 0x53 else (pc[3] * (-1 if opcode & 4 else 1), pc[1] ^ int(bool(opcode & 4)), pc[2] == 'inf')
    invalid = invalid or left_inf and right_inf and left_sign != right_sign
    if invalid or any(p[2] == 'nan' for p in operands):
        return box(nan), 16 if invalid or any(p[4] for p in operands) else 0
    if left_inf or right_inf:
        return box(infinity | (left_sign if left_inf else right_sign) * sign_bit), 0
    zero_sign = left_sign if not left and not right and left_sign == right_sign else int(mode == 2)
    value, flags = round_float(left + right, width, mode, zero_sign)
    return box(value), flags
