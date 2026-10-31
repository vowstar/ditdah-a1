# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Exercise precise core debugging through the native memory harness."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import shutil
import struct
import subprocess

from formal import instance_ports
from programs import Program, addi, alu, amo, beq, csr, ld, muldiv, sd
from verify import compile_tb, compare, configuration, run


def program(name):
    p = Program(0)
    steps, trigger = 0, 0
    if name in ('step', 'step_compressed', 'step_fault', 'step_wfi', 'step_user', 'step_supervisor', 'step_interrupt'):
        steps = 7 if name == 'step_compressed' else 6 if name == 'step' else 3 if name in ('step_user', 'step_supervisor') else 4
    p.emit(addi(4, 0, 9), addi(5, 0, 3), addi(6, 0, 5))
    if name == 'step_multiply':
        steps = 3
        p.offset = 0
        p.emit(muldiv(4, 0, 5), addi(5, 0, 3), addi(6, 0, 5))
    elif name == 'step_compressed':
        p.half(0x0205, 0x0285)
    elif name == 'step_fault':
        p.offset = 12
        p.emit(0xffffffff)
    elif name == 'step_wfi':
        p.offset = 12
        p.emit(0x10500073)
    elif name in ('store', 'atomic', 'load'):
        p.address(10, 0x200)
        p.emit(sd(4, 10))
        if name == 'atomic':
            p.emit(amo(0, 7, 10, 5))
        elif name == 'load':
            p.emit(ld(7, 10), ld(8, 10, 8))
        trigger = {'store': 1, 'atomic': 4, 'load': 5}[name]
    elif name == 'divide':
        p.emit(muldiv(7, 4, 5, 4))
        trigger = 2
    elif name == 'floating':
        p.address(10, 0x200)
        p.emit(0x00002237, csr(0, 0x300, 4, True),
               (ld(1, 10) & ~0x7f) | 7, (ld(2, 10, 8) & ~0x7f) | 7,
               (0x0d << 25) | (2 << 20) | (1 << 15) | (3 << 7) | 0x53,
               (0x71 << 25) | (3 << 15) | (7 << 7) | 0x53)
        p.memory.update(enumerate(struct.pack('<dd', 3.0, 1.5), 0x200))
        trigger = 7
    elif name == 'wfi':
        p.emit(0x10500073)
        trigger = 3
    elif name in ('breakpoint', 'priority'):
        p.emit(0x00100073)
    elif name in ('illegal_dret', 'illegal_dpc'):
        p.emit(0x7b200073 if name == 'illegal_dret' else csr(7, 0x7b1, 0, True))
    elif name != 'exception' and name not in ('step', 'step_compressed', 'step_fault', 'step_wfi', 'step_user', 'step_supervisor', 'step_interrupt'):
        raise ValueError(name)
    p.emit(addi(9, 0, 11))
    p.address(10, 0x220)
    p.emit(sd(9, 10), sd(7, 10, 8), sd(20, 10, 16), sd(23, 10, 24))
    p.finish()
    if name == 'step_interrupt':
        p.offset = 0x800
        p.emit(csr(20, 0x342, 0, True), csr(21, 0x341, 0, True), addi(23, 23, 1))
        p.address(22, 0x5008)
        p.emit(sd(0, 22), 0x30200073)
    p.offset = 0x1000
    p.emit(csr(28, 0x7b2, 28))
    p.address(28, 0x3000)
    p.emit(sd(29, 28), sd(30, 28, 8), sd(31, 28, 16), ld(29, 28, 24),
           addi(29, 29, 1), sd(29, 28, 24), addi(29, 29, -1),
           alu(29, 29, 5, 1, immediate=True),
           alu(29, 28, 29, 0), csr(30, 0x7b0, 0, True), csr(31, 0x7b1, 0, True),
           sd(31, 29, 0x100), sd(30, 29, 0x108), csr(31, 0x342, 0, True),
           sd(31, 29, 0x110), csr(31, 0x341, 0, True), sd(31, 29, 0x118))
    if name == 'exception':
        p.emit(ld(29, 28, 48), beq(29, 0, 16) ^ 0x1000)
        # The first visit faults; the exception handler marks the next visit.
        p.address(29, 0x6000)
        p.emit(ld(31, 29))
    if name in ('breakpoint', 'priority'):
        p.emit(alu(31, 30, 6, 5, immediate=True), alu(31, 31, 7, 7, immediate=True),
               addi(31, 31, -1), beq(31, 0, 16) ^ 0x1000,
               csr(31, 0x7b1, 0, True), addi(31, 31, 4), csr(0, 0x7b1, 31))
    p.emit(csr(31, 0x7b0, 0, True), alu(31, 31, -5, 7, immediate=True),
           ld(29, 28, 24), alu(29, 29, steps + 1, 3, immediate=True),
           alu(29, 29, 2, 1, immediate=True), alu(31, 31, 29, 6))
    if name in ('breakpoint', 'priority'):
        p.emit(0x00008eb7, alu(31, 31, 29, 6))
    if name in ('step_user', 'step_supervisor'):
        p.emit(ld(29, 28, 24), addi(29, 29, -1), beq(29, 0, 8) ^ 0x1000,
               alu(31, 31, -4, 7, immediate=True))
        if name == 'step_supervisor':
            p.emit(alu(31, 31, 1, 6, immediate=True))
        p.address(29, 0x800)
        p.emit(csr(0, 0x305, 29))
    if name == 'step_interrupt':
        p.emit(addi(29, 0, 0x80), csr(0, 0x304, 29, True), addi(29, 0, 8), csr(0, 0x300, 29, True))
    if name == 'step_multiply':
        p.emit(ld(29, 28, 24), addi(29, 29, -1), beq(29, 0, 8) ^ 0x1000, addi(5, 0, -1))
    p.emit(csr(0, 0x7b0, 31), ld(29, 28), ld(30, 28, 8), ld(31, 28, 16),
           csr(28, 0x7b2, 28), 0x7b200073)
    p.offset = 0x1800
    p.address(28, 0x3000)
    p.emit(addi(29, 0, 1), sd(29, 28, 48), 0x00100073)
    return p, steps, trigger


def check(name, log, steps, trigger):
    text = log.read_text()
    assert 'PASS\n' in text
    values = {int(a, 16): int(v, 16) for a, v in re.findall(r'^DEBUG_VALUE (\w+) (\w+)$', text, re.M)}
    events = [(int(c), int(n), int(pc, 16)) for c, n, pc in re.findall(r'^DEBUG_ENTER (\d+) (\d+) (\w+)$', text, re.M)]
    assert events and len(events) == (steps + 1 if steps else 3 if name == 'priority' else 2 if name == 'breakpoint' else 1), (name, events)
    assert values[0x3018] == len(events) + int(name == 'exception'), (name, values[0x3018], events)
    for index, (_, retired, expected_pc) in enumerate(events):
        pc, dcsr, cause, epc = (values[0x3100 + index * 32 + offset] for offset in (0, 8, 16, 24))
        expected_cause = 3 if name == 'priority' and index == 1 else 1 if name in ('breakpoint', 'priority') and index else 4 if index else 3
        assert (dcsr >> 6) & 7 == expected_cause, (name, index, hex(dcsr))
        assert dcsr >> 28 == 4 and not dcsr & (1 << 11), (name, hex(dcsr))
        assert pc == expected_pc, (name, index, hex(pc), hex(expected_pc))
        if index and steps:
            assert retired - events[index - 1][1] == 1, (name, events)
        if name in ('breakpoint', 'priority'):
            assert cause == epc == 0, (name, cause, epc)
    traces = [[int(v, 16) for v in line.split()[1:]] for line in text.splitlines() if line.startswith('TRACE ')]
    assert all(not 0x1000 <= record[1] < 0x2000 for record in traces), name
    assert values[0x220] == 11, (name, values[0x220])
    if name in ('illegal_dret', 'illegal_dpc', 'step_user', 'step_supervisor'):
        assert values[0x230] == 2 and values[0x238] == 1, (name, values[0x230], values[0x238])
    if name == 'step_fault':
        assert events[-1][2] == 0x800 and values[0x230] == 2, events
    if name in ('step_user', 'step_supervisor'):
        assert values[0x3128] & 3 == int(name == 'step_supervisor') and events[-1][2] == 0x800
    if name == 'step_interrupt':
        assert all(values[0x3110 + i*32] == values[0x3118 + i*32] == 0 for i in range(len(events)))
        assert values[0x230] == (1 << 63) | 7 and values[0x238] == 1
        assert sum(bool(r[7] and r[8] >> 63) for r in traces) == 1 and 'IRQ_START 4' in text
    if name == 'divide':
        assert values[0x228] == 3
    if name == 'floating':
        assert values[0x228] == int.from_bytes(struct.pack('<d', 2.0), 'little')
    if name == 'atomic':
        assert values[0x200] == 12 and values[0x228] == 9
    if name == 'load':
        assert values[0x228] == 9
    if name == 'exception':
        assert values[0x3030] == 1
        assert values[0x3130] == values[0x3138] == 0
    assert text.count('DEBUG_EXIT ') == len(events), name
    return dict(name=name, entries=len(events), retirements=len(traces), trigger=trigger)


def negative_controls(output, config):
    reports = []
    for kind, case in [('early', 'store'), ('step', 'step_multiply')]:
        work = output / 'mutations' / kind
        shutil.copytree(output / 'rtl', work / 'rtl', dirs_exist_ok=True)
        shutil.copytree(output / 'memory', work / 'memory', dirs_exist_ok=True)
        path = work / 'rtl/DitDahA1Backend.sv'
        body = path.read_text()
        pins = instance_ports(body, 'DitDahA1Csr')[0][1]
        if kind == 'early':
            body, count = re.subn(r'\.debug_enter\s*\([^()]*\)',
                                  '.debug_enter(debug_haltReq & ~debug_mode)', body)
            assert count == 1
        else:
            assignment = next(m for m in re.finditer(r'stepIssued <=\s*[^;]+;', body)
                              if pins['debug_step'] in m[0])
            retire = instance_ports(body, 'DitDahA1Commit')[0][1]
            body = body[:assignment.start()] + f"stepIssued <= ({retire['output_valid']}) & ({pins['debug_step']}) | ~({pins['debug_mode']}) & stepIssued;" + body[assignment.end():]
        path.write_text(body)
        binary = compile_tb(work / 'rtl', work, config['axiDataBits'], config['physicalAddressBits'],
                            'memory_tb', Path('test/memory_tb.sv').resolve(), [(work / 'memory/DitDahA1Memory.sv').resolve()])
        p, _, trigger = program(case)
        image = work / 'image.hex'
        image.write_text('@0\n' + '\n'.join(f'{p.memory.get(i, 0):02x}' for i in range(0x4000)) + '\n')
        log = work / 'run.log'
        with log.open('w') as stream:
            result = subprocess.run([binary, f'+IMAGE={image.resolve()}', '+BASE=0', f'+STOP={p.stop:x}',
                                     '+SEED=17', f'+DEBUG_TRIGGER={trigger}'], stdout=stream, stderr=subprocess.STDOUT,
                                    timeout=60, preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_CORE, (0, 0)))
        text = log.read_text()
        if kind == 'early':
            assert result.returncode != 0 and 'Debug entry before accepted data drain' in text
        else:
            events = [int(n) for n in re.findall(r'^DEBUG_ENTER \d+ (\d+)', text, re.M)]
            assert result.returncode == 0 and 'PASS\n' in text and len(events) >= 2
            assert any(b - a > 1 for a, b in zip(events, events[1:])), events
        reports.append(dict(mutation=kind, case=case, expectedFailure=True))
    return reports


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--config', type=Path)
    group.add_argument('--profile', choices=('single', 'wide', 'floating', 'supervisor'))
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--use-generated', action='store_true')
    parser.add_argument('--case', action='append', dest='selected')
    parser.add_argument('--mutations', action='store_true')
    parser.add_argument('--quiet-only', action='store_true')
    args = parser.parse_args()
    inputs = [Path(__file__), Path('test/debug_driver.svh'), Path('test/memory_tb.sv'), Path('test/verify.py'),
              Path('test/programs.py'), Path('test/formal.py'), Path('test/contracts.py'), Path('test/core_tb.sv'), Path('test/model.py')]
    test_hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    output = args.output
    output.mkdir(parents=True, exist_ok=True)
    if args.config is None:
        wide = args.profile != 'single'
        config = dict(configuration(64),
                      enableJtag=True, enableInterrupts=wide, enableUserMode=wide, enableC=wide,
                      issueWidth=3 if wide else 1, loadQueueEntries=2 if wide else 1,
                      enableSupervisorMode=args.profile == 'supervisor',
                      floatingPointBits=64 if args.profile == 'floating' else 0)
        args.config = output / 'input.json'
        args.config.write_text(json.dumps(config, indent=2) + '\n')
    rtl = output / 'rtl'
    if not args.use_generated:
        run(['build-ditdah-a1', '--top', 'DitDahA1Core', '--trace', '--config', args.config,
             '--output', rtl], output / 'build.log')
        run(['build-ditdah-a1', '--top', 'DitDahA1MemoryFabric', '--config', args.config,
             '--output', output / 'memory'], output / 'memory-build.log')
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    config = manifest['parameters']
    expected = json.loads(args.config.read_text())
    for key, value in expected.items():
        if key == 'memoryRegions':
            assert len(config[key]) == len(value) and all(all(actual[k] == v for k, v in region.items())
                    for actual, region in zip(config[key], value)), 'Stale memory map'
        else:
            assert config[key] == value, ('Stale configuration', key)
    assert manifest['top'] == 'DitDahA1Core' and config['enableJtag'] and int(config['resetVector']) == 0
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in manifest['sourceHashes'].items()), 'Stale RTL'
    binary = compile_tb(rtl, output, config['axiDataBits'], config['physicalAddressBits'], 'memory_tb',
                        Path('test/memory_tb.sv').resolve(), [(output / 'memory/DitDahA1Memory.sv').resolve()])
    names = ['step', 'step_multiply', 'step_fault', 'step_wfi', 'breakpoint', 'priority', 'store', 'atomic', 'load', 'divide', 'exception', 'illegal_dret', 'illegal_dpc']
    if config['enableC']:
        names.append('step_compressed')
    if config['enableUserMode']:
        names.append('step_user')
    if config['enableInterrupts']:
        names.extend(('wfi', 'step_interrupt'))
    if config['enableSupervisorMode']:
        names.append('step_supervisor')
    if config['floatingPointBits'] == 64:
        names.append('floating')
    reports = []
    for name in [] if args.quiet_only else args.selected or names:
        p, steps, trigger = program(name)
        image = output / (name + '.hex')
        image.write_text('@0\n' + '\n'.join(f'{p.memory.get(i, 0):02x}' for i in range(0x4000)) + '\n')
        for seed in (1, 17, 2026):
            log = output / f'{name}-{seed}.log'
            command = [binary, f'+IMAGE={image.resolve()}', '+BASE=0', f'+STOP={p.stop:x}',
                       f'+SEED={seed}', f'+DEBUG_TRIGGER={trigger}', f'+DEBUG_PRIORITY={int(name == "priority")}']
            if name == 'step_interrupt':
                command += ['+IRQ_MASK=2', '+IRQ_MODE=4', f'+IRQ_WAIT_LIMIT={(steps+1)*1000}']
            run(command, log)
            reports.append(dict(seed=seed, **check(name, log, steps, trigger)))
    negative = negative_controls(output, config) if args.mutations else []
    quiet = None
    if args.quiet_only or not args.selected:
        directory = output / 'ordinary'
        directory.mkdir(exist_ok=True)
        selected = ['arithmetic', 'integer_reserved', 'integer_breakpoint', 'muldiv_4', 'atomic_0_3']
        if config['enableC']:
            selected.append('compressed_integer')
        if config['floatingPointBits']:
            selected.append('floating_64')
        quiet = compare(binary, directory, config, 'memory', selected)
        assert {case['test'] for case in quiet['cases']} == set(selected), 'Missing ordinary case'
    assert test_hashes == {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}, 'Checker inputs changed'
    (output / ('quiet-summary.json' if args.quiet_only else 'summary.json')).write_text(json.dumps(dict(sourceHashes=manifest['sourceHashes'],
        testSourceHashes=test_hashes,
        configurations=config, runs=reports, negativeControls=negative, ordinary=quiet), indent=2) + '\n')
    print(f"Core checks passed: {len(reports)} debug and {len(quiet['cases']) if quiet else 0} ordinary schedules")


if __name__ == '__main__':
    main()
