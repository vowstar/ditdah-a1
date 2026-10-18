# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Compare generated RTL against instruction and bus-level expectations."""

import argparse
from collections import Counter
import hashlib
import json
import re
from pathlib import Path
import subprocess

from contracts import verify as verify_contracts, verify_storage
from model import Fault, Model, MASK
from programs import cases, multicore_cases


def run(command, log, cwd=None):
    with log.open('w') as stream:
        result = subprocess.run(list(map(str, command)), cwd=cwd, stdout=stream, stderr=subprocess.STDOUT, timeout=600)
    if result.returncode:
        raise RuntimeError(f'{command[0]} failed; see {log}\n' + log.read_text()[-10000:])


def configuration(width):
    base = 0 if width == 64 else 1 << 40
    regions = []
    for offset, size, read, write, execute, device in (
            (0, 0x4000, True, True, True, False),
            (0x4000, 0x1000, True, False, True, False),
            (0x5000, 0x1000, True, True, False, True),
            (0x6000, 0x1000, False, False, False, False),
            (0x7000, 0x1000, True, True, False, False),
            (0x8000, 0x1000, False, False, True, False)):
        regions.append(dict(base=str(base + offset), size=str(size), readable=read,
                            writable=write, executable=execute, device=device, atomic=offset == 0))
    return dict(resetVector=str(base), axiDataBits=width, physicalAddressBits=32 if width == 64 else 56,
                virtualAddressBits=0, iCacheBytes=0, dCacheBytes=0, l2CacheBytes=0, pmpEntries=0,
                memoryRegions=regions)


def compile_tb(rtl, directory, width, pa, top='core_tb', source=None, extra_files=()):
    source = source or Path('test/core_tb.sv').resolve()
    files = [(rtl / name).resolve() for name in (rtl / 'filelist.f').read_text().splitlines()]
    parameters = json.loads((rtl / 'ditdah_a1_config.json').read_text())['parameters']
    interrupts, harts = parameters['enableInterrupts'], parameters['hartCount']
    bindings, ports = [], []
    observers = [f'  wire [{harts - 1}:0] architectural_fetch_busy;\n  wire [63:0] architectural_fetch_pc[{harts}];']
    for hart in range(harts if top == 'core_tb' else 1):
        fetch = f'dut.core_{hart}.frontend.fetch' if top == 'core_tb' else 'dut.frontend.fetch'
        order = fetch.replace('.frontend.fetch', '.backend.dV.traceOrder')
        prefix = f'$write("HART {hart} "); ' if harts > 1 else ''
        observers.append(f'''  assign architectural_fetch_busy[{hart}] = !{fetch}.request_ready;
  assign architectural_fetch_pc[{hart}] = {fetch}.request_bits_pc;
  always @(posedge clock) if (!reset) begin
    if ({fetch}.request_valid && {fetch}.request_ready) begin
      {prefix}$display("ARCH_REQUEST %016h %02h", {fetch}.request_bits_pc, {fetch}.request_bits_tag);
    end
    if ({fetch}.cancel) begin {prefix}$display("ARCH_CANCEL %016h", {order}); end
    if ({fetch}.output_valid && {fetch}.output_ready) begin
      {prefix}$display("ARCH_FETCH %016h %01h %08h %02h", {fetch}.output_bits_pc,
        {fetch}.output_bits_fault, {fetch}.output_bits_instruction, {fetch}.output_bits_tag);
    end
  end''')
    (directory / 'fetch_observers.svh').write_text('\n'.join(observers) + '\n')
    if top == 'core_tb':
        names = re.findall(r'\bDitDahA1Core\s+(\w+)\s*\(', (rtl / 'DitDahA1.sv').read_text())
        assert names == [f'core_{h}' for h in range(harts)], names
        for hart, name in enumerate(names):
            core = f'dut.{name}'
            for field in ('traceValid', 'traceOrder', 'tracePc', 'traceInstruction', 'traceNextPc', 'traceRd',
                          'traceRdWrite', 'traceValue', 'traceTrap', 'traceCause', 'traceTval', 'pipelineOccupancy', 'pipelineStall'):
                bindings.append(f'assign traces[{hart}].{field} = {core}.backend.dV.{field};')
            bindings.append(f'assign multiply_busy[{hart}] = {core}.backend.multiply.busy;')
            for kind, port in enumerate(('instruction', 'data')):
                index = 2 * hart + kind
                for channel in ('request', 'response'):
                    for field in ('valid', 'ready'):
                        bindings.append(f'assign {channel}_{field}[{index}] = {core}.{port}_{channel}_{field};')
                    for field in (('address', 'data', 'size', 'mask', 'tag', 'write', 'fetch', 'atomic') if channel == 'request' else ('data', 'fault', 'tag')):
                        bindings.append(f'assign {channel}s[{index}].{field} = {core}.{port}_{channel}_bits_{field};')
            if interrupts:
                ports += [f'.interrupts_{hart}_{name}(irq_by_hart[{hart}][{index}]),'
                          for index, name in enumerate(('software', 'timer', 'external'))]
    (directory / 'core_bindings.svh').write_text('\n'.join(bindings) + '\n')
    (directory / 'core_ports.svh').write_text('\n'.join(ports) + '\n')
    if interrupts and top == 'memory_tb':
        extra_files = [*extra_files, Path('test/core_tb.sv').resolve()]
    run(['verilator', '--binary', '--timing', '--assert', '-j', '2', '--top-module', top,
         '-Wno-TIMESCALEMOD', '-Wno-WIDTHTRUNC', '-Wno-WIDTHEXPAND',
         f'-DAXI_BITS={width}', f'-DPA_BITS={pa}', f'-DHARTS={harts}', '-I' + str(directory.resolve()), *(['-DENABLE_INTERRUPTS'] if interrupts else []), '-I' + str(rtl.resolve()),
         *(['-DICACHE'] if parameters['iCacheBytes'] else []),
         '--Mdir', str((directory / 'obj').resolve()), *files, *extra_files, source], directory / 'compile.log')
    return (directory / 'obj' / ('V' + top)).resolve()


def check_fetches(lines, config, faults, local_faults=()):
    def allowed(address):
        return address % 4 == 0 and address + 4 <= 1 << config['physicalAddressBits'] and any(
            int(region['base']) <= address and address + 4 <= int(region['base']) + int(region['size'])
            and region['executable'] for region in config['memoryRegions'])

    architectural = any(line.startswith('ARCH_REQUEST ') for line in lines)
    pending, requests, demand = None, {}, None
    arch_accepted, arch_completed, arch_wraps = 0, 0, 0
    fetched, failed = Counter(), Counter()
    physical_fetched, physical_failed, bus_failed = Counter(), Counter(), Counter()
    cancel_order, retired_order = None, -1

    def discard_outputs():
        fetched.clear()
        failed.clear()
        bus_failed.clear()

    reachable = {int(config['resetVector'])}
    accepted, completed = 0, 0
    for line in lines:
        fields = line.split()
        if fields[:1] == ['ARCH_REQUEST']:
            address, tag = (int(value, 16) for value in fields[1:])
            assert not requests and pending is None and address in reachable, 'Unexpected architectural fetch identity or control flow'
            requests[tag] = address
            demand = address
            arch_wraps += int(tag == 0 and arch_accepted != 0)
            arch_accepted += 1
            reachable.add(address + 4)
        elif fields[:1] == ['ARCH_CANCEL']:
            requests.clear()
            physical_fetched.clear()
            physical_failed.clear()
            if pending is not None:
                pending[1] = True
            cancel_order = int(fields[1], 16) if len(fields) == 2 else -1
            if cancel_order <= retired_order:
                discard_outputs()
                cancel_order = None
        elif fields[:1] == ['ARCH_FETCH']:
            address, fault, instruction, tag = (int(value, 16) for value in fields[1:])
            assert requests.pop(tag, None) == address, 'Unrequested, repeated or cancelled architectural fetch'
            if not config['iCacheBytes']:
                if not fault:
                    assert physical_fetched[address, instruction], 'Architectural fetch without matching physical response'
                    physical_fetched[address, instruction] -= 1
                elif physical_failed[address]:
                    physical_failed[address] -= 1
                    bus_failed[address] += 1
            arch_completed += 1
            (failed if fault else fetched)[address if fault else (address, instruction)] += 1
        elif fields[:2] == ['BUS', 'fetch']:
            address, size, data = int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            assert pending is None, 'Overlapping instruction transactions'
            assert size == 4 and data == 0 and allowed(address), f'Forbidden fetch: {line}'
            expected = demand is not None and (address & ~63 == demand & ~63 if config['iCacheBytes'] else address == demand)
            assert (expected if architectural else address in reachable), f'Fetch outside current instruction demand: {line}'
            reachable.add(address + 4)
            pending = [address, architectural and not requests]
            accepted += 1
        elif fields[:1] == ['FETCH']:
            address, response, instruction = (int(value, 16) for value in fields[1:])
            assert pending is not None and pending[0] == address, f'Unrequested fetch response: {line}'
            assert response == (2 if address == faults.get('fetch') else 0), f'Fetch response: {line}'
            if not architectural:
                (failed if response else fetched)[address if response else (address, instruction)] += 1
            elif not pending[1]:
                (physical_failed if response else physical_fetched)[address if response else (address, instruction)] += 1
            pending = None
            completed += 1
        elif fields[:1] == ['TRACE']:
            trace = tuple(int(value, 16) for value in fields[1:])
            pc, instruction, trap, cause = trace[1], trace[2], trace[7], trace[8]
            reachable.add(trace[3])
            if trap and cause >> 63:
                pass
            elif trap and cause == 1:
                if architectural or (trace[0] not in local_faults and allowed(pc)):
                    assert failed[pc], f'Fetch fault without failed response: {line}'
                    failed[pc] -= 1
                if architectural and not config['iCacheBytes'] and trace[0] not in local_faults and allowed(pc):
                    assert bus_failed[pc], 'Architectural fetch fault without physical failure or local denial'
                    bus_failed[pc] -= 1
            else:
                assert fetched[pc, instruction], f'Retirement without completed instruction fetch: {line}'
                fetched[pc, instruction] -= 1
            retired_order = trace[0]
            if cancel_order == retired_order:
                discard_outputs()
                cancel_order = None
    return dict(accepted=accepted, completed=completed, architecturalAccepted=arch_accepted,
                architecturalCompleted=arch_completed, architecturalTagWraps=arch_wraps,
                discarded=sum(fetched.values()) + sum(failed.values()))


def check_fetch_oracle():
    config, word = configuration(64), 0x0400006f
    request = 'ARCH_REQUEST 0 0'
    physical = ['BUS fetch 0 4 0', f'FETCH 0 0 {word:x}']
    output = f'ARCH_FETCH 0 0 {word:x} 0'
    trace = f'TRACE 0 0 {word:x} 40 0 0 0 0 0 0'
    valid = [request, *physical, output, trace]
    check_fetches(valid, config, {})
    local = [request, 'ARCH_FETCH 0 1 0 0', 'TRACE 0 0 0 0 0 0 0 1 1 0']
    check_fetches(local, config, {}, local_faults=(0,))
    fault = [request, 'BUS fetch 0 4 0', 'FETCH 0 2 0', 'ARCH_FETCH 0 1 0 0']
    fault_trace = 'TRACE 0 0 0 0 0 0 0 1 1 0'
    for ending in (['ARCH_CANCEL 0', fault_trace], [fault_trace, 'ARCH_CANCEL 0']):
        check_fetches([*fault, *ending], config, {'fetch': 0})
    rejected = {
        'missingPhysicalResponse': [request, output, trace],
        'unrelatedLine': [*valid, 'ARCH_REQUEST 40 1', *physical],
        'cancelledOutput': [request, *physical, 'ARCH_CANCEL', output],
        'missingFaultResponse': local,
        'cancelledFaultCredit': [*fault, 'ARCH_CANCEL 0', 'TRACE 0 0 0 0 0 0 0 1 800000000000000b 0',
                                 'ARCH_REQUEST 0 1', 'ARCH_FETCH 0 1 0 1', 'TRACE 1 0 0 0 0 0 0 1 1 0'],
    }
    for name, lines in rejected.items():
        profiles = (config, dict(config, iCacheBytes=8192)) if name in ('unrelatedLine', 'cancelledOutput') else (config,)
        for profile in profiles:
            try:
                check_fetches(lines, profile, {'fetch': 0} if name == 'cancelledFaultCredit' else {})
            except AssertionError:
                continue
            raise AssertionError(f'Fetch oracle accepted {name}')
    return list(rejected)


def compare(binary, directory, config, transport='axi', selected=()):
    base = int(config['resetVector'])
    coverage = [0] * 6
    coverage_names = (('awBeforeW', 'wBeforeAw', 'awWithW', 'arStall', 'awStall', 'wStall') if transport == 'axi'
                      else ('overlap', 'instructionStall', 'dataStall', 'responseDelay', 'permissionReject', 'architecturalTagWrap' if config['iCacheBytes'] else 'tagWrap'))
    count = 0
    reports = []
    pipeline_max, dependency_stalls = 0, 0
    for name, program in cases(base, config['pmpEntries'] != 0, config['enableInterrupts']):
        if selected and name not in selected:
            continue
        image = directory / (name + '.hex')
        image.write_text('\n'.join(f'{program.memory.get(base + i, 0):02x}' for i in range(65536)) + '\n')
        model = Model(config, program.memory, program.faults)
        expected = []
        for _ in range(2000):
            if hasattr(program, 'interrupts'):
                break
            record = model.step()
            expected.append(record)
            if not record[7] and record[1] == program.stop:
                break
        else:
            raise AssertionError(f'{name}: reference program did not finish')
        for seed in (1, 17, 2026):
            log = directory / f'{name}-{seed}.log'
            command = [binary, f'+IMAGE={image.resolve()}', f'+BASE={base:x}',
                       f'+STOP={program.stop:x}', f'+SEED={seed}']
            command.extend(f'+FAULT_{kind.upper()}={address:x}' for kind, address in program.faults.items())
            command += [f'+{key.upper()}={getattr(program, key, 0)}' for key in ('exclusive_failures', 'interference')]
            if hasattr(program, 'interrupts'):
                command.extend(f'+IRQ_{key.upper()}={value:x}' if key == 'target' else f'+IRQ_{key.upper()}={value}'
                               for key, value in program.interrupts.items())
            run(command, log)
            lines = log.read_text().splitlines()
            assert 'PASS' in lines, f'{name}: simulation did not complete'
            if hasattr(program, 'interrupts'):
                model = Model(config, program.memory, program.faults)
                expected, causes, deferred = [], [], 0
                for line in lines:
                    fields = line.split()
                    if fields[:1] == ['IRQ']:
                        model.set_interrupts(int(fields[1], 16))
                    elif fields[:1] == ['TRACE']:
                        observed = tuple(int(v, 16) for v in fields[1:])
                        pending = model.interrupt_cause()
                        record = model.interrupt() if observed[8] >> 63 else model.step()
                        if pending and not record[8] >> 63 and not record[7]:
                            deferred += 1
                            assert deferred <= 1 and record[2] & 127 in (3, 0x23, 0x2f), f'{name}: interrupt deferred beyond its memory owner'
                        else:
                            deferred = 0
                        if record[8] >> 63:
                            causes.append(record[8] & 63)
                        expected.append(record)
                wanted_causes = [bit for index, bit in ((2, 11), (0, 3), (1, 7)) if program.interrupts['mask'] & (1 << index)]
                assert causes == wanted_causes, f'{name}: interrupt delivery or priority {causes} != {wanted_causes}'
                start = next((i for i, line in enumerate(lines) if line.startswith('IRQ_START ')), None)
                assert start is not None, f'{name}: stimulus never activated'
                if program.interrupts['mode'] == 7:
                    assert any(line.startswith('TRACE ') and int(line.split()[2], 16) == program.interrupts['target']
                               and int(line.split()[8], 16) == 0 for line in lines[:start]), f'{name}: target did not retire before interrupt assertion'
            actual = [tuple(int(v, 16) for v in line.split()[1:]) for line in lines if line.startswith('TRACE ')]
            bus = [(v[1], int(v[2], 16), int(v[3]), int(v[4], 16))
                   for line in lines if line.startswith('BUS ') for v in [line.split()]]
            assert len(actual) == len(expected), f'{name}: trace length {len(actual)} != {len(expected)}'
            for index, (observed, wanted) in enumerate(zip(actual, expected)):
                assert observed == wanted, f'{name} trace {index}:\nactual {observed}\nexpected {wanted}'
            data_bus = [event for event in bus if event[0] != 'fetch']
            expected_bus = [event for event in model.bus if event[0] != 'fetch']
            if transport == 'axi' and ('atomic' in name or name in ('fence_ordering', 'synchronization')):
                check_multicore(lines, config, program, name)
            else:
                assert data_bus == expected_bus, f'{name}: unexpected data accesses\nactual {data_bus}\nexpected {expected_bus}'
            if transport == 'memory':
                requests = [(v[1], int(v[2], 16), int(v[3]), int(v[4], 16)) for line in lines
                            if line.startswith('REQUEST ') for v in [line.split()] if v[1] != 'fetch']
                assert requests == [r for r in model.requests if r[0] != 'fetch'], f'{name}: unexpected Core requests'
            fetches = check_fetches(lines, config, program.faults, model.local_fetch_faults)
            if name == 'pipeline_redirect':
                fault = program.faults['fetch']
                assert any(line.startswith(f'FETCH {fault:016x} 2 ') for line in lines), 'Wrong-path fetch fault was not exercised'
            if name == 'pipeline_reuse':
                assert fetches['architecturalAccepted'] > 256, 'Instruction identity wraparound was not exercised'
            for line in lines:
                if line.startswith('COVER '):
                    observed_coverage = list(map(int, line.split()[1:]))
                    if transport == 'memory' and config['iCacheBytes']:
                        observed_coverage[5] = fetches['architecturalTagWraps']
                    coverage = [a + b for a, b in zip(coverage, observed_coverage)]
                elif line.startswith('PIPELINE '):
                    occupancy, stalls = map(int, line.split()[1:])
                    pipeline_max = max(pipeline_max, occupancy)
                    dependency_stalls += stalls
            count += len(actual)
            elapsed = next(int(line.split()[1]) for line in lines if line.startswith('CYCLES '))
            reports.append(dict(test=name, seed=seed, events=len(actual), cycles=elapsed, busTransactions=len(bus), fetches=fetches))
        print(f'  {name}: {len(expected)} events, three bus schedules', flush=True)
    assert reports, 'No selected scalar program'
    if not selected:
        assert all(coverage), f'{transport} coverage missing: {dict(zip(coverage_names, coverage))}'
        assert pipeline_max >= 2 and dependency_stalls, f'Pipeline coverage missing: {pipeline_max}, {dependency_stalls}'
    return dict(events=count, cases=reports, pipelineCoverage=dict(maxOccupancy=pipeline_max, dependencyStalls=dependency_stalls),
                **{('busCoverage' if transport == 'axi' else 'portCoverage'): dict(zip(coverage_names, coverage))})


def check_multicore(lines, config, program, name):
    covers = [list(map(int, line.split()[1:])) for line in lines if line.startswith('COVER ')]
    harts, base = config['hartCount'], int(config['resetVector'])
    assert len(covers) == 1 and len(covers[0]) == 6 and (harts == 1 or all(covers[0])), 'Missing AXI scheduling coverage'
    memory, active = dict(program.memory), None
    failures = getattr(program, 'exclusive_failures', 0)
    models = [Model(config, program.memory, program.faults, hart_id=h) for h in range(harts)]
    for model in models:
        model.memory = memory
    pending, finished, per_hart = [None] * harts, set(), [[] for _ in range(harts)]
    collisions, tags, sources, events, effects = set(), {}, set(), 0, Counter()
    interrupts, overtaken = Counter(), 0
    deferred = [0] * harts
    concurrent = Counter()

    def no_service(*args):
        raise AssertionError('Architectural data access without bus service')

    for model in models:
        model.external_access = no_service

    def service(hart, event, atomic_fault=False):
        assert pending[hart] is None, 'Second memory operation before retirement'
        accesses = []

        def access(address, size, kind, data):
            wanted = kind, address, size, data if kind in ('write', 'atomic') else 0
            assert event == wanted, f'{name}: data service {event} != independent instruction {wanted}'
            accesses.append(wanted)
            if atomic_fault or address == program.faults.get(kind):
                raise Fault(5 if kind == 'read' else 7, address)
            old = sum(memory.get(address + byte, 0) << (byte * 8) for byte in range(size))
            if kind in ('write', 'atomic'):
                value = (old + data) & MASK if kind == 'atomic' else data
                for byte in range(size):
                    memory[address + byte] = (value >> (byte * 8)) & 255
                effects[hart, address] += 1
            return 0 if kind == 'write' else old

        models[hart].external_access = access
        pending[hart] = models[hart].step()
        models[hart].external_access = no_service
        assert len(accesses) == 1, 'Bus service did not match an architectural access'

    for line in lines:
        fields = line.split()
        if fields[:1] == ['HART']:
            hart, fields = int(fields[1]), fields[2:]
        elif harts == 1 and fields and fields[0] in ('REQUEST', 'BUS', 'READ', 'WRITE', 'INTERFERE', 'RESPONSE', 'FETCH', 'IRQ', 'TRACE', 'ARCH_REQUEST', 'ARCH_FETCH', 'ARCH_CANCEL'):
            hart = 0
        else:
            continue
        assert 0 <= hart < harts
        per_hart[hart].append(' '.join(fields))
        kind = fields[0]
        if kind in ('ARCH_REQUEST', 'ARCH_FETCH', 'ARCH_CANCEL'):
            continue
        assert kind in ('REQUEST', 'BUS', 'READ', 'WRITE', 'INTERFERE', 'RESPONSE', 'FETCH', 'IRQ', 'TRACE'), 'Unknown hart event'
        if kind == 'REQUEST':
            assert active is None, 'Overlapping source ownership'
            event = fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            tag = int(fields[5], 16)
            active = dict(hart=hart, event=event, tag=tag, bus=False, response=None)
            source = 2 * hart + int(event[0] != 'fetch')
            sources.add(source)
            if tag in tags and tags[tag] != hart:
                collisions.add(tag)
            tags[tag] = hart
        elif kind == 'BUS':
            event = fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            if event[0] in ('exclusive_read', 'exclusive_write'):
                assert active and active['hart'] == hart and active['event'][0] == 'atomic'
                _, address, size, addend = active['event']
                assert event[1:3] == (address, size) and size == 8
                if event[0] == 'exclusive_read':
                    assert active.get('phase') in (None, 'retry') and event[3] == 0
                    active.update(bus=True, phase='read')
                else:
                    assert active['phase'] == 'write' and event[3] == (active['old'] + addend) & MASK
                    active['phase'] = 'response'
                continue
            assert active and active['hart'] == hart and active['event'] == event and not active['bus']
            active['bus'] = True
            if event[0] == 'write':
                service(hart, event)
                active['response'] = (0, int(event[1] == program.faults.get('write')))
        elif kind == 'READ':
            assert active and active['hart'] == hart and active['bus'] and active['response'] is None
            access, address, size, _ = active['event']
            expected = sum(memory.get(address + byte, 0) << (byte * 8) for byte in range(size))
            if access == 'atomic':
                assert active['phase'] == 'read'
                response = 2 if address == program.faults.get('read') else 0 if address == program.faults.get('exclusive') else 1
                assert tuple(int(v, 16) for v in fields[1:]) == (address, response, expected)
                active.update(old=expected, phase='write' if response == 1 else 'complete')
                if response != 1:
                    service(hart, active['event'], atomic_fault=True)
                    active['response'] = (expected, 1)
                continue
            fault = address == program.faults.get(access)
            assert tuple(int(v, 16) for v in fields[1:]) == (address, 2 if fault else 0, expected)
            if access == 'read':
                overtaken += sum(record is not None for h, record in enumerate(pending) if h != hart)
                service(hart, active['event'])
            active['response'] = (expected, int(fault))
        elif kind == 'INTERFERE':
            assert active and active['hart'] == hart and active['phase'] == 'response' and failures > 0
            address, value = (int(v, 16) for v in fields[1:])
            assert address == active['event'][1] and value == (active['old'] + program.interference) & MASK
            for byte in range(8):
                memory[address + byte] = (value >> (8 * byte)) & 255
            failures -= 1
            active['phase'] = 'interference'
        elif kind == 'WRITE':
            assert active and active['hart'] == hart and active['phase'] in ('response', 'interference')
            address, response = (int(v, 16) for v in fields[1:])
            assert address == active['event'][1]
            fault = address == program.faults.get('write')
            assert response == (2 if fault else 0 if active['phase'] == 'interference' else 1)
            active['phase'] = 'retry' if response == 0 else 'complete'
            if response:
                service(hart, active['event'], atomic_fault=fault)
                active['response'] = (active['old'], int(fault))
        elif kind == 'RESPONSE':
            assert active and active['hart'] == hart, 'Response to the wrong hart'
            channel, data, fault, tag = (int(v, 16) for v in fields[1:])
            assert channel == int(active['event'][0] != 'fetch') and tag == active['tag']
            if not active['bus']:
                assert fault, 'Locally rejected request did not fault'
                if channel:
                    assert pending[hart] is None
                    first = len(models[hart].requests)
                    pending[hart] = models[hart].step()
                    requests = [event for event in models[hart].requests[first:] if event[0] != 'fetch']
                    assert requests == [active['event']], 'Unexpected locally rejected request'
                    assert pending[hart][7]
            else:
                expected_data, expected_fault = active['response']
                assert fault == expected_fault and (fault or data == expected_data), 'Response data or fault mismatch'
            active = None
        elif kind == 'IRQ':
            models[hart].set_interrupts(int(fields[1], 16))
        elif kind == 'TRACE':
            observed = tuple(int(v, 16) for v in fields[1:])
            eligible, owned = models[hart].interrupt_cause(), pending[hart] is not None
            if pending[hart] is not None:
                assert active is None or active['hart'] != hart or active['event'][0] == 'fetch', 'Memory operation retired before its response'
                wanted, pending[hart] = pending[hart], None
            elif observed[8] >> 63:
                wanted = models[hart].interrupt()
                interrupts[hart] += 1
            else:
                wanted = models[hart].step()
            if eligible and not wanted[7]:
                deferred[hart] += 1
                assert owned and deferred[hart] == 1, 'Interrupt deferred beyond its memory owner'
            else:
                deferred[hart] = 0
            assert observed == wanted, f'{name} hart {hart}:\nactual {observed}\nexpected {wanted}'
            events += 1
            if active is not None and active['hart'] != hart:
                concurrent['trapDuringPeerService'] += int(bool(wanted[7]))
                concurrent['redirectDuringPeerService'] += int(wanted[3] != wanted[1] + 4)
            if not wanted[7] and wanted[1] == program.stop:
                finished.add(hart)
    assert finished == set(range(harts)) and all(record is None for record in pending)
    assert active is None or active['event'][0] == 'fetch', 'Unretired data access at completion'
    assert failures == 0, 'Exclusive failure stimulus was not consumed'
    if harts > 1:
        assert sources == set(range(2 * harts)) and collisions, 'Missing source or cross-hart tag collision'
    assert interrupts == (Counter({getattr(program, 'interrupts', {}).get('hart', 0): 1}) if hasattr(program, 'interrupts') else Counter()), 'Interrupt isolation'
    if harts > 1 and 'atomic' in name:
        word = lambda address: sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8))
        assert word(base + 0x1800) == 4 * harts + 14, 'Lost or duplicate atomic update'
        old = [word(base + 0x2000 + hart * 64 + i * 8) for hart in range(harts) for i in range(4)]
        assert sorted(old) == list(range(14, 14 + 4 * harts)), 'Atomic old-value uniqueness'
    for hart, model in enumerate(models):
        if hasattr(program, 'synchronization'):
            word = lambda address: sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8))
            tasks = program.synchronization['rounds'] * harts
            assert word(base + 0x1810) == tasks, 'Work allocation count'
            assert [word(base + 0x2000 + 8 * ticket) for ticket in range(tasks)] == list(range(1, tasks + 1)), 'Lost or duplicate work'
            assert all(sum(effects[h, base + 0x2000 + 8 * ticket] for h in range(harts)) == 1 for ticket in range(tasks)), 'Repeated task execution'
            assert effects[hart, base + 0x1810] == program.synchronization['rounds'], 'Hart did not execute every work round'
            assert all(word(base + offset) == harts for offset in (0x1800, 0x1818, 0x1820, 0x1828, 0x1830)), 'Incomplete repeated barrier'
            assert word(base + 0x2400 + 64 * hart) == 3 and word(base + 0x2408 + 64 * hart) == 9, 'Instruction publication did not replace warmed code'
            assert model.registers[19] == tasks * (tasks + 1) // 2, 'Distributed work checksum'
        elif harts > 1 and 'atomic' in name:
            assert model.registers[18] == harts * (harts + 1) // 2, 'Release/acquire publication'
        elif harts > 1:
            assert model.registers[8] == (hart + 1) % harts + 1, 'Mailbox exchange did not complete'
            assert model.registers[12] == 1 and effects[hart, base + 0x5100] == 1, 'Private data or device effect'
            assert model.registers[17] == hart and (name == 'interrupt' or model.registers[19] == hart), 'Hart identity or read-only CSR'
        if name == 'protection':
            assert effects[hart, base + 0x1800] == int(hart != 0), 'PMP isolation'
        check_fetches(per_hart[hart], config, program.faults, model.local_fetch_faults)
    return dict(events=events, activeHarts=len(finished), sources=sorted(sources),
                collidingTags=len(collisions), readsBeforePeerRetirement=overtaken, concurrency=dict(concurrent),
                busCoverage=dict(zip(('awBeforeW', 'wBeforeAw', 'awWithW', 'arStall', 'awStall', 'wStall'), covers[0])))


def compare_multicore(binary, directory, config, selected=()):
    harts, base = config['hartCount'], int(config['resetVector'])
    reports = []
    for name, program in multicore_cases(base, harts, bool(config['pmpEntries']), config['enableInterrupts']):
        if selected and name not in selected:
            continue
        image = directory / (name + '.hex')
        image.write_text('\n'.join(f'{program.memory.get(base + i, 0):02x}' for i in range(65536)) + '\n')
        first = len(reports)
        for seed in (1, 17, 2026):
            log = directory / f'{name}-{seed}.log'
            command = [binary, f'+IMAGE={image.resolve()}', f'+BASE={base:x}', f'+STOP={program.stop:x}', f'+SEED={seed}']
            command += [f'+FAULT_{kind.upper()}={address:x}' for kind, address in program.faults.items()]
            command += [f'+{key.upper()}={getattr(program, key, 0)}' for key in ('exclusive_failures', 'interference')]
            if hasattr(program, 'interrupts'):
                command += [f'+IRQ_{key.upper()}={value:x}' if key == 'target' else f'+IRQ_{key.upper()}={value}'
                            for key, value in program.interrupts.items()]
            run(command, log)
            lines = log.read_text().splitlines()
            assert 'PASS' in lines, f'{name}: incomplete multicore run'
            reports.append(dict(test=name, seed=seed, **check_multicore(lines, config, program, name)))
        if harts > 1 and 'atomic' not in name and not hasattr(program, 'synchronization'):
            concurrent = Counter()
            for report in reports[first:]:
                concurrent.update(report['concurrency'])
            assert concurrent['trapDuringPeerService'] and concurrent['redirectDuringPeerService'], f'{name}: missing concurrent trap or redirect {dict(concurrent)}'
        print(f'  {harts} harts, {name}: three shared-memory schedules', flush=True)
    assert reports, 'No selected multicore program'
    return dict(events=sum(report['events'] for report in reports), cases=reports)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--width', type=int, choices=(64, 128, 256, 512), action='append')
    parser.add_argument('--use-generated', action='store_true')
    parser.add_argument('--multicore-only', action='store_true')
    parser.add_argument('--harts', type=int, choices=(2, 3, 16), action='append')
    parser.add_argument('--output', type=Path, default=Path('result/verify'))
    parser.add_argument('--interrupts', action='store_true', help='Run only enabled interrupt profiles')
    parser.add_argument('--pmp-entries', type=int, choices=(0, 16))
    parser.add_argument('--icache-bytes', type=int, choices=(0, 8192, 16384, 32768, 65536), default=0)
    parser.add_argument('--case', dest='selected', action='append', default=[])
    parser.add_argument('--traffic-baseline', type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    summary_path = args.output / 'summary.json'
    summary_path.unlink(missing_ok=True)
    test_hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for name in
                   ('verify.py', 'contracts.py', 'model.py', 'programs.py', 'core_tb.sv', 'memory_tb.sv')
                   for p in (Path('test') / name,)}
    summary = {'scope': 'implemented scalar subset; simulation and assertions', 'selectedCases': args.selected,
               'fetchOracleGuards': check_fetch_oracle(), 'configurations': []}
    frozen_sources = None

    def freeze_sources(manifest):
        nonlocal frozen_sources
        assert manifest.get('sourceHashes'), 'Generated RTL has no source provenance'
        if frozen_sources is None:
            frozen_sources = manifest['sourceHashes']
        assert manifest['sourceHashes'] == frozen_sources, 'Mixed generated source snapshots'

    core_profiles = {}
    profiles = [(width, entries, False) for entries in ((args.pmp_entries,) if args.pmp_entries is not None else (0, 16))
                for width in args.width or (64, 128, 256, 512) if entries == 0 or width in (64, 512)]
    if args.interrupts or args.multicore_only:
        profiles = []
    profiles += [(width, entries, True) for width, entries in (() if args.multicore_only else ((64, 0), (512, 16)))
                 if (not args.width or width in args.width) and (args.pmp_entries is None or entries == args.pmp_entries)]
    for width, entries, interrupts in profiles:
        directory = args.output / f'{"irq-" if interrupts else ""}{"pmp16-" if entries else ""}axi{width}'
        directory.mkdir(parents=True, exist_ok=True)
        config = configuration(width)
        config.update(pmpEntries=entries, enableInterrupts=interrupts, iCacheBytes=args.icache_bytes)
        config_path = directory / 'input.json'
        config_path.write_text(json.dumps(config, indent=2) + '\n')
        rtl = directory / 'rtl'
        if not args.use_generated:
            print(f'Generating AXI{width} RTL', flush=True)
            run(['build-ditdah-a1', '--trace', '--config', config_path, '--output', rtl], directory / 'build.log')
        manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
        freeze_sources(manifest)
        assert manifest['top'] == 'DitDahA1' and manifest['validationScope'] == 'system'
        assert manifest.get('sourceHashes'), 'Generated RTL has no source provenance'
        for name, digest in manifest['sourceHashes'].items():
            assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, f'Stale RTL source: {name}'
        for key, value in config.items():
            assert manifest['parameters'][key] == value, f'Stale RTL configuration: {key}'
        interface_contracts = verify_contracts(rtl, directory / 'contracts')
        storage = verify_storage(rtl, directory / 'storage')
        binary = compile_tb(rtl, directory, width, config['physicalAddressBits'])
        print(f'Checking AXI{width}', flush=True)
        report = compare(binary, directory, manifest['parameters'], selected=args.selected)
        report['interfaceContracts'] = interface_contracts
        report['instructionStorage'] = storage
        report.update(axiDataBits=width, physicalAddressBits=config['physicalAddressBits'], pmpEntries=entries, enableInterrupts=interrupts, iCacheBytes=args.icache_bytes)
        summary['configurations'].append(report)
        core = directory / 'core'
        core_config = dict(config, axiDataBits=256)
        core_key = json.dumps(core_config, sort_keys=True)
        if core_key in core_profiles:
            report['coreReuse'] = core_profiles[core_key]
            continue
        core.mkdir(exist_ok=True)
        core_input = core / 'input.json'
        core_input.write_text(json.dumps(core_config, indent=2) + '\n')
        if not args.use_generated:
            run(['build-ditdah-a1', '--top', 'DitDahA1Core', '--trace', '--config', core_input, '--output', core / 'rtl'], core / 'build.log')
        core_manifest = json.loads((core / 'rtl/ditdah_a1_config.json').read_text())
        assert core_manifest['top'] == 'DitDahA1Core' and core_manifest['validationScope'] == 'core'
        assert all(core_manifest['parameters'][k] == v for k, v in core_config.items()), 'Stale Core configuration'
        assert core_manifest['sourceHashes'] == manifest['sourceHashes'], 'Stale Core sources'
        assert not (core / 'rtl/DitDahA1Axi.sv').exists(), 'AXI dependency in standalone Core'
        binary = compile_tb(core / 'rtl', core, width, config['physicalAddressBits'], 'memory_tb',
                            Path('test/memory_tb.sv').resolve(), [(rtl / 'DitDahA1Memory.sv').resolve()])
        report['core'] = compare(binary, core, core_manifest['parameters'], 'memory', args.selected)
        core_profiles[core_key] = str(core)
    if args.multicore_only:
        for harts, width, entries, interrupts in ((2, 64, 0, False), (2, 512, 16, True),
                                                  (3, 64, 16, True), (16, 512, 16, True)):
            if (args.harts and harts not in args.harts) or (args.width and width not in args.width):
                continue
            if args.pmp_entries is not None and entries != args.pmp_entries:
                continue
            directory = args.output / f'harts{harts}-axi{width}'
            directory.mkdir(parents=True, exist_ok=True)
            config = dict(configuration(width), hartCount=harts, pmpEntries=entries, enableInterrupts=interrupts, iCacheBytes=args.icache_bytes)
            config_path, rtl = directory / 'input.json', directory / 'rtl'
            config_path.write_text(json.dumps(config, indent=2) + '\n')
            if not args.use_generated:
                run(['build-ditdah-a1', '--trace', '--config', config_path, '--output', rtl], directory / 'build.log')
            manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
            freeze_sources(manifest)
            assert manifest['implementation']['hartCount'] == harts
            assert all(manifest['parameters'][key] == value for key, value in config.items())
            assert all(hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest for name, digest in manifest['sourceHashes'].items())
            binary = compile_tb(rtl, directory, width, config['physicalAddressBits'])
            report = compare_multicore(binary, directory, manifest['parameters'], args.selected)
            report['interfaceContracts'] = verify_contracts(
                rtl, directory / 'contracts', modules=('DitDahA1MemoryArbiter', 'DitDahA1MemoryFabric'))
            report['instructionStorage'] = verify_storage(rtl, directory / 'storage')
            report.update(hartCount=harts, axiDataBits=width, pmpEntries=entries, enableInterrupts=interrupts, iCacheBytes=args.icache_bytes)
            if not args.icache_bytes:
                for count in ((15, 16) if harts == 16 else (harts,)):
                    Path(f'result/harts{count}-input.json').write_text(json.dumps(dict(config, hartCount=count), indent=2) + '\n')
            summary['configurations'].append(report)
        assert summary['configurations'], 'No selected multicore profile'
    else:
        frontend_config = dict(configuration(128), issueWidth=2, axiDataBits=512, iCacheBytes=8192, enableInterrupts=True)
        Path('result/frontend-input.json').write_text(json.dumps(frontend_config, indent=2) + '\n')
        fabric_config = dict(frontend_config, resetVector='2', hartCount=16, virtualAddressBits=48, pmpEntries=16)
        Path('result/fabric-input.json').write_text(json.dumps(fabric_config, indent=2) + '\n')
        backend_config = dict(fabric_config, issueWidth=1, pmpEntries=0, enableInterrupts=False, iCacheBytes=0)
        Path('result/backend-input.json').write_text(json.dumps(backend_config, indent=2) + '\n')
    assert frozen_sources
    for name, digest in frozen_sources.items():
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, f'Source changed during verification: {name}'
    summary['sourceHashes'] = dict(frozen_sources)
    for name, digest in test_hashes.items():
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, f'Test changed during verification: {name}'
    summary['sourceHashes'].update(test_hashes)
    if args.traffic_baseline:
        baseline = json.loads(args.traffic_baseline.read_text())
        assert args.icache_bytes and baseline['sourceHashes'] == summary['sourceHashes'], 'Traffic baseline uses different sources'
        comparison = []
        keys = ('axiDataBits', 'physicalAddressBits', 'pmpEntries', 'enableInterrupts')
        for profile in summary['configurations']:
            previous = [entry for entry in baseline['configurations'] if not entry['iCacheBytes']
                        and all(entry[key] == profile[key] for key in keys)]
            assert len(previous) == 1, 'Missing matching uncached traffic profile'
            for observed in profile['cases']:
                if observed['test'] != 'pipeline_reuse':
                    continue
                wanted = next(entry for entry in previous[0]['cases'] if entry['test'] == observed['test'] and entry['seed'] == observed['seed'])
                old, new = wanted['fetches']['accepted'], observed['fetches']['accepted']
                assert new < old, 'Repeated instruction hits did not reduce external fetches'
                comparison.append(dict(**{key: profile[key] for key in keys}, seed=observed['seed'],
                                       uncachedFetches=old, cachedFetches=new,
                                       uncachedCycles=wanted['cycles'], cachedCycles=observed['cycles']))
        assert comparison, 'No repeated workload for traffic comparison'
        summary['instructionCacheComparison'] = comparison
    summary_path.write_text(json.dumps(summary, indent=2) + '\n')
    print('Scalar RTL verification passed', flush=True)


if __name__ == '__main__':
    main()
