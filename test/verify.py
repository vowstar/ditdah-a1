# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Compare generated RTL against instruction and bus-level expectations."""

import argparse
from collections import Counter, deque
from concurrent.futures import ProcessPoolExecutor
import hashlib
import importlib.util
from itertools import chain
import json
import os
import re
from pathlib import Path
import subprocess
from types import SimpleNamespace

from contracts import verify as verify_contracts, verify_storage
from model import ExclusiveMonitor, Fault, LocalInterrupts, Model, MASK, atomic_value, integer_value, pmp_allowed, sv39_walk
from programs import cases, multicore_cases, platform_program


def run(command, log, cwd=None, timeout=600):
    with log.open('w') as stream:
        result = subprocess.run(list(map(str, command)), cwd=cwd, stdout=stream, stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        with log.open('rb') as stream:
            stream.seek(max(0, log.stat().st_size - 10000))
            tail = stream.read().decode(errors='replace')
        raise RuntimeError(f'{command[0]} failed; see {log}\n' + tail)


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
                            writable=write, executable=execute, device=device, atomic=offset == 0,
                            dataCacheable=False))
    return dict(resetVector=str(base), axiDataBits=width, physicalAddressBits=32 if width == 64 else 56,
                virtualAddressBits=0, iCacheBytes=0, dCacheBytes=0, l2CacheBytes=0, pmpEntries=0,
                memoryRegions=regions)


def local_interrupt_base(config):
    value = config.get('localInterruptBase')
    return int(value) if value is not None else None


def compile_tb(rtl, directory, width, pa, top='core_tb', source=None, extra_files=(), software=None):
    source = source or Path('test/core_tb.sv').resolve()
    files = [(rtl / name).resolve() for name in (rtl / 'filelist.f').read_text().splitlines()]
    parameters = json.loads((rtl / 'ditdah_a1_config.json').read_text())['parameters']
    interrupts, harts = parameters['enableInterrupts'], parameters['hartCount']
    bindings, ports, platform = [], [], []
    local_base = local_interrupt_base(parameters) if top == 'core_tb' else None
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
        translated = parameters.get('virtualAddressBits') == 39
        if translated:
            unit = f'dut.core_{hart}' if top == 'core_tb' else 'dut'
            translation = unit + '.translation'
            for port in range(2):
                observers.append(f'''  always @(posedge clock) if (!reset) begin
    if ({translation}.ports_{port}_request_valid && {translation}.ports_{port}_request_ready) begin
      {prefix}$display("TRANSLATE_REQUEST {port} %016h %01h %01h %01h %016h %01h %01h", {translation}.ports_{port}_request_bits_address,
        {translation}.ports_{port}_request_bits_privilege, {translation}.ports_{port}_request_bits_fetch, {translation}.ports_{port}_request_bits_write,
        {translation}.state_satp, {translation}.state_sum, {translation}.state_mxr);
    end
    if ({translation}.ports_{port}_response_valid && {translation}.ports_{port}_response_ready) begin
      {prefix}$display("TRANSLATE_RESPONSE {port} %016h %01h %016h", {translation}.ports_{port}_response_bits_address,
        {translation}.ports_{port}_response_bits_fault, {translation}.ports_{port}_response_bits_cause);
    end
  end''')
            observers.append(f'''  always @(posedge clock) if (!reset) begin
    if ({translation}.memory_request_valid && {translation}.memory_request_ready) begin
      {prefix}$display("WALK_REQUEST %016h %02h", {translation}.memory_request_bits_address, {translation}.memory_request_bits_tag);
    end
    if ({translation}.memory_response_valid && {translation}.memory_response_ready) begin
      {prefix}$display("WALK_RESPONSE %016h %01h %02h", {translation}.memory_response_bits_data,
        {translation}.memory_response_bits_fault, {translation}.memory_response_bits_tag);
    end
  end''')
        if top == 'core_tb' and parameters['dCacheBytes'] or translated:
            core = f'dut.core_{hart}.backend.lsu.memory' if translated and top == 'core_tb' else 'dut.backend.lsu.memory' if translated else f'dut.core_{hart}.data'
            sample = f'dut.data_cache_{hart}.dV'
            observers.append(f'''  always @(posedge clock) if (!reset) begin
    if ({core}_request_valid && {core}_request_ready) begin
      {prefix}$display("ARCH_DATA_REQUEST %s %016h %0d %016h %02h %01h",
        {core}_request_bits_atomic ? "atomic" : ({core}_request_bits_write ? "write" : "read"),
        {core}_request_bits_address, 1 << {core}_request_bits_size,
        {core}_request_bits_write ? {core}_request_bits_data & access_mask({core}_request_bits_size) : 64'b0,
        {core}_request_bits_tag, {core}_request_bits_privileged);
    end
''' + (f'''    if ({sample}.sampleValid) begin
      {prefix}$display("CACHE_SAMPLE %016h %016h %02h", {sample}.sampleAddress,
        {sample}.sampleData, {sample}.sampleTag);
    end
''' if top == 'core_tb' and parameters['dCacheBytes'] else '') + f'''
    if ({core}_response_valid && {core}_response_ready) begin
      {prefix}$display("ARCH_DATA_RESPONSE %016h %01h %02h", {core}_response_bits_data,
        {core}_response_bits_fault, {core}_response_bits_tag);
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
                physical = f'dut.fabric.{port}_{hart}'
                for channel in ('request', 'response'):
                    for field in ('valid', 'ready'):
                        bindings.append(f'assign {channel}_{field}[{index}] = {physical}_{channel}_{field};')
                    for field in (('address', 'data', 'size', 'mask', 'tag', 'write', 'fetch', 'atomic', 'atomicOperation', 'scEligible', 'privileged') if channel == 'request' else ('data', 'fault', 'tag')):
                        bindings.append(f'assign {channel}s[{index}].{field} = {physical}_{channel}_bits_{field};')
            if interrupts:
                ports += [f'.interrupts_{hart}_{name}(irq_by_hart[{hart}][{index}]),'
                          for index, name in enumerate(('software', 'timer', 'external'))]
                bindings += [f'assign effective_irq[{hart}][{index}] = {core}.interrupts_{name};'
                             for index, name in enumerate(('software', 'timer', 'external'))]
        if local_base is not None:
            ports.append('.timeTick(local_tick),')
            instances = re.findall(r'\bDitDahA1LocalInterrupts\s+(\w+)\s*\(', (rtl / 'DitDahA1MemoryFabric.sv').read_text())
            assert len(instances) == 1, 'Missing local interrupt instance'
            device = f'dut.fabric.{instances[0]}'
            external = '{' + ', '.join(f'irq_by_hart[{h}]' for h in reversed(range(harts))) + '}'
            effective = '{' + ', '.join(f'effective_irq[{h}]' for h in reversed(range(harts))) + '}'
            sleeping = '{' + ', '.join(f'dut.core_{h}.status_sleep' for h in reversed(range(harts))) + '}'
            prefix = '$write("HART %0d ", bus_owner / 2);' if harts > 1 else ''
            platform.append(f'''  task observe_platform;
    $display("CYCLE %0d %01h %h %h %h", cycles, local_tick, {external}, {effective}, {sleeping});
    if ({device}.memory_request_valid && {device}.memory_request_ready) begin
      {prefix}
      $display("LOCAL_REQUEST %s %016h %0d %016h %02h",
        {device}.memory_request_bits_atomic ? "atomic" : ({device}.memory_request_bits_fetch ? "fetch" : ({device}.memory_request_bits_write ? "write" : "read")),
        {device}.memory_request_bits_address, 1 << {device}.memory_request_bits_size,
        {device}.memory_request_bits_write ? {device}.memory_request_bits_data & access_mask({device}.memory_request_bits_size) : 64'b0,
        {device}.memory_request_bits_tag);
    end
    if ({device}.memory_response_valid && {device}.memory_response_ready) begin
      {prefix}
      $display("LOCAL_RESPONSE %016h %01h %02h", {device}.memory_response_bits_data,
        {device}.memory_response_bits_fault, {device}.memory_response_bits_tag);
    end
  endtask''')
    (directory / 'core_bindings.svh').write_text('\n'.join(bindings) + '\n')
    (directory / 'core_ports.svh').write_text('\n'.join(ports) + '\n')
    (directory / 'platform_observers.svh').write_text('\n'.join(platform) + '\n')
    if interrupts and top == 'memory_tb':
        extra_files = [*extra_files, Path('test/core_tb.sv').resolve()]
    command = ['verilator', '--binary', '--timing', '--assert', '-j', '2', '--top-module', top,
         '-Wno-TIMESCALEMOD', '-Wno-WIDTHTRUNC', '-Wno-WIDTHEXPAND',
         f'-DAXI_BITS={width}', f'-DPA_BITS={pa}', f'-DHARTS={harts}', '-I' + str(directory.resolve()), *(['-DENABLE_INTERRUPTS'] if interrupts else []), '-I' + str(rtl.resolve()),
         *(['-DICACHE'] if parameters['iCacheBytes'] else []),
         *(['-DLOCAL_INTERRUPTS'] if local_base is not None else []),
         *(['-DSOFTWARE'] if software else []),
         *([f'-DMEMORY_BYTES={software["memoryBytes"]}', f'-DTIME_TICK_CYCLES={software["timeTickCycles"]}'] if software else []),
         '--Mdir', str((directory / 'obj').resolve()), *files, *extra_files, source]
    binary, stamp = (directory / 'obj' / ('V' + top)).resolve(), directory / 'compile-inputs.json'
    inputs = [*files, *extra_files, source, rtl / 'filelist.f', rtl / 'ditdah_a1_config.json', *directory.glob('*.svh')]
    hashes = {str(path): hashlib.sha256(Path(path).read_bytes()).hexdigest() for path in inputs}
    tools = {name: subprocess.check_output([name, '--version'], text=True).splitlines()[0]
             for name in ('verilator', os.environ.get('CXX', 'g++'), 'make')}
    identity = dict(command=list(map(str, command)), inputs=hashes, tools=tools,
                    environment=hashlib.sha256(json.dumps(dict(os.environ), sort_keys=True).encode()).hexdigest())
    if stamp.exists() and binary.exists():
        previous = json.loads(stamp.read_text())
        if previous.get('inputs') == identity and previous.get('binaryHash') == hashlib.sha256(binary.read_bytes()).hexdigest():
            return binary
    stamp.unlink(missing_ok=True)
    run(command, directory / 'compile.log')
    assert all(hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest for path, digest in hashes.items()), 'Inputs changed during compilation'
    stamp.write_text(json.dumps(dict(inputs=identity, binaryHash=hashlib.sha256(binary.read_bytes()).hexdigest()), indent=2) + '\n')
    return binary


def log_lines(source):
    if isinstance(source, Path):
        with source.open() as stream:
            yield from (line.rstrip('\n') for line in stream)
    else:
        yield from source


def fetch_checker(config, faults, local_faults, architectural=None, buffered=()):
    if architectural is None:
        entries = []
        while entry := (yield):
            entries.append(entry)
            if entry[1][0] == 'ARCH_REQUEST':
                break
        if entry is None:
            entries.append(None)
        return (yield from fetch_checker(config, faults, local_faults, entry is not None, iter(entries)))
    def allowed(address):
        return address % 4 == 0 and address + 4 <= 1 << config['physicalAddressBits'] and any(
            int(region['base']) <= address and address + 4 <= int(region['base']) + int(region['size'])
            and region['executable'] for region in config['memoryRegions'])

    pending, requests, demand, physical_demand = None, {}, None, None
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
    buffered, missing = iter(buffered), object()
    while True:
        entry = next(buffered, missing)
        if entry is missing:
            entry = yield
        if entry is None:
            break
        line, fields = entry
        if fields[:1] == ['ARCH_REQUEST']:
            address, tag = (int(value, 16) for value in fields[1:])
            assert not requests and pending is None and address in reachable, 'Unexpected architectural fetch identity or control flow'
            requests[tag] = address
            demand = address
            physical_demand = address
            arch_wraps += int(tag == 0 and arch_accepted != 0)
            arch_accepted += 1
            reachable.add(address + 4)
        elif fields[:2] == ['TRANSLATE_RESPONSE', '0']:
            physical_demand = int(fields[2], 16)
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
            expected = demand is not None and (address & ~63 == physical_demand & ~63 if config['iCacheBytes'] else address == physical_demand)
            assert (expected if architectural else address in reachable), f'Fetch outside current instruction demand: {line}'
            reachable.add(address + 4)
            pending = [address, architectural and not requests, demand]
            accepted += 1
        elif fields[:1] == ['FETCH']:
            address, response, instruction = (int(value, 16) for value in fields[1:])
            assert pending is not None and pending[0] == address, f'Unrequested fetch response: {line}'
            assert response == (2 if address == faults.get('fetch') else 0), f'Fetch response: {line}'
            if not architectural:
                (failed if response else fetched)[address if response else (address, instruction)] += 1
            elif not pending[1]:
                virtual = pending[2] if config.get('virtualAddressBits') == 39 else address
                (physical_failed if response else physical_fetched)[virtual if response else (virtual, instruction)] += 1
            pending = None
            completed += 1
        elif fields[:1] == ['TRACE']:
            trace = tuple(int(value, 16) for value in fields[1:])
            pc, instruction, trap, cause = trace[1], trace[2], trace[7], trace[8]
            reachable.add(trace[3])
            if trap and cause >> 63:
                pass
            elif trap and cause in (1, 12):
                if architectural or (trace[0] not in local_faults and allowed(pc)):
                    assert failed[pc], f'Fetch fault without failed response: {line}'
                    failed[pc] -= 1
                if cause == 1 and architectural and not config['iCacheBytes'] and trace[0] not in local_faults and allowed(pc):
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


def check_fetches(lines, config, faults, local_faults=()):
    checker = fetch_checker(config, faults, local_faults)
    next(checker)
    for line in lines:
        checker.send((line, line.split()))
    try:
        checker.send(None)
    except StopIteration as result:
        return result.value


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


def check_access_privileges(lines, modes, requests, privileges, required):
    expected = iter(privilege != 0 for request, privilege in zip(requests, privileges) if request[0] != 'fetch')
    mode, demand, retired, pending = 3, 3, 0, None
    for line in lines:
        fields = line.split()
        if fields[:1] == ['ARCH_REQUEST']:
            demand = mode
        elif fields[:1] == ['REQUEST']:
            assert pending is None or not required, 'Missing accepted access privilege'
            pending = demand != 0 if fields[1] == 'fetch' else next(expected)
        elif fields[:1] == ['ACCESS_PRIVILEGE']:
            assert pending is not None and int(fields[1], 16) == pending, 'Accepted access privilege differs from architectural context'
            pending = None
        elif fields[:1] == ['TRACE']:
            retired += 1
            mode = modes[retired]
    assert pending is None or not required, 'Missing final accepted access privilege'
    assert not required or next(expected, None) is None, 'Missing architectural data request privilege'


def translation_maintenance(trace):
    instruction = trace[2]
    funct3, address = (instruction >> 12) & 7, instruction >> 20
    write = instruction & 127 == 0x73 and funct3 in (1, 2, 3, 5, 6, 7) and (funct3 & 3 == 1 or (instruction >> 15) & 31)
    return not trace[7] and (instruction & 0xfe007fff == 0x12000073 or write and
        (address == 0x180 or 0x3a0 <= address <= 0x3ae or 0x3b0 <= address <= 0x3ef))


def check_translation_result(walk, result, config, model, history):
    def read_pte(address, reads):
        entry = next(reads, None)
        if entry is None:
            if walk.get('cancelled'):
                raise StopIteration
            assert not any(int(r['base']) <= address and address + 8 <= int(r['base']) + int(r['size']) and r['readable'] and not r['device'] for r in config['memoryRegions']) or not pmp_allowed(
                [model.pmp_config(i) for i in range(config['pmpEntries'])], [model.csrs[0x3b0+i] for i in range(config['pmpEntries'])], address, 8, 'read', config['physicalAddressBits'], 1), 'Permitted PTE omitted physical service'
            raise Fault(5, address)
        assert entry[0] == address, 'PTE address differs from independent walk'
        if entry[2]:
            raise Fault(5, address)
        return entry[1]
    paged = walk['privilege'] != 3 and walk['satp'] >> 60 == 8
    cached = [reads for satp, vpn, bits, reads in history if satp == walk['satp'] and walk['address'] >> bits == vpn]
    candidates = [walk['reads']] if walk['reads'] or not paged else cached or [[]]
    matches = bool(walk.get('cancelled'))
    for candidate in candidates:
        reads = iter(candidate)
        expected, fault, cause = walk['address'], False, 0
        try:
            expected = sv39_walk(walk['address'], walk['kind'], walk['privilege'], walk['satp'], walk['status'], lambda address: read_pte(address, reads))
        except StopIteration:
            continue
        except Fault as error:
            fault, cause = True, error.cause
        matches |= result == (expected, fault, cause) and next(reads, None) is None
        if config.get('tlbEntries') and paged and walk['reads'] and not fault and not walk.get('stale'):
            bits = 12 + 9 * (3 - len(walk['reads']))
            entry = walk['satp'], walk['address'] >> bits, bits, tuple(walk['reads'])
            if entry not in history:
                history.append(entry)
    assert matches, 'Translation result lacks a matching walk or authorized cached leaf'
    return paged and not walk['reads'] and bool(cached)


def check_core_translations(lines, config, program, expected_requests):
    model, walk, request, architectural = Model(config, program.memory, program.faults), None, None, []
    history = []
    for line in lines:
        fields = line.split()
        if fields[:1] == ['TRANSLATE_REQUEST']:
            port, address, privilege, fetch, write, satp, sum_enabled, mxr = (int(value, 16) for value in fields[1:])
            assert walk is None, 'Overlapping Core translations'
            walk = dict(port=port, address=address, privilege=privilege, kind='fetch' if fetch else 'write' if write else 'read',
                        satp=satp, status=(sum_enabled << 18) | (mxr << 19), reads=[])
        elif fields[:1] == ['ARCH_CANCEL'] and walk and walk['port'] == 0:
            walk['cancelled'] = True
        elif fields[:1] == ['WALK_REQUEST']:
            assert walk and request is None, 'Unowned Core page-table request'
            request = int(fields[1], 16), int(fields[2], 16)
        elif fields[:1] == ['WALK_RESPONSE']:
            data, fault, tag = (int(value, 16) for value in fields[1:])
            assert request and tag == request[1], 'Core page-table response identity'
            expected = sum(model.memory.get(request[0] + byte, 0) << (8 * byte) for byte in range(8))
            assert fault == (request[0] == program.faults.get('read')) and (fault or data == expected), 'Core PTE response differs from independent memory'
            walk['reads'].append((request[0], data, bool(fault)))
            request = None
        elif fields[:1] == ['TRANSLATE_RESPONSE']:
            port, physical, fault, cause = (int(value, 16) for value in fields[1:])
            assert walk and walk['port'] == port and request is None, 'Unowned Core translation response'
            check_translation_result(walk, (physical, fault, cause), config, model, history)
            walk = None
        elif fields[:1] == ['ARCH_DATA_REQUEST']:
            architectural.append((fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)))
        elif fields[:1] == ['IRQ']:
            model.set_interrupts(int(fields[1], 16))
        elif fields[:1] == ['TRACE']:
            if translation_maintenance(tuple(int(v, 16) for v in fields[1:])):
                history.clear()
                if walk:
                    walk['stale'] = True
            (model.interrupt if int(fields[9], 16) >> 63 else model.step)()
    assert architectural == [event for event in expected_requests if event[0] != 'fetch'], 'Core LSU physical requests differ from architectural translation'


def compare(binary, directory, config, transport='axi', selected=()):
    base = int(config['resetVector'])
    coverage = [0] * 6
    coverage_names = (('awBeforeW', 'wBeforeAw', 'awWithW', 'arStall', 'awStall', 'wStall') if transport == 'axi'
                      else ('overlap', 'instructionStall', 'dataStall', 'responseDelay', 'permissionReject', 'architecturalTagWrap' if config['iCacheBytes'] else 'tagWrap'))
    count = 0
    reports = []
    pipeline_max, dependency_stalls = 0, 0
    for name, program in cases(base, config['pmpEntries'] != 0, config['enableInterrupts'], config.get('enableUserMode', False), local_interrupt_base(config), config.get('enableSupervisorMode', False), config.get('virtualAddressBits') == 39):
        if selected and name not in selected:
            continue
        image = directory / (name + '.hex')
        image.write_text('\n'.join(f'{program.memory.get(base + i, 0):02x}' for i in range(65536)) + '\n')
        model = Model(config, program.memory, program.faults)
        expected, expected_atomics, expected_modes = [], [], [3]
        def advance():
            first = len(model.requests)
            record = model.step()
            expected_modes.append(getattr(model, 'privilege', 3))
            if any(event[0] == 'atomic' for event in model.requests[first:]):
                expected_atomics.append((model.atomic_operation, int(model.sc_eligible)))
            return record
        for _ in range(2000):
            if hasattr(program, 'interrupts'):
                break
            record = advance()
            expected.append(record)
            if not record[7] and record[1] == program.stop:
                break
        else:
            raise AssertionError(f'{name}: reference program did not finish')
        if hasattr(program, 'translation'):
            assert all(model.registers[index] == value for index, value in program.translation.items()), 'Translation context did not select distinct physical data'
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
                expected, expected_atomics, causes, deferred, expected_modes = [], [], [], 0, [3]
                for line in lines:
                    fields = line.split()
                    if fields[:1] == ['IRQ']:
                        model.set_interrupts(int(fields[1], 16))
                    elif fields[:1] == ['TRACE']:
                        observed = tuple(int(v, 16) for v in fields[1:])
                        pending = model.interrupt_cause()
                        record = model.interrupt() if observed[8] >> 63 else advance()
                        if observed[8] >> 63:
                            expected_modes.append(getattr(model, 'privilege', 3))
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
            cache_report = None
            translation_report = None
            if config.get('virtualAddressBits') == 39 and transport == 'memory':
                check_core_translations(lines, config, program, model.requests)
            elif transport == 'axi' and (config.get('virtualAddressBits') == 39 or config.get('dCacheBytes') or any(event[0] == 'atomic' for event in model.requests) or name in ('fence_ordering', 'synchronization')):
                checked = check_multicore(lines, config, program, name, atomic_metadata=True)
                cache_report = checked.get('dataCache')
                translation_report = checked.get('translation')
                if name == 'sv39_reuse':
                    assert translation_report['pteReads'] == (3 if config.get('tlbEntries') else 99), 'Repeated page walk count'
            else:
                assert data_bus == expected_bus, f'{name}: unexpected data accesses\nactual {data_bus}\nexpected {expected_bus}'
            if transport == 'memory':
                assert [tuple(int(value, 16) for value in line.split()[1:]) for line in lines if line.startswith('ATOMIC ')] == expected_atomics, 'Memory atomic metadata differs from independent instructions'
                requests = [(v[1], int(v[2], 16), int(v[3]), int(v[4], 16)) for line in lines
                            if line.startswith('REQUEST ') for v in [line.split()] if v[1] != 'fetch']
                if config.get('virtualAddressBits') != 39:
                    assert requests == [r for r in model.requests if r[0] != 'fetch'], f'{name}: unexpected Core requests'
            if not config.get('dCacheBytes') and config.get('virtualAddressBits') != 39 and (config.get('enableUserMode') or any(line.startswith('ACCESS_PRIVILEGE ') for line in lines)):
                check_access_privileges(lines, expected_modes, model.requests, model.request_privileges, config.get('enableUserMode', False))
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
            reports.append(dict(test=name, seed=seed, events=len(actual), cycles=elapsed, busTransactions=len(bus), fetches=fetches,
                                **(dict(translation=translation_report) if translation_report is not None else {}),
                                **(dict(dataCache=cache_report) if cache_report is not None else {})))
        print(f'  {name}: {len(expected)} events, three bus schedules', flush=True)
    assert reports, 'No selected scalar program'
    if not selected:
        assert all(coverage), f'{transport} coverage missing: {dict(zip(coverage_names, coverage))}'
        assert pipeline_max >= 2 and dependency_stalls, f'Pipeline coverage missing: {pipeline_max}, {dependency_stalls}'
    return dict(events=count, cases=reports, pipelineCoverage=dict(maxOccupancy=pipeline_max, dependencyStalls=dependency_stalls),
                **{('busCoverage' if transport == 'axi' else 'portCoverage'): dict(zip(coverage_names, coverage))})


def check_multicore(lines, config, program, name, atomic_metadata=False, software_output=False):
    harts, base = config['hartCount'], int(config['resetVector'])
    covers, results, passed = [], [], False
    memory, active = dict(program.memory), None
    failures = getattr(program, 'exclusive_failures', 0)
    models = [Model(config, {}, program.faults, hart_id=h) for h in range(harts)]
    local_base = local_interrupt_base(config)
    device = LocalInterrupts(local_base, harts) if local_base is not None else None
    software = getattr(program, 'software', None)
    console, console_events, successful_stores = [bytearray() for _ in range(harts)], deque(), Counter()
    for model in models:
        model.memory = memory
    pending, finished = [None] * harts, set()
    architectural, cache_counts = [None] * harts, [Counter() for _ in range(harts)]
    hit_addresses = [Counter() for _ in range(harts)]
    data_cache = bool(config.get('dCacheBytes'))
    translated = config.get('virtualAddressBits') == 39
    observed_data = data_cache or translated
    implicit, walks = [None] * harts, [None] * harts
    translation_history = [[] for _ in range(harts)]
    translation_counts = Counter()
    fetch_privileges, retired_privileges = [3] * harts, [3] * harts
    fetch_checks = [fetch_checker(config, program.faults, model.local_fetch_faults) for model in models]
    for checker in fetch_checks:
        next(checker)
    collisions, tags, sources, events, effects = set(), {}, set(), 0, Counter()
    interrupts, causes, overtaken = Counter(), Counter(), 0
    deferred = [0] * harts
    waiting, sleep_cycles, wake = [False] * harts, [0] * harts, [False] * harts
    wait_started, waiting_mask, wake_mask = [0] * harts, 0, 0
    interrupt_dirty, previous_external, previous_time, next_timer, expected_levels = True, None, 0, 0, 0
    concurrent = Counter()
    monitor, reservation_max, sc_results = ExclusiveMonitor(), 0, Counter()
    observed_reservations = None
    elapsed_cycles, transactions, axi_transactions = None, 0, 0

    def no_service(*args):
        raise AssertionError('Architectural data access without bus service')

    for model in models:
        model.external_access = no_service

    def service(hart, event, atomic_fault=False, local=False):
        nonlocal interrupt_dirty
        assert pending[hart] is None, 'Second memory operation before retirement'
        accesses, response = [], None

        def access(address, size, kind, data):
            nonlocal response, interrupt_dirty
            wanted = kind, address, size, data if kind in ('write', 'atomic') else 0
            assert event == wanted, f'{name}: data service {event} != independent instruction {wanted}'
            accesses.append(wanted)
            operation = models[hart].atomic_operation if kind == 'atomic' else None
            if kind == 'atomic':
                assert (operation, models[hart].sc_eligible) == (active['operation'], active['eligible']), 'Atomic operation or local reservation differs from raw instruction'
                assert not atomic_metadata or active.get('atomicMetadata'), 'Missing atomic request metadata'
                if operation == 3 and not active.get('scSuccess', False) and not atomic_fault:
                    return 1
            if local:
                try:
                    value = device.access(address, size, kind, data)
                except Fault:
                    response = (0, 1)
                    raise
                response = (value, 0)
                if kind == 'write':
                    interrupt_dirty = True
                    effects[hart, address] += 1
                    monitor.write(address, size)
                return value
            if atomic_fault or address == program.faults.get(kind):
                raise Fault(5 if kind == 'read' or operation == 2 else 7, address)
            if kind == 'write':
                monitor.write(address, size)
            if software and software['console'] <= address < software['console'] + 4 * harts:
                assert kind == 'write' and size == 4 and address == software['console'] + 4 * hart, 'Console access width, direction or hart'
                assert 0 <= data < 128, 'Console requires ASCII bytes'
                console[hart].append(data)
                console_events.append((hart, data))
                return 0
            old = sum(memory.get(address + byte, 0) << (byte * 8) for byte in range(size))
            if kind == 'read':
                response = (old, 0)
            if kind == 'write' or (kind == 'atomic' and operation != 2):
                value = atomic_value(operation, old, data, size) if kind == 'atomic' and operation != 3 else data
                for byte in range(size):
                    memory[address + byte] = (value >> (byte * 8)) & 255
                effects[hart, address] += 1
                if software and address == software['results'] + 8 * hart and size == 8 and data == 1:
                    successful_stores[hart] += 1
            return 0 if kind == 'write' or operation == 3 else old

        models[hart].external_access = access
        pending[hart] = models[hart].step()
        models[hart].external_access = no_service
        assert len(accesses) == 1, 'Bus service did not match an architectural access'
        return response

    def complete_data(hart):
        access = architectural[hart]
        if 'expected' not in access or 'response' not in access:
            return
        data, fault, tag = access['response']
        expected, expected_fault = access['expected']
        assert tag == access['tag'] and fault == expected_fault and (fault or data == expected), 'Architectural data response differs from independent service'
        architectural[hart] = None
        cache_counts[hart]['completed'] += 1

    def complete_walk(hart):
        access = implicit[hart]
        if access is None or 'expected' not in access or 'response' not in access:
            return
        data, fault, tag = access['response']
        expected, expected_fault = access['expected']
        assert tag == access['tag'] and fault == expected_fault and (fault or data == expected), 'PTE response differs from physical service'
        walks[hart]['reads'].append((access['event'][1], data, bool(fault)))
        implicit[hart] = None

    def data_owner(hart, event, tag):
        candidates = [access for access in (implicit[hart], architectural[hart])
                      if access and access['event'] == event and access['tag'] == tag and 'expected' not in access]
        assert len(candidates) == 1, 'Physical data service lacks unique LSU or page-table owner'
        return candidates[0]

    for line in log_lines(lines):
        fields = line.split()
        if fields[:1] == ['COVER']:
            covers.append(list(map(int, fields[1:])))
            continue
        if fields[:1] == ['RESULT']:
            results.append((int(fields[1]), int(fields[2], 16)))
            continue
        if fields == ['PASS']:
            passed = True
            continue
        if fields[:1] == ['CYCLE']:
            assert device is not None, 'Unexpected platform event'
            cycle, tick = int(fields[1]), int(fields[2], 16)
            external, effective, sleeping = (int(value, 16) for value in fields[3:])
            device.begin_cycle(cycle, tick)
            assert tick == int(cycle % (software['timeTickCycles'] if software else 1) == 0), 'Platform timebase divider mismatch'
            if interrupt_dirty or external != previous_external or device.time < previous_time or device.time >= next_timer:
                expected_levels, wake_mask = 0, 0
                for hart, model in enumerate(models):
                    levels = device.levels(hart) | ((external >> (3 * hart)) & 7)
                    expected_levels |= levels << (3 * hart)
                    model.set_interrupts(levels)
                    wake[hart] = bool(model.csrs[0x304] & model.csrs[0x344])
                    wake_mask |= int(wake[hart]) << hart
                next_timer = min((value for value in device.compare if value > device.time), default=MASK + 1)
                interrupt_dirty, previous_external = False, external
            previous_time = device.time
            assert effective == expected_levels, f'Platform interrupt mismatch at cycle {cycle}'
            assert sleeping == waiting_mask, f'Architectural wait mismatch at cycle {cycle}'
            waking = waiting_mask & wake_mask
            waiting_mask &= ~waking
            while waking:
                bit = waking & -waking
                hart = bit.bit_length() - 1
                sleep_cycles[hart] += cycle - wait_started[hart] + 1
                waiting[hart] = False
                waking ^= bit
            continue
        if fields[:1] == ['CONSOLE']:
            assert software and console_events and console_events.popleft() == (int(fields[1]), int(fields[2], 16)), 'Console byte without matching software service'
            continue
        if fields[:1] == ['EXCLUSIVE']:
            assert observed_reservations is None
            observed_reservations = int(fields[1])
            continue
        if fields[:1] == ['CYCLES']:
            assert elapsed_cycles is None
            elapsed_cycles = int(fields[1])
            continue
        if fields[:1] == ['HART']:
            hart, fields = int(fields[1]), fields[2:]
        elif harts == 1 and fields and fields[0] in ('REQUEST', 'ACCESS_PRIVILEGE', 'ATOMIC', 'BUS', 'READ', 'WRITE', 'INTERFERE', 'RESPONSE', 'FETCH', 'IRQ', 'TRACE', 'ARCH_REQUEST', 'ARCH_FETCH', 'ARCH_CANCEL', 'LOCAL_REQUEST', 'LOCAL_RESPONSE', 'ARCH_DATA_REQUEST', 'ARCH_DATA_RESPONSE', 'CACHE_SAMPLE', 'TRANSLATE_REQUEST', 'TRANSLATE_RESPONSE', 'WALK_REQUEST', 'WALK_RESPONSE'):
            hart = 0
        else:
            continue
        assert 0 <= hart < harts
        kind = fields[0]
        if kind != 'TRACE':
            fetch_checks[hart].send((line, fields))
        if kind in ('ARCH_REQUEST', 'ARCH_FETCH', 'ARCH_CANCEL'):
            if kind == 'ARCH_REQUEST':
                fetch_privileges[hart] = retired_privileges[hart]
            assert kind != 'ARCH_REQUEST' or not waiting[hart], 'New architectural fetch while waiting'
            if kind == 'ARCH_CANCEL' and walks[hart] and walks[hart]['port'] == 0:
                walks[hart]['cancelled'] = True
            continue
        assert kind in ('REQUEST', 'ACCESS_PRIVILEGE', 'ATOMIC', 'BUS', 'READ', 'WRITE', 'INTERFERE', 'RESPONSE', 'FETCH', 'IRQ', 'TRACE', 'LOCAL_REQUEST', 'LOCAL_RESPONSE', 'ARCH_DATA_REQUEST', 'ARCH_DATA_RESPONSE', 'CACHE_SAMPLE', 'TRANSLATE_REQUEST', 'TRANSLATE_RESPONSE', 'WALK_REQUEST', 'WALK_RESPONSE'), 'Unknown hart event'
        if kind == 'TRANSLATE_REQUEST':
            port, address, privilege, fetch, write, satp, sum_enabled, mxr = (int(value, 16) for value in fields[1:])
            assert translated and walks[hart] is None and port in (0, 1), 'Overlapping translation ownership'
            assert privilege == (fetch_privileges[hart] if port == 0 else models[hart].data_privilege()), 'Translation effective privilege'
            assert (satp, sum_enabled, mxr) == (models[hart].csrs[0x180], bool(models[hart].csrs[0x300] & (1 << 18)), bool(models[hart].csrs[0x300] & (1 << 19))), 'Translation context snapshot'
            walks[hart] = dict(port=port, address=address, privilege=privilege, kind='fetch' if fetch else 'write' if write else 'read',
                               satp=satp, status=(sum_enabled << 18) | (mxr << 19), reads=[])
            translation_counts['requests'] += 1
        elif kind == 'TRANSLATE_RESPONSE':
            port, physical, fault, cause = (int(value, 16) for value in fields[1:])
            walk = walks[hart]
            assert translated and walk and walk['port'] == port and implicit[hart] is None, 'Unowned translation response'
            translation_counts['hits'] += check_translation_result(walk, (physical, fault, cause), config, models[hart], translation_history[hart])
            walks[hart] = None
            translation_counts['responses'] += 1
        elif kind == 'WALK_REQUEST':
            address, tag = (int(value, 16) for value in fields[1:])
            assert translated and walks[hart] and implicit[hart] is None, 'Unowned page-table access'
            assert pmp_allowed([models[hart].pmp_config(i) for i in range(config['pmpEntries'])], [models[hart].csrs[0x3b0+i] for i in range(config['pmpEntries'])], address, 8, 'read', config['physicalAddressBits'], 1), 'Page walk bypassed S-mode physical protection'
            implicit[hart] = dict(event=('read', address, 8, 0), tag=tag, walk=True)
            translation_counts['pteReads'] += 1
        elif kind == 'WALK_RESPONSE':
            assert implicit[hart] and 'response' not in implicit[hart], 'Unowned PTE response'
            implicit[hart]['response'] = tuple(int(value, 16) for value in fields[1:])
            complete_walk(hart)
        elif kind == 'ARCH_DATA_REQUEST':
            assert observed_data and architectural[hart] is None and pending[hart] is None, 'Overlapping architectural data requests'
            event = fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            assert event[0] in ('read', 'write', 'atomic') and int(fields[6], 16) == (models[hart].data_privilege() != 0), 'Architectural access context'
            architectural[hart] = dict(event=event, tag=int(fields[5], 16))
            cache_counts[hart]['accepted'] += 1
            cache_counts[hart]['reads'] += int(event[0] == 'read')
        elif kind == 'CACHE_SAMPLE':
            address, value, tag = (int(field, 16) for field in fields[1:])
            access = data_owner(hart, ('read', address, 8, 0), tag)
            assert data_cache and access and not access.get('physical') and 'expected' not in access, 'Unowned, duplicate or physically serviced cache sample'
            assert access['event'] == ('read', address, 8, 0) and access['tag'] == tag and address % 8 == 0, 'Cache sample request identity'
            assert any(region.get('dataCacheable', False) and not region['device'] and region['readable']
                       and int(region['base']) <= address and address + 8 <= int(region['base']) + int(region['size'])
                       for region in config['memoryRegions']), 'Cache sample outside permitted cacheable RAM'
            expected = (sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8)), 0) if access.get('walk') else service(hart, access['event'])
            assert expected == (value, 0), 'Cache sample differs from independent shared memory'
            access['expected'] = expected
            cache_counts[hart]['hits'] += int(not access.get('walk'))
            hit_addresses[hart][address] += int(not access.get('walk'))
            cache_counts[hart]['hitsDuringPeerService'] += int(not access.get('walk') and active is not None and active['hart'] != hart)
            (complete_walk if access.get('walk') else complete_data)(hart)
        elif kind == 'ARCH_DATA_RESPONSE':
            access = architectural[hart]
            assert observed_data and access and 'response' not in access, 'Unowned or duplicate architectural response'
            access['response'] = tuple(int(field, 16) for field in fields[1:])
            if not access.get('physical') and 'expected' not in access:
                assert access['response'][1] and pending[hart] is None, 'Architectural response without a cache sample or physical service'
                first = len(models[hart].requests)
                pending[hart] = models[hart].step()
                assert pending[hart][7] and [event for event in models[hart].requests[first:] if event[0] != 'fetch'] == [access['event']], 'Unexpected cache-local rejection'
                access['expected'] = (0, 1)
                cache_counts[hart]['rejectedReads'] += int(access['event'][0] == 'read')
            complete_data(hart)
        elif kind == 'REQUEST':
            assert active is None, 'Overlapping source ownership'
            event = fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            tag = int(fields[5], 16)
            access = data_owner(hart, event, tag) if observed_data and event[0] != 'fetch' else None
            privilege = 1 if access and access.get('walk') else fetch_privileges[hart] if event[0] == 'fetch' else models[hart].data_privilege() if hasattr(models[hart], 'data_privilege') else 3
            active = dict(hart=hart, event=event, tag=tag, bus=False, response=None, expectedPrivileged=privilege != 0)
            if access:
                assert access and access['event'] == event and access['tag'] == tag and 'expected' not in access and not access.get('physical'), 'Physical request lacks unique architectural ownership'
                access['physical'] = True
                active['walk'] = access.get('walk', False)
                cache_counts[hart]['physicalReads'] += int(event[0] == 'read' and not active['walk'])
            if event[0] == 'atomic':
                instruction_address = models[hart].translate(models[hart].pc, 'fetch')
                instruction = sum(memory.get(instruction_address + byte, 0) << (8 * byte) for byte in range(4))
                operation = instruction >> 27
                assert instruction & 127 == 47 and (instruction >> 12) & 7 == 3 and operation in (0, 1, 2, 3, 8)
                assert operation != 2 or (instruction >> 20) & 31 == 0
                active.update(operation=operation, eligible=operation == 3 and models[hart].local_reservation == event[1:3])
            source = 2 * hart + int(event[0] != 'fetch')
            sources.add(source)
            if tag in tags and tags[tag] != hart:
                collisions.add(tag)
            tags[tag] = hart
        elif kind == 'ACCESS_PRIVILEGE':
            assert active and active['hart'] == hart and not active.get('privilegeMetadata'), 'Unowned access privilege'
            assert int(fields[1], 16) == active['expectedPrivileged'], 'Accepted access privilege differs from architectural context'
            active['privilegeMetadata'] = True
        elif kind == 'ATOMIC':
            assert active and active['hart'] == hart and active['event'][0] == 'atomic' and not active.get('atomicMetadata')
            assert tuple(int(value, 16) for value in fields[1:]) == (active['operation'], int(active['eligible'])), 'Atomic request metadata differs from instruction/local LR pair'
            active['atomicMetadata'] = True
        elif kind == 'LOCAL_REQUEST':
            assert device is not None and active and active['hart'] == hart and not active['bus']
            event = fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            assert event == active['event'] and int(fields[5], 16) == active['tag'], 'Local request identity'
            assert device.base <= event[1] < device.base + 65536, 'Local request outside platform window'
            active.update(bus=True, local=True, response=service(hart, event, local=True))
        elif kind == 'LOCAL_RESPONSE':
            assert device is not None and active and active['hart'] == hart and active.get('local') and not active.get('localResponse')
            data, fault, tag = (int(value, 16) for value in fields[1:])
            assert (data, fault) == active['response'] and tag == active['tag'], 'Local response value or identity'
            active['localResponse'] = True
        elif kind == 'BUS':
            axi_transactions += 1
            event = fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            assert device is None or not device.base <= event[1] < device.base + 65536, 'Platform request escaped to AXI'
            if event[0] in ('exclusive_read', 'exclusive_write'):
                assert active and active['hart'] == hart and active['event'][0] == 'atomic'
                _, address, size, addend = active['event']
                assert event[1:3] == (address, size) and size == 8
                if event[0] == 'exclusive_read':
                    assert active['operation'] != 3 and active.get('phase') in (None, 'retry') and event[3] == 0
                    active.update(bus=True, phase='read')
                else:
                    if active['operation'] == 3:
                        assert active.get('phase') is None and active['eligible'] and event[3] == addend, 'SC without a matching local LR or incorrect operand'
                        active.update(bus=True, old=sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(size)))
                    else:
                        assert active['operation'] in (0, 1, 8) and active['phase'] == 'write' and event[3] == atomic_value(active['operation'], active['old'], addend, size)
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
                if response == 1:
                    monitor.reserve(hart, address, size)
                    reservation_max = max(reservation_max, len(monitor.reservations))
                    if active['operation'] == 2:
                        service(hart, active['event'])
                        active.update(response=(expected, 0), phase='complete')
                if response != 1:
                    service(hart, active['event'], atomic_fault=True)
                    active['response'] = (expected, 1)
                continue
            fault = address == program.faults.get(access)
            assert tuple(int(v, 16) for v in fields[1:]) == (address, 2 if fault else 0, expected)
            if access == 'read' and not active.get('walk'):
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
            monitor.write(address, 8)
            active['phase'] = 'interference'
        elif kind == 'WRITE':
            assert active and active['hart'] == hart and active['phase'] in ('response', 'interference')
            address, response = (int(v, 16) for v in fields[1:])
            assert address == active['event'][1]
            fault = address == program.faults.get('write')
            success = not fault and monitor.conditional(hart, address, active['event'][2])
            assert response == (2 if fault else 1 if success else 0), 'Exclusive response differs from independent endpoint monitor'
            active['phase'] = 'retry' if response == 0 and active['operation'] != 3 else 'complete'
            if active['operation'] == 3:
                active['scSuccess'] = success
                sc_results[hart, success] += int(not fault)
                service(hart, active['event'], atomic_fault=fault)
                active['response'] = (0 if success else 1, int(fault))
            elif response:
                service(hart, active['event'], atomic_fault=fault)
                active['response'] = (active['old'], int(fault))
        elif kind == 'RESPONSE':
            transactions += 1
            assert active and active['hart'] == hart, 'Response to the wrong hart'
            assert not config.get('enableUserMode') or active.get('privilegeMetadata'), 'Missing accepted access privilege'
            channel, data, fault, tag = (int(v, 16) for v in fields[1:])
            assert channel == int(active['event'][0] != 'fetch') and tag == active['tag']
            if not active['bus']:
                if not fault and active['event'][0] == 'atomic' and active['operation'] == 3 and not active['eligible']:
                    service(hart, active['event'])
                    assert data == 1, 'SC without local reservation must fail without bus traffic'
                    sc_results[hart, False] += 1
                else:
                    assert fault, 'Locally rejected request did not fault'
                if channel and fault:
                    assert pending[hart] is None
                    first = len(models[hart].requests)
                    pending[hart] = models[hart].step()
                    requests = [event for event in models[hart].requests[first:] if event[0] != 'fetch']
                    assert requests == [active['event']], 'Unexpected locally rejected request'
                    assert pending[hart][7]
                    if active['event'][0] == 'atomic':
                        assert (models[hart].atomic_operation, models[hart].sc_eligible) == (active['operation'], active['eligible'])
                        assert not atomic_metadata or active.get('atomicMetadata'), 'Missing rejected atomic metadata'
            else:
                expected_data, expected_fault = active['response']
                assert fault == expected_fault and (fault or data == expected_data), 'Response data or fault mismatch'
                assert not active.get('local') or active.get('localResponse'), 'Core response preceded local service'
            if observed_data and channel:
                access = implicit[hart] if active.get('walk') else architectural[hart]
                assert access and access.get('physical') and 'expected' not in access
                access['expected'] = active['response'] if active['bus'] else (1, 0) if not fault else (0, 1)
                (complete_walk if active.get('walk') else complete_data)(hart)
            active = None
        elif kind == 'IRQ':
            if device is None:
                models[hart].set_interrupts(int(fields[1], 16))
                if models[hart].csrs[0x304] & models[hart].csrs[0x344]:
                    waiting[hart] = False
            else:
                assert int(fields[1], 16) == sum((bool(models[hart].csrs[0x344] & (1 << bit)) << index)
                                               for index, bit in enumerate((3, 7, 11))), 'Retirement IRQ disagrees with cycle sample'
        elif kind == 'TRACE':
            assert not waiting[hart], 'Architectural event while waiting without a wakeup'
            observed = tuple(int(v, 16) for v in fields[1:])
            if translated and translation_maintenance(observed):
                translation_history[hart].clear()
                if walks[hart]:
                    walks[hart]['stale'] = True
            eligible, owned = models[hart].interrupt_cause(), pending[hart] is not None
            if pending[hart] is not None:
                assert active is None or active['hart'] != hart or active['event'][0] == 'fetch', 'Memory operation retired before its response'
                assert not observed_data or architectural[hart] is None, 'Memory operation retired before architectural response'
                wanted, pending[hart] = pending[hart], None
            elif observed[8] >> 63:
                wanted = models[hart].interrupt()
                interrupts[hart] += 1
                causes[hart, wanted[8] & 63] += 1
            else:
                first = len(models[hart].requests)
                wanted = models[hart].step()
                assert not observed_data or not any(event[0] != 'fetch' for event in models[hart].requests[first:]), 'Retirement omitted an architectural data request'
            if eligible and not wanted[7]:
                deferred[hart] += 1
                assert owned and deferred[hart] == 1, 'Interrupt deferred beyond its memory owner'
            else:
                deferred[hart] = 0
            fetch_checks[hart].send((line, fields))
            models[hart].requests.clear()
            models[hart].bus.clear()
            if hasattr(models[hart], 'request_privileges'):
                models[hart].request_privileges.clear()
            retired_privileges[hart] = getattr(models[hart], 'privilege', 3)
            assert observed == wanted, f'{name} hart {hart}:\nactual {observed}\nexpected {wanted}'
            wake[hart] = bool(models[hart].csrs[0x304] & models[hart].csrs[0x344])
            wake_mask = (wake_mask & ~(1 << hart)) | (int(wake[hart]) << hart)
            if wanted[7]:
                waiting[hart] = False
            elif wanted[2] == 0x10500073:
                waiting[hart] = config['enableInterrupts'] and not wake[hart]
                if waiting[hart]:
                    wait_started[hart] = device.cycle + 1 if device is not None else 0
            waiting_mask = (waiting_mask & ~(1 << hart)) | (int(waiting[hart]) << hart)
            events += 1
            if active is not None and active['hart'] != hart:
                concurrent['trapDuringPeerService'] += int(bool(wanted[7]))
                concurrent['redirectDuringPeerService'] += int(wanted[3] != wanted[1] + 4)
            if not wanted[7] and wanted[1] == program.stop:
                finished.add(hart)
    assert len(covers) == 1 and len(covers[0]) == 6 and (harts == 1 or all(covers[0])), 'Missing AXI scheduling coverage'
    if software_output:
        assert passed, 'Software simulation did not finish'
        assert results == [(hart, 1) for hart in range(harts)], 'Test memory did not contain per-hart success'
    if device is not None:
        for hart in range(harts):
            if waiting[hart]:
                sleep_cycles[hart] += device.cycle - wait_started[hart] + 1
    assert finished == set(range(harts)) and all(record is None for record in pending)
    assert active is None or active['event'][0] == 'fetch', 'Unretired data access at completion'
    assert all(access is None for access in architectural), 'Uncompleted architectural data access'
    assert failures == 0, 'Exclusive failure stimulus was not consumed'
    assert not atomic_metadata or observed_reservations == reservation_max, 'Exclusive monitor coverage differs from independent reservations'
    if harts > 1:
        assert sources == set(range(2 * harts)) and collisions, 'Missing source or cross-hart tag collision'
    expected_interrupts = (Counter({hart: 2 * program.platform['rounds'] for hart in range(harts)}) if hasattr(program, 'platform') else
                           Counter({program.interrupts.get('hart', 0): program.interrupts['mask'].bit_count()}) if hasattr(program, 'interrupts') else Counter())
    if software and software['kind'] == 'zephyr':
        assert all(causes[hart, 3] and causes[hart, 7] and not causes[hart, 11] for hart in range(harts)), 'Missing per-hart software/timer progress'
    elif software:
        expected_causes = Counter((hart, cause) for hart in range(harts) for cause in software['expectedInterruptCauses'])
        assert causes == expected_causes, f'Software interrupt causes: {causes} != {expected_causes}'
    else:
        assert interrupts == expected_interrupts, f'Interrupt isolation: {interrupts} != {expected_interrupts}'
    if hasattr(program, 'lrsc'):
        job = program.lrsc
        word = lambda address: sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8))
        witnesses = [[word(job['witnesses'] + hart * job['stride'] + 8 * round) for round in range(job['rounds'])] for hart in range(harts)]
        if job['shared']:
            assert word(job['counter']) == job['rounds'] * harts
            assert sorted(value for group in witnesses for value in group) == list(range(job['rounds'] * harts)), 'Lost or duplicate conditional store'
        else:
            assert all(word(job['counter'] + 8 * hart) == job['rounds'] and witnesses[hart] == list(range(job['rounds'])) for hart in range(harts)), 'Private LR/SC result mismatch'
            assert reservation_max >= min(harts, 2), 'Independent exclusive IDs were not simultaneously live'
        assert all(sc_results[hart, True] == job['rounds'] for hart in range(harts)), 'Missing per-hart successful SC'
    elif harts > 1 and 'atomic' in name:
        word = lambda address: sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8))
        assert word(base + 0x1800) == 4 * harts + 14, 'Lost or duplicate atomic update'
        old = [word(base + 0x2000 + hart * 64 + i * 8) for hart in range(harts) for i in range(4)]
        assert sorted(old) == list(range(14, 14 + 4 * harts)), 'Atomic old-value uniqueness'
    for hart, model in enumerate(models):
        if software:
            word = lambda address: sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8))
            assert word(software['results'] + 8 * hart) == 1 and successful_stores[hart] == 1, 'Software did not publish success exactly once'
            assert console[hart].decode('ascii') == software['expectedConsole'][hart], 'Missing or incorrect per-hart software console'
        elif hasattr(program, 'platform'):
            rounds, tasks = program.platform['rounds'], program.platform['rounds'] * harts
            word = lambda address: sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8))
            assert model.registers[23:25] == [rounds, rounds], 'Missing per-hart software or timer interrupt'
            assert causes[hart, 3] == rounds and causes[hart, 7] == rounds, 'Wrong platform interrupt causes'
            assert word(base + 0x1810) == tasks and model.registers[19] == tasks * (tasks + 1) // 2, 'Distributed task checksum'
            assert [word(base + 0x2400 + 8 * ticket) for ticket in range(tasks)] == list(range(1, tasks + 1)), 'Lost platform work'
            assert all(sum(effects[h, base + 0x2400 + 8 * ticket] for h in range(harts)) == 1 for ticket in range(tasks)), 'Repeated platform work'
            assert device.software[hart] == 0 and device.compare[hart] == MASK, 'Interrupt sources left asserted'
            assert not program.platform.get('wait') or sleep_cycles[hart] >= program.platform['rounds'], 'Missing real per-hart wait cycles'
        elif hasattr(program, 'synchronization'):
            word = lambda address: sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8))
            tasks = program.synchronization['rounds'] * harts
            assert word(base + 0x1810) == tasks, 'Work allocation count'
            assert [word(base + 0x2000 + 8 * ticket) for ticket in range(tasks)] == list(range(1, tasks + 1)), 'Lost or duplicate work'
            assert all(sum(effects[h, base + 0x2000 + 8 * ticket] for h in range(harts)) == 1 for ticket in range(tasks)), 'Repeated task execution'
            assert effects[hart, base + 0x1810] == program.synchronization['rounds'], 'Hart did not execute every work round'
            assert all(word(base + offset) == harts for offset in (0x1800, 0x1818, 0x1820, 0x1828, 0x1830)), 'Incomplete repeated barrier'
            assert word(base + 0x2400 + 64 * hart) == 3 and word(base + 0x2408 + 64 * hart) == 9, 'Instruction publication did not replace warmed code'
            assert model.registers[19] == tasks * (tasks + 1) // 2, 'Distributed work checksum'
        elif harts > 1 and 'atomic' in name and not hasattr(program, 'lrsc'):
            assert model.registers[18] == harts * (harts + 1) // 2, 'Release/acquire publication'
        elif harts > 1 and not hasattr(program, 'lrsc') and not hasattr(program, 'data_cache') and not name.startswith('user_'):
            assert model.registers[8] == (hart + 1) % harts + 1, 'Mailbox exchange did not complete'
            assert model.registers[12] == 1 and effects[hart, base + 0x5100] == 1, 'Private data or device effect'
            assert model.registers[17] == hart and (name == 'interrupt' or model.registers[19] == hart), 'Hart identity or read-only CSR'
        if name == 'protection':
            assert effects[hart, base + 0x1800] == int(hart != 0), 'PMP isolation'
        try:
            fetch_checks[hart].send(None)
        except StopIteration:
            pass
    if data_cache:
        assert all(count['accepted'] == count['completed'] and count['reads'] == count['hits'] + count['physicalReads'] + count['rejectedReads'] for count in cache_counts), 'Cached read accounting differs from architectural requests'
    if data_cache and hasattr(program, 'data_cache'):
        job = program.data_cache
        for hart, count in enumerate(cache_counts):
            addresses = job.get('addresses', ())
            count['witnessHits'] = sum(hit_addresses[hart][address] for address in addresses) if addresses else count['hits']
            assert count['witnessHits'] >= job['minHits'] and all(hit_addresses[hart][address] for address in addresses), 'Missing target-address private-cache hits'
        for hart, registers in enumerate(job.get('finalRegisters', [job.get('expectedRegisters', {})] * harts)):
            assert all(models[hart].registers[int(register)] == value for register, value in registers.items()), 'Cache program register result'
        if 'witnesses' in job:
            assert all(sum(memory.get(job['witnesses'] + hart * job['stride'] + 8 * index + byte, 0) << (8 * byte) for byte in range(8)) == value
                       for hart in range(harts) for index, value in enumerate(job['values'])), 'Coherence publication witness'
    assert not console_events, 'Console service was not printed'
    return dict(**(dict(results=results) if software_output else {}), **(dict(dataCache=[dict(count) for count in cache_counts]) if data_cache else {}), **(dict(translation=dict(translation_counts)) if translated else {}), events=events, activeHarts=len(finished), sources=sorted(sources),
                cycles=elapsed_cycles, transactions=transactions, axiTransactions=axi_transactions,
                collidingTags=len(collisions), readsBeforePeerRetirement=overtaken, concurrency=dict(concurrent),
                platformCycles=device.cycle + 1 if device is not None else 0,
                sleepCycles=sleep_cycles,
                exclusiveReservations=reservation_max,
                conditionalStores={str(hart): dict(success=sc_results[hart, True], failure=sc_results[hart, False]) for hart in range(harts)},
                interrupts={str(hart): {str(bit): causes[hart, bit] for bit in (1, 3, 5, 7, 9, 11)} for hart in range(harts)},
                console=[text.decode('ascii') for text in console] if software else [],
                busCoverage=dict(zip(('awBeforeW', 'wBeforeAw', 'awWithW', 'arStall', 'awStall', 'wStall'), covers[0])))


def compare_multicore(binary, directory, config, selected=(), platform=False):
    harts, base = config['hartCount'], int(config['resetVector'])
    reports = []
    programs = ((name, platform_program(base, harts, local_interrupt_base(config), wait=name == 'platform_wait'))
                for name in ('platform', 'platform_wait')) if platform else multicore_cases(
        base, harts, bool(config['pmpEntries']), config['enableInterrupts'], config.get('enableUserMode', False))
    if platform and config.get('enableUserMode'):
        programs = chain(programs,
            ((name, program) for name, program in multicore_cases(base, harts, bool(config['pmpEntries']), config['enableInterrupts'], True) if name == 'user_isolation'),
            ((name, program) for name, program in cases(base, bool(config['pmpEntries']), config['enableInterrupts'], True, local_interrupt_base(config)) if name == 'user_device'))
    for name, program in programs:
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
            reports.append(dict(test=name, seed=seed, **check_multicore(lines, config, program, name, atomic_metadata=True)))
        if harts > 1 and 'atomic' not in name and not hasattr(program, 'synchronization') and not hasattr(program, 'data_cache') and not platform and not name.startswith('user_'):
            concurrent = Counter()
            for report in reports[first:]:
                concurrent.update(report['concurrency'])
            assert concurrent['trapDuringPeerService'] and concurrent['redirectDuringPeerService'], f'{name}: missing concurrent trap or redirect {dict(concurrent)}'
        print(f'  {harts} harts, {name}: three shared-memory schedules', flush=True)
    assert reports, 'No selected multicore program'
    return dict(events=sum(report['events'] for report in reports), cases=reports)


def check_data_oracle():
    config = dict(configuration(64), hartCount=2, enableInterrupts=False, dCacheBytes=8192)
    config['memoryRegions'][0]['dataCacheable'] = True
    instructions = (0x10000093, 0x0000b103, 0x0000b183, 0x00000013)
    memory = {4 * index + byte: (word >> (8 * byte)) & 255 for index, word in enumerate(instructions) for byte in range(4)}
    memory[0x100] = 42
    program = SimpleNamespace(memory=memory, faults={}, stop=12,
                              data_cache=dict(minHits=1, addresses=[0x100], expectedRegisters={'2': 42, '3': 42}))
    models = [Model(config, memory, {}) for _ in range(2)]
    lines = []

    def emit(hart, event):
        lines.append(f'HART {hart} {event}')

    def fetch(hart, index, complete=True):
        address, word = index * 4, instructions[index]
        emit(hart, f'REQUEST fetch {address:x} 4 0 {index:x}')
        emit(hart, 'ACCESS_PRIVILEGE 1')
        emit(hart, f'BUS fetch {address:x} 4 0')
        if complete:
            fetch_response(hart, index)

    def fetch_response(hart, index):
        address, word = index * 4, instructions[index]
        emit(hart, f'READ {address:x} 0 {word:x}')
        emit(hart, f'FETCH {address:x} 0 {word:x}')
        emit(hart, f'RESPONSE 0 {word:x} 0 {index:x}')

    def trace(hart):
        emit(hart, 'TRACE ' + ' '.join(f'{field:x}' for field in models[hart].step()))

    for hart in range(2):
        fetch(hart, 0)
        trace(hart)
        fetch(hart, 1)
        emit(hart, 'ARCH_DATA_REQUEST read 100 8 0 1 1')
        emit(hart, 'REQUEST read 100 8 0 1')
        emit(hart, 'ACCESS_PRIVILEGE 1')
        emit(hart, 'BUS read 100 8 0')
        emit(hart, 'READ 100 0 2a')
        emit(hart, 'RESPONSE 1 2a 0 1')
        emit(hart, 'ARCH_DATA_RESPONSE 2a 0 1')
        trace(hart)
        fetch(hart, 2)
        emit(hart, 'ARCH_DATA_REQUEST read 100 8 0 2 1')
    fetch(1, 3, complete=False)
    for hart in range(2):
        emit(hart, 'CACHE_SAMPLE 100 2a 2')
        emit(hart, 'ARCH_DATA_RESPONSE 2a 0 2')
        trace(hart)
    fetch_response(1, 3)
    fetch(0, 3)
    trace(0)
    trace(1)
    lines += ['COVER 1 1 1 1 1 1', 'EXCLUSIVE 0', 'PASS']
    report = check_multicore(lines, config, program, 'data_oracle', atomic_metadata=True)
    assert report['dataCache'][0]['hitsDuringPeerService'] == 1
    sample = lines.index('HART 0 CACHE_SAMPLE 100 2a 2')
    request = lines.index('HART 0 ARCH_DATA_REQUEST read 100 8 0 2 1')
    response = sample + 1
    mutations = dict(
        staleSample=(sample, ['HART 0 CACHE_SAMPLE 100 29 2']),
        sampleTag=(sample, ['HART 0 CACHE_SAMPLE 100 2a 3']),
        duplicateSample=(sample, [lines[sample], lines[sample]]),
        missingRequest=(request, []),
        missingSample=(sample, []),
        wrongResponse=(response, ['HART 0 ARCH_DATA_RESPONSE 29 0 2']),
        missingResponse=(response, []),
        responseTag=(response, ['HART 0 ARCH_DATA_RESPONSE 2a 0 3']))
    for name, (index, replacement) in mutations.items():
        try:
            check_multicore([*lines[:index], *replacement, *lines[index + 1:]], config, program, 'data_oracle', atomic_metadata=True)
        except AssertionError:
            continue
        raise AssertionError(f'Data oracle accepted {name}')
    program.data_cache['addresses'] = [0x108]
    try:
        check_multicore(lines, config, program, 'data_oracle', atomic_metadata=True)
    except AssertionError:
        return [*mutations, 'missingTargetHit']
    raise AssertionError('Data oracle credited unrelated cache hits')


def load_software(image, config_path):
    from elftools.elf.elffile import ELFFile

    document = json.loads(config_path.read_text())
    config = document.get('parameters', document)
    for region in config['memoryRegions']:
        region.setdefault('dataCacheable', False)
    manifest = json.loads(image.with_name('manifest.json').read_text())
    assert hashlib.sha256(config_path.read_bytes()).hexdigest() == manifest['configurationHash'], 'Software configuration changed'
    assert hashlib.sha256(image.read_bytes()).hexdigest() == manifest['imageHash'], 'Software image changed'
    assert all(hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest for name, digest in manifest['sourceHashes'].items()), 'Stale software sources'
    base, harts, memory, spans, payloads = int(config['resetVector']), config['hartCount'], {}, [], []
    ram = next(r for r in config['memoryRegions'] if int(r['base']) == base and r['readable'] and r['writable'] and r['executable'] and not r['device'])
    memory_bytes = max(65536, int(ram['size']))
    assert memory_bytes <= 524288, 'Software RAM exceeds supported test profile'
    layout, code = manifest.get('layout', {}), []
    kind = layout.get('kind', 'runtime')
    assert kind in ('runtime', 'arch-test', 'zephyr'), 'Unknown software layout'
    with image.open('rb') as stream:
        elf = ELFFile(stream)
        assert elf.elfclass == 64 and elf.little_endian and elf['e_machine'] == 'EM_RISCV' and elf['e_type'] == 'ET_EXEC', 'Unsupported executable format'
        assert not elf['e_flags'] & 6 and (kind == 'arch-test' or not elf['e_flags'] & 1), 'Unsupported compressed or floating-point ABI'
        table = elf.get_section_by_name('.symtab')
        assert table is not None, 'Software symbols are missing'
        all_symbols = {symbol.name: symbol for symbol in table.iter_symbols() if symbol['st_shndx'] != 'SHN_UNDEF'}
        symbols = {name: symbol['st_value'] for name, symbol in all_symbols.items() if symbol['st_info']['bind'] in ('STB_GLOBAL', 'STB_WEAK')}
        assert symbols == manifest['symbols'], 'Software symbols changed'
        entry, alias = layout.get('entrySymbol', '_start'), layout.get('entryAlias', '_start')
        assert symbols[entry] == symbols[alias] == elf['e_entry'] == base, 'Invalid software entry'
        for segment in elf.iter_segments():
            if segment['p_type'] != 'PT_LOAD':
                continue
            address, size, files, flags = (segment[key] for key in ('p_paddr', 'p_memsz', 'p_filesz', 'p_flags'))
            assert segment['p_vaddr'] == address and files <= size and segment['p_offset'] + files <= image.stat().st_size, 'Invalid load segment'
            assert base <= address <= address + size <= base + memory_bytes, 'Load segment exceeds test memory'
            assert any(not r['device'] and int(r['base']) <= address and address + size <= int(r['base']) + int(r['size'])
                       and (not flags & 4 or r['readable']) and (not flags & 2 or r['writable']) and (not flags & 1 or r['executable'])
                       for r in config['memoryRegions']), 'Load segment violates memory attributes'
            assert all(address + size <= low or high <= address for low, high, _ in spans), 'Overlapping load segments'
            payload = segment.data()
            assert len(payload) == files, 'Truncated load segment'
            memory.update((address + offset, payload[offset] if offset < files else 0) for offset in range(size))
            spans.append((address, address + size, flags))
            payloads.append((address, address + files))
        if kind in ('arch-test', 'zephyr'):
            spec = importlib.util.spec_from_file_location('architecture_image', 'scripts/build_arch_tests.py')
            builder = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(builder)
            integer = 'rv64i2p1_zicsr2p0_zifencei2p0'
            architecture = 'rv64i2p1_a2p1_zicsr2p0_zifencei2p0_zaamo1p0_zalrsc1p0' if kind == 'zephyr' else integer
            code = builder.code_spans(elf, architecture, (integer,) if kind == 'zephyr' else ())
            if kind == 'arch-test':
                assert code == manifest['codeSpans'] and hashlib.sha256(table.data()).hexdigest() == manifest['symbolTableHash'], 'Executable mappings changed'
            implemented_csrs = Model(config, {}, {}).csrs
            for span in code:
                section = elf.get_section_by_name(span['section'])
                data = section.data()
                for address in range(span['start'], span['end'], 4):
                    word = int.from_bytes(data[address - section['sh_addr']:address - section['sh_addr'] + 4], 'little')
                    opcode, funct3, funct7 = word & 127, (word >> 12) & 7, word >> 25
                    assert opcode in (3, 15, 19, 23, 27, 35, 47, 51, 55, 59, 99, 103, 111, 115), 'Unsupported software instruction family'
                    assert not (opcode in (51, 59) and funct7 == 1), 'Software requires multiplication or division'
                    if opcode in (19, 27, 51, 59):
                        try:
                            integer_value(word, 0, 0)
                        except Fault as error:
                            raise AssertionError('Unsupported software integer encoding') from error
                    elif opcode in (3, 15, 35, 99, 103):
                        assert funct3 in {3: range(7), 15: (0, 1), 35: range(4), 99: (0, 1, 4, 5, 6, 7), 103: (0,)}[opcode], 'Unsupported software memory/control encoding'
                    elif opcode == 47:
                        assert kind == 'zephyr' and funct3 == 3 and word >> 27 in (0, 1, 2, 3, 8) and (word >> 27 != 2 or (word >> 20) & 31 == 0), 'Unsupported software atomic instruction'
                    elif opcode == 115:
                        update = funct3 & 3 == 1 or (word >> 15) & 31 != 0
                        assert word in (0x73, 0x30200073, 0x10500073) or (funct3 in (1, 2, 3, 5, 6, 7) and word >> 20 in implemented_csrs and (not update or word >> 30 != 3)), 'Unsupported software system instruction'
        if kind == 'zephyr':
            stacks = layout['stacks']
            actual = {name for name, symbol in all_symbols.items() if symbol['st_size'] and name.endswith(('_stack', '_stacks'))
                      and isinstance(symbol['st_shndx'], int) and elf.get_section(symbol['st_shndx'])['sh_flags'] & 3 == 3
                      and not elf.get_section(symbol['st_shndx'])['sh_flags'] & 4}
            assert {stack['symbol'] for stack in stacks} == actual, 'Missing or unrelated stack objects'
            for stack in stacks:
                symbol = all_symbols[stack['symbol']]
                count = harts if stack['symbol'].endswith('_stacks') else 1
                assert stack == dict(symbol=stack['symbol'], address=symbol['st_value'], size=symbol['st_size'], count=count, stride=symbol['st_size'] // count), 'Stack object layout changed'
                assert stack['size'] % count == 0
            assert all_symbols['__test_results']['st_size'] == 8 * harts, 'Result array has the wrong hart count'
        else:
            assert symbols['__hart_count'] == harts and symbols['__stack_top'] - symbols['__stack_bottom'] == harts * symbols['__stack_bytes']
            stacks = [dict(symbol='__stack_bottom', address=symbols['__stack_bottom'], size=harts * symbols['__stack_bytes'], count=harts, stride=symbols['__stack_bytes'])]
            assert base == symbols['__ram_base'] and symbols['__stack_top'] <= base + symbols['__ram_bytes'] <= base + memory_bytes
            if kind == 'arch-test':
                assert harts == 1 and stacks == layout['stacks'], 'Architecture test stack layout changed'
                low, high = symbols['__stack_bottom'], symbols['__stack_top']
                assert all(high <= start or end <= low for start, end in payloads), 'Loaded bytes overlap reserved stack'
                assert all(high <= span['start'] or span['end'] <= low for span in code), 'Code overlaps reserved stack'
    assert any(low <= base < high and flags & 1 for low, high, flags in spans), 'Entry is not executable'
    assert symbols['__test_halt'] % 4 == 0 and any(low <= symbols['__test_halt'] < high and flags & 1 for low, high, flags in spans)
    bss = symbols['__bss_start'], symbols['__bss_end']
    assert base <= bss[0] <= symbols['__test_results'] <= symbols['__test_results'] + 8 * harts <= bss[1] <= base + memory_bytes
    assert symbols['__test_results'] % 8 == 0 and all(memory.get(address) == 0 for address in range(*bss)), 'ELF BSS was not zero-filled'
    assert not layout or (layout['bssStart'], layout['bssEnd']) == bss
    ranges = []
    for stack in stacks:
        low, high = stack['address'], stack['address'] + stack['size']
        assert stack['size'] > 0 and low % 16 == 0 and high % 16 == 0 and bss[1] <= low < high <= base + memory_bytes
        if kind == 'zephyr':
            assert any(start <= low and high <= end and flags & 2 for start, end, flags in spans), 'Stack has no writable load allocation'
        assert any(not r['device'] and r['readable'] and r['writable'] and int(r['base']) <= low < high <= int(r['base']) + int(r['size']) for r in config['memoryRegions']), 'Stacks exceed writable RAM'
        assert all(high <= start or end <= low for start, end in ranges), 'Stack objects overlap'
        ranges.append((low, high))
    output = manifest.get('console', dict(transport='word', base=symbols.get('__console_base')))
    console = output['base']
    assert output['transport'] == 'word' and isinstance(console, int) and console % 4 == 0, 'Unsupported console transport'
    assert any(r['device'] and r['writable'] and not r['executable'] and not r['atomic'] and int(r['base']) <= console and
               console + 4 * harts <= int(r['base']) + int(r['size']) for r in config['memoryRegions']), 'Console mapping is invalid'
    expected = manifest.get('expectedConsole', [f'hart {hart:x} online\n' for hart in range(harts)])
    assert len(expected) == harts and all(text and text.endswith('\n') and text.isascii() for text in expected), 'Invalid expected console bytes'
    interrupt_causes = manifest.get('expectedInterruptCauses', [])
    assert isinstance(interrupt_causes, list) and all(type(cause) is int and 0 <= cause < 64 for cause in interrupt_causes), 'Invalid expected software interrupt causes'
    frequency = manifest.get('timebaseHz', 100000000)
    assert 0 < frequency <= 100000000 and 100000000 % frequency == 0, 'Unsupported software timebase'
    if kind == 'zephyr':
        assert frequency == 10000000 and local_interrupt_base(config) is not None and config['enableInterrupts']
        assert all(hashlib.sha256(image.with_name(name).read_bytes()).hexdigest() == digest for name, digest in manifest['generatedHashes'].items()), 'Generated software configuration changed'
    return config, SimpleNamespace(memory=memory, faults={}, stop=symbols['__test_halt'],
        software=dict(kind=kind, console=console, results=symbols['__test_results'], bss=bss, expectedConsole=expected, expectedInterruptCauses=interrupt_causes,
                      memoryBytes=memory_bytes, timebaseHz=frequency, timeTickCycles=100000000 // frequency,
                      idleCycles=4 * 100000000 // 100 if kind == 'zephyr' else 0)), manifest


def test_source_hashes():
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for name in
            ('verify.py', 'contracts.py', 'model.py', 'programs.py', 'core_tb.sv', 'memory_tb.sv')
            for p in (Path('test') / name,)}


def check_software_output(lines, config, program, console):
    report = check_multicore(lines, config, program, 'software', atomic_metadata=True, software_output=True)
    assert Counter(console.read_text().splitlines()) == Counter(f'[hart {hart}] {line}' for hart, text in enumerate(program.software['expectedConsole']) for line in text.splitlines()), 'Console log differs from software bytes'
    return report


def check_translation_guards(lines, config, program):
    cached_response, paged, walked, cancelled, port = None, False, False, False, 0
    for index, line in enumerate(lines):
        fields = line.split()
        if not fields:
            continue
        if fields[0] == 'HART':
            fields = fields[2:]
        if fields[0] == 'TRANSLATE_REQUEST':
            paged, walked = int(fields[3], 16) != 3 and int(fields[6], 16) >> 60 == 8, False
            cancelled, port = False, int(fields[1])
        elif fields[0] == 'WALK_REQUEST':
            walked = True
        elif fields[0] == 'ARCH_CANCEL' and port == 0:
            cancelled = True
        elif fields[0] == 'TRANSLATE_RESPONSE' and paged and not walked and not cancelled and not int(fields[3], 16):
            cached_response = index
            break
    mutations = (('contextPrivilege', 'TRANSLATE_REQUEST', 3, 1),
                 ('contextRoot', 'TRANSLATE_REQUEST', 6, 1),
                 ('physicalResult', 'TRANSLATE_RESPONSE', 2, 0x1000),
                 ('pteAddress', 'WALK_REQUEST', 1, 8),
                 ('pteData', 'WALK_RESPONSE', 1, 1),
                 ('lsuAddress', 'ARCH_DATA_REQUEST', 2, 8))
    if config.get('tlbEntries'):
        assert cached_response is not None, 'Translation cache was not exercised'
        mutations += (('cachedResult', 'TRANSLATE_RESPONSE', 2, 8),)
    for name, event, field, mask in mutations:
        changed = list(lines)
        index = cached_response if name == 'cachedResult' else next(i for i, line in enumerate(lines) if line.split()[2 if line.startswith('HART ') else 0] == event)
        fields = changed[index].split()
        field += 2 if fields[0] == 'HART' else 0
        fields[field] = f'{int(fields[field], 16) ^ mask:x}'
        changed[index] = ' '.join(fields)
        try:
            check_multicore(changed, config, program, 'software', atomic_metadata=True, software_output=True)
        except AssertionError:
            continue
        raise AssertionError(f'Translation oracle accepted {name}')
    guards = [item[0] for item in mutations]
    if config.get('tlbEntries'):
        fields = next(line.split()[2:] if line.startswith('HART ') else line.split() for line in lines
                      if 'TRANSLATE_REQUEST' in line and int(line.split()[-3], 16) >> 60 == 8 and int(line.split()[-6], 16) != 3)
        context = dict(port=int(fields[1]), address=int(fields[2], 16), privilege=int(fields[3], 16),
                       kind='fetch' if int(fields[4]) else 'write' if int(fields[5]) else 'read',
                       satp=int(fields[6], 16), status=(int(fields[7]) << 18) | (int(fields[8]) << 19), reads=[])
        permitted = dict(config, pmpEntries=0)
        try:
            check_translation_result(context, (context['address'], False, 0), permitted, Model(permitted, {}, {}), [])
        except AssertionError:
            guards.append('fabricatedHit')
        else:
            raise AssertionError('Translation oracle accepted an unfilled cache hit')
    return guards


def software_schedule(task):
    binary, image, output, config, program, seed, transaction_limit, cycle_limit, timeout = task
    console, log = output / f'console-{seed}.log', output / f'software-{seed}.log'
    run([binary, f'+IMAGE={image.resolve()}', f'+BASE={int(config["resetVector"]):x}', f'+STOP={program.stop:x}', f'+SEED={seed}',
         f'+CONSOLE_BASE={program.software["console"]:x}', f'+CONSOLE_LOG={console.resolve()}',
         f'+RESULTS={program.software["results"]:x}', f'+TRANSACTIONS={transaction_limit}', f'+CYCLE_LIMIT={cycle_limit}'], log, timeout=timeout)
    return dict(seed=seed, consoleLog=str(console), **check_software_output(log, config, program, console))


def verify_software(args):
    args.output.mkdir(parents=True, exist_ok=True)
    summary_path = args.output / 'summary.json'
    summary_path.unlink(missing_ok=True)
    config, program, software = load_software(args.elf, args.config)
    software_manifest_hash = hashlib.sha256(args.elf.with_name('manifest.json').read_bytes()).hexdigest()
    if args.poison_bss:
        program.memory.update((address, 0xa5) for address in range(*program.software['bss']))
    test_hashes = test_source_hashes()
    config_path, rtl = args.output / 'input.json', args.output / 'rtl'
    config_path.write_text(json.dumps(config, indent=2) + '\n')
    if not args.use_generated:
        run(['build-ditdah-a1', '--trace', '--config', config_path, '--output', rtl], args.output / 'build.log')
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    assert manifest['top'] == 'DitDahA1' and manifest['validationScope'] == 'system'
    assert all(manifest['parameters'][key] == value for key, value in config.items() if key != 'enableTrace'), 'Stale software RTL configuration'
    assert all(hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest for name, digest in manifest['sourceHashes'].items()), 'Stale software RTL sources'
    profile = program.software
    if profile['kind'] != 'runtime':
        assert args.software_transactions is not None, 'Set a measured or bounded --software-transactions probe budget'
    transaction_limit = args.software_transactions or 640 * config['hartCount']
    software_timeout = args.software_timeout or 600
    assert transaction_limit > 0
    cycle_limit = transaction_limit * 128 + profile['idleCycles'] if args.software_transactions else (50000 if config['hartCount'] == 1 else transaction_limit * 128)
    assert cycle_limit < 1 << 31, 'Software budget exceeds simulator counter width'
    binary = compile_tb(rtl, args.output, config['axiDataBits'], config['physicalAddressBits'], software=profile)
    base, harts = int(config['resetVector']), config['hartCount']
    image = args.output / 'software.hex'
    image.write_text('\n'.join(f'{program.memory.get(base + i, 0):02x}' for i in range(profile['memoryBytes'])) + '\n')
    tasks = [(binary, image, args.output, manifest['parameters'], program, seed, transaction_limit, cycle_limit, software_timeout)
             for seed in args.seeds]
    with ProcessPoolExecutor(max_workers=min(args.jobs, len(tasks))) as executor:
        reports = list(executor.map(software_schedule, tasks))
    guards = (check_translation_guards((args.output / f'software-{args.seeds[0]}.log').read_text().splitlines(), manifest['parameters'], program)
              if config.get('virtualAddressBits') == 39 and config['hartCount'] == 1 and not config['dCacheBytes'] else [])
    hashes = {**manifest['sourceHashes'], **test_hashes, **software['sourceHashes']}
    assert all(hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest for name, digest in hashes.items()), 'Sources changed during software verification'
    assert hashlib.sha256(args.elf.read_bytes()).hexdigest() == software['imageHash'], 'Image changed during software verification'
    assert hashlib.sha256(args.config.read_bytes()).hexdigest() == software['configurationHash'], 'Configuration changed during software verification'
    assert hashlib.sha256(args.elf.with_name('manifest.json').read_bytes()).hexdigest() == software_manifest_hash, 'Software manifest changed during verification'
    summary_path.write_text(json.dumps(dict(scope='implemented scalar software execution and console', sourceHashes=hashes,
        software=software, poisonBss=args.poison_bss, zeroLoadedBssBytes=program.software['bss'][1] - program.software['bss'][0],
        hartCount=harts, axiDataBits=config['axiDataBits'], clockHz=100000000, timebaseHz=profile['timebaseHz'],
        cyclesPerTimeTick=profile['timeTickCycles'], transactionLimit=transaction_limit, cycleLimit=cycle_limit,
        idleCycles=profile['idleCycles'], wallSecondsPerSchedule=software_timeout, translationOracleGuards=guards, cases=reports), indent=2) + '\n')
    print(f'{harts}-hart ELF software and console passed {len(reports)} bus schedules', flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--width', type=int, choices=(64, 128, 256, 512), action='append')
    parser.add_argument('--use-generated', action='store_true')
    parser.add_argument('--elf', type=Path)
    parser.add_argument('--config', type=Path)
    parser.add_argument('--poison-bss', action='store_true')
    parser.add_argument('--software-transactions', type=int)
    parser.add_argument('--software-timeout', type=int)
    parser.add_argument('--seeds', type=int, nargs='+', default=(1, 17, 2026))
    parser.add_argument('--jobs', type=int, choices=range(1, 17), default=1)
    parser.add_argument('--user-mode', action='store_true')
    parser.add_argument('--supervisor-mode', action='store_true')
    parser.add_argument('--sv39', action='store_true')
    parser.add_argument('--tlb-entries', type=int, choices=(0, 2, 4), default=0)
    parser.add_argument('--multicore-only', action='store_true')
    parser.add_argument('--platform-only', action='store_true')
    parser.add_argument('--harts', type=int, choices=(1, 2, 3, 16), action='append')
    parser.add_argument('--output', type=Path, default=Path('result/verify'))
    parser.add_argument('--interrupts', action='store_true', help='Run only enabled interrupt profiles')
    parser.add_argument('--pmp-entries', type=int, choices=(0, 16))
    parser.add_argument('--icache-bytes', type=int, choices=(0, 8192, 16384, 32768, 65536), default=0)
    parser.add_argument('--dcache-bytes', type=int, choices=(0, 8192), default=0)
    parser.add_argument('--case', dest='selected', action='append', default=[])
    parser.add_argument('--traffic-baseline', type=Path)
    args = parser.parse_args()
    if args.tlb_entries and not args.sv39:
        parser.error('--tlb-entries requires --sv39')
    if args.sv39:
        args.supervisor_mode = True
    if args.supervisor_mode:
        args.user_mode = args.interrupts = True
    if len(set(args.seeds)) != len(args.seeds) or any(not 0 < seed < 1 << 32 for seed in args.seeds):
        parser.error('--seeds requires distinct nonzero 32-bit integers')
    if not args.elf and (args.jobs != 1 or tuple(args.seeds) != (1, 17, 2026)):
        parser.error('--seeds and --jobs require --elf')
    if args.software_timeout is not None and (args.elf is None or args.software_timeout <= 0):
        parser.error('--software-timeout requires --elf and a positive integer')
    assert bool(args.elf) == bool(args.config), 'ELF execution requires its configuration'
    assert not args.poison_bss or args.elf, 'BSS poisoning requires an ELF image'
    if args.elf:
        verify_software(args)
        return
    assert not (args.multicore_only and args.platform_only), 'Select one shared-memory profile family'
    args.output.mkdir(parents=True, exist_ok=True)
    summary_path = args.output / 'summary.json'
    summary_path.unlink(missing_ok=True)
    test_hashes = test_source_hashes()
    summary = {'scope': 'implemented scalar subset; simulation and assertions', 'selectedCases': args.selected,
               'fetchOracleGuards': check_fetch_oracle(), 'dataOracleGuards': check_data_oracle(), 'configurations': []}
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
    if args.interrupts or args.multicore_only or args.platform_only:
        profiles = []
    profiles += [(width, entries, True) for width, entries in (() if args.multicore_only or args.platform_only else ((64, 0), (512, 16)))
                 if (not args.width or width in args.width) and (args.pmp_entries is None or entries == args.pmp_entries)]
    if args.supervisor_mode and not (args.multicore_only or args.platform_only):
        profiles = [(width, args.pmp_entries if args.pmp_entries is not None else 16, True)
                    for width in args.width or (64, 512)]
    assert profiles or args.multicore_only or args.platform_only, 'No configurations match the requested profile'
    for width, entries, interrupts in profiles:
        directory = args.output / f'{"irq-" if interrupts else ""}{"pmp16-" if entries else ""}axi{width}'
        directory.mkdir(parents=True, exist_ok=True)
        config = configuration(width)
        config.update(pmpEntries=entries, enableInterrupts=interrupts, iCacheBytes=args.icache_bytes, dCacheBytes=args.dcache_bytes, tlbEntries=args.tlb_entries)
        config['memoryRegions'][0]['dataCacheable'] = bool(args.dcache_bytes)
        if args.user_mode:
            config['enableUserMode'] = True
        if args.supervisor_mode:
            config['enableSupervisorMode'] = True
        if args.sv39:
            config['virtualAddressBits'] = 39
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
        report.update(axiDataBits=width, physicalAddressBits=config['physicalAddressBits'], pmpEntries=entries, enableInterrupts=interrupts, iCacheBytes=args.icache_bytes, dCacheBytes=args.dcache_bytes)
        summary['configurations'].append(report)
        core = directory / 'core'
        core_config = dict(config, axiDataBits=256, dCacheBytes=0)
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
    if args.multicore_only or args.platform_only:
        shared_profiles = ((1, 64, 0, True), (2, 64, 0, True), (3, 128, 16, True), (16, 512, 16, True)) if args.platform_only else (
            (2, 64, 0, False), (2, 512, 16, True), (3, 64, 16, True), (16, 512, 16, True))
        for harts, width, entries, interrupts in shared_profiles:
            if (args.harts and harts not in args.harts) or (args.width and width not in args.width):
                continue
            if args.pmp_entries is not None and entries != args.pmp_entries:
                continue
            directory = args.output / f'harts{harts}-axi{width}'
            directory.mkdir(parents=True, exist_ok=True)
            config = dict(configuration(width), hartCount=harts, pmpEntries=entries, enableInterrupts=interrupts, iCacheBytes=args.icache_bytes, dCacheBytes=args.dcache_bytes, tlbEntries=args.tlb_entries)
            config['memoryRegions'][0]['dataCacheable'] = bool(args.dcache_bytes)
            if args.user_mode:
                config['enableUserMode'] = True
            if args.supervisor_mode:
                config.update(enableSupervisorMode=True, enableInterrupts=True)
            if args.sv39:
                config['virtualAddressBits'] = 39
            if args.platform_only:
                local_base = int(config['resetVector']) + 0x10000
                config.update(localInterruptBase=str(local_base))
                config['memoryRegions'].append(dict(base=str(local_base), size=str(65536), readable=True,
                                                    writable=True, executable=False, device=True, atomic=False, dataCacheable=False))
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
            report = compare_multicore(binary, directory, manifest['parameters'], args.selected, args.platform_only)
            report['interfaceContracts'] = verify_contracts(
                rtl, directory / 'contracts', modules=('DitDahA1MemoryArbiter', 'DitDahA1MemoryFabric',
                                                      *(('DitDahA1DataCache', 'DitDahA1Coherence') if args.dcache_bytes else ()),
                                                      *(('DitDahA1LocalInterrupts',) if args.platform_only else ())))
            report['instructionStorage'] = verify_storage(rtl, directory / 'storage')
            report.update(hartCount=harts, axiDataBits=width, pmpEntries=entries, enableInterrupts=interrupts, iCacheBytes=args.icache_bytes, dCacheBytes=args.dcache_bytes)
            if not args.icache_bytes and not args.dcache_bytes and not args.platform_only:
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
