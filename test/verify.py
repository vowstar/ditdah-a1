# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Compare generated RTL against instruction and bus-level expectations."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

from contracts import verify as verify_contracts
from model import Model
from programs import cases


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
            (0x8000, 0x1000, False, False, True, False)):
        regions.append(dict(base=str(base + offset), size=str(size), readable=read,
                            writable=write, executable=execute, device=device))
    return dict(resetVector=str(base), axiDataBits=width, physicalAddressBits=32 if width == 64 else 56,
                virtualAddressBits=0, iCacheBytes=0, dCacheBytes=0, l2CacheBytes=0, pmpEntries=0,
                memoryRegions=regions)


def compile_tb(rtl, directory, width, pa, top='core_tb', source=None, extra_files=()):
    source = source or Path('test/core_tb.sv').resolve()
    files = [(rtl / name).resolve() for name in (rtl / 'filelist.f').read_text().splitlines()]
    run(['verilator', '--binary', '--timing', '--assert', '-j', '2', '--top-module', top,
         '-Wno-TIMESCALEMOD', '-Wno-WIDTHTRUNC', '-Wno-WIDTHEXPAND',
         f'-DAXI_BITS={width}', f'-DPA_BITS={pa}', '-I' + str(rtl.resolve()),
         '--Mdir', str((directory / 'obj').resolve()), *files, *extra_files, source], directory / 'compile.log')
    return (directory / 'obj' / ('V' + top)).resolve()


def check_fetches(lines, config, faults):
    def allowed(address):
        return address % 4 == 0 and address + 4 <= 1 << config['physicalAddressBits'] and any(
            int(region['base']) <= address and address + 4 <= int(region['base']) + int(region['size'])
            and region['executable'] for region in config['memoryRegions'])

    pending = None
    fetched, failed = Counter(), Counter()
    reachable = {int(config['resetVector'])}
    accepted, completed = 0, 0
    for line in lines:
        fields = line.split()
        if fields[:2] == ['BUS', 'fetch']:
            address, size, data = int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            assert pending is None, 'Overlapping instruction transactions'
            assert size == 4 and data == 0 and allowed(address), f'Forbidden fetch: {line}'
            assert address in reachable, f'Fetch outside sequential or committed control flow: {line}'
            reachable.add(address + 4)
            pending = address
            accepted += 1
        elif fields[:1] == ['FETCH']:
            address, response, instruction = (int(value, 16) for value in fields[1:])
            assert pending == address, f'Unrequested fetch response: {line}'
            assert response == (2 if address == faults.get('fetch') else 0), f'Fetch response: {line}'
            if response:
                failed[address] += 1
            else:
                fetched[address, instruction] += 1
            pending = None
            completed += 1
        elif fields[:1] == ['TRACE']:
            trace = tuple(int(value, 16) for value in fields[1:])
            pc, instruction, trap, cause = trace[1], trace[2], trace[7], trace[8]
            reachable.add(trace[3])
            if trap and cause == 1:
                if allowed(pc):
                    assert failed[pc], f'Fetch fault without failed response: {line}'
                    failed[pc] -= 1
            else:
                assert fetched[pc, instruction], f'Retirement without completed instruction fetch: {line}'
                fetched[pc, instruction] -= 1
    return dict(accepted=accepted, completed=completed, discarded=sum(fetched.values()) + sum(failed.values()))


def compare(binary, directory, config, transport='axi'):
    base = int(config['resetVector'])
    coverage = [0] * 6
    coverage_names = (('awBeforeW', 'wBeforeAw', 'awWithW', 'arStall', 'awStall', 'wStall') if transport == 'axi'
                      else ('overlap', 'instructionStall', 'dataStall', 'responseDelay', 'permissionReject', 'tagWrap'))
    count = 0
    reports = []
    pipeline_max, dependency_stalls = 0, 0
    for name, program in cases(base):
        image = directory / (name + '.hex')
        image.write_text('\n'.join(f'{program.memory.get(base + i, 0):02x}' for i in range(65536)) + '\n')
        model = Model(config, program.memory, program.faults)
        expected = []
        for _ in range(2000):
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
            run(command, log)
            lines = log.read_text().splitlines()
            assert 'PASS' in lines, f'{name}: simulation did not complete'
            actual = [tuple(int(v, 16) for v in line.split()[1:]) for line in lines if line.startswith('TRACE ')]
            bus = [(v[1], int(v[2], 16), int(v[3]), int(v[4], 16))
                   for line in lines if line.startswith('BUS ') for v in [line.split()]]
            assert len(actual) == len(expected), f'{name}: trace length {len(actual)} != {len(expected)}'
            for index, (observed, wanted) in enumerate(zip(actual, expected)):
                assert observed == wanted, f'{name} trace {index}:\nactual {observed}\nexpected {wanted}'
            data_bus = [event for event in bus if event[0] != 'fetch']
            expected_bus = [event for event in model.bus if event[0] != 'fetch']
            assert data_bus == expected_bus, f'{name}: unexpected data accesses\nactual {data_bus}\nexpected {expected_bus}'
            if transport == 'memory':
                requests = [(v[1], int(v[2], 16), int(v[3]), int(v[4], 16)) for line in lines
                            if line.startswith('REQUEST ') for v in [line.split()] if v[1] != 'fetch']
                assert requests == [r for r in model.requests if r[0] != 'fetch'], f'{name}: unexpected Core requests'
            fetches = check_fetches(lines, config, program.faults)
            if name == 'pipeline_redirect':
                fault = program.faults['fetch']
                assert any(line.startswith(f'FETCH {fault:016x} 2 ') for line in lines), 'Wrong-path fetch fault was not exercised'
            if name == 'pipeline_reuse':
                assert fetches['accepted'] > 256, 'Instruction identity wraparound was not exercised'
            for line in lines:
                if line.startswith('COVER '):
                    coverage = [a + int(b) for a, b in zip(coverage, line.split()[1:])]
                elif line.startswith('PIPELINE '):
                    occupancy, stalls = map(int, line.split()[1:])
                    pipeline_max = max(pipeline_max, occupancy)
                    dependency_stalls += stalls
            count += len(actual)
            reports.append(dict(test=name, seed=seed, events=len(actual), busTransactions=len(bus), fetches=fetches))
        print(f'  {name}: {len(expected)} events, three bus schedules', flush=True)
    assert all(coverage), f'{transport} coverage missing: {dict(zip(coverage_names, coverage))}'
    assert pipeline_max >= 2 and dependency_stalls, f'Pipeline coverage missing: {pipeline_max}, {dependency_stalls}'
    return dict(events=count, cases=reports, pipelineCoverage=dict(maxOccupancy=pipeline_max, dependencyStalls=dependency_stalls),
                **{('busCoverage' if transport == 'axi' else 'portCoverage'): dict(zip(coverage_names, coverage))})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--width', type=int, choices=(64, 128, 256, 512), action='append')
    parser.add_argument('--use-generated', action='store_true')
    args = parser.parse_args()
    summary_path = Path('result/verify/summary.json')
    summary_path.unlink(missing_ok=True)
    test_hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in sorted(Path('test').glob('*')) if p.suffix in ('.py', '.sv')}
    summary = {'scope': 'implemented scalar subset; simulation and assertions', 'configurations': []}
    core_profiles = {}
    for width in args.width or (64, 128, 256, 512):
        directory = Path(f'result/verify/axi{width}')
        directory.mkdir(parents=True, exist_ok=True)
        config = configuration(width)
        config_path = directory / 'input.json'
        config_path.write_text(json.dumps(config, indent=2) + '\n')
        rtl = directory / 'rtl'
        if not args.use_generated:
            print(f'Generating AXI{width} RTL', flush=True)
            run(['build-ditdah-a1', '--trace', '--config', config_path, '--output', rtl], directory / 'build.log')
        manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
        assert manifest['top'] == 'DitDahA1' and manifest['validationScope'] == 'system'
        assert manifest.get('sourceHashes'), 'Generated RTL has no source provenance'
        for name, digest in manifest['sourceHashes'].items():
            assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, f'Stale RTL source: {name}'
        for key, value in config.items():
            assert manifest['parameters'][key] == value, f'Stale RTL configuration: {key}'
        verify_contracts(rtl, directory / 'contracts')
        binary = compile_tb(rtl, directory, width, config['physicalAddressBits'])
        print(f'Checking AXI{width}', flush=True)
        report = compare(binary, directory, manifest['parameters'])
        report['interfaceContracts'] = ['fetch cancellation and identity', 'LSU authorization and completion',
                                        'frontend sequencing and redirects',
                                        'decode dependencies', 'memory arbitration and response ownership',
                                        'memory permissions and transfer attributes', 'AXI request and response handling',
                                        'physical fabric ownership, backpressure, and faults']
        report.update(axiDataBits=width, physicalAddressBits=config['physicalAddressBits'])
        summary['configurations'].append(report)
        core = directory / 'core'
        core_config = dict(config, axiDataBits=256, iCacheBytes=8192)
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
        report['core'] = compare(binary, core, core_manifest['parameters'], 'memory')
        core_profiles[core_key] = str(core)
    frontend_config = dict(configuration(128), issueWidth=2, axiDataBits=512, iCacheBytes=8192)
    Path('result/frontend-input.json').write_text(json.dumps(frontend_config, indent=2) + '\n')
    fabric_config = dict(frontend_config, resetVector='2', hartCount=8, virtualAddressBits=48, pmpEntries=16)
    Path('result/fabric-input.json').write_text(json.dumps(fabric_config, indent=2) + '\n')
    summary['sourceHashes'] = {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in sorted(Path('ditdah_a1/src').glob('*.scala'))}
    for name, digest in test_hashes.items():
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, f'Test changed during verification: {name}'
    summary['sourceHashes'].update(test_hashes)
    Path('result/verify/summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('Scalar RTL verification passed', flush=True)


if __name__ == '__main__':
    main()
