# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Check self-contained production artifacts and their external interfaces."""

from pathlib import Path
import argparse
import re
import json
import runpy
import subprocess
from types import SimpleNamespace
from contracts import verify_storage

parser = argparse.ArgumentParser()
parser.add_argument('--harts', type=int, nargs='+', choices=(2, 3, 15, 16), default=[2])
parser.add_argument('--data-cache', action='store_true')
parser.add_argument('--dcache-refill-bytes', type=int, choices=(8, 64), default=8)
parser.add_argument('--supervisor', action='store_true')
parser.add_argument('--sv39', action='store_true')
parser.add_argument('--burst-refill', action='store_true')
parser.add_argument('--pipeline', action='store_true')
parser.add_argument('--tlb-entries', type=int, choices=(0, 2, 4), default=0)
args = parser.parse_args()

load_configuration = runpy.run_path('scripts/build_software.py')['load_configuration']
source = Path('software/platform.json')
original = source.read_bytes()
baseline = json.loads(original)
directory = Path('result/software-config-checks') / ('pipeline' if args.pipeline else 'sv39' if args.sv39 else 'supervisor' if args.supervisor else 'data-cache' if args.data_cache else 'base')
for name, overrides in (('unchanged', {}), ('derived', dict(harts=2)), ('supervisor', dict(harts=2, supervisor_mode=True)), ('sv39', dict(harts=2, sv39=True)), ('cache', dict(tlb_entries=2)), ('burst', dict(burst_refill=True)), ('data-line', dict(dcache_bytes=8192, dcache_refill_bytes=64))):
    output = directory / name
    output.mkdir(parents=True, exist_ok=True)
    selection = SimpleNamespace(config=source, output=output, harts=None, icache_bytes=None, dcache_bytes=None)
    vars(selection).update(overrides)
    selected, _ = load_configuration(selection)
    assert selected['hartCount'] == overrides.get('harts', baseline['hartCount'])
    assert bool(selected.get('enableSupervisorMode')) == bool(overrides.get('supervisor_mode') or overrides.get('sv39'))
    assert selected['virtualAddressBits'] == (39 if overrides.get('sv39') else baseline['virtualAddressBits'])
    assert bool(selected.get('enableBurstRefill')) == bool(overrides.get('burst_refill'))
    assert selected.get('tlbEntries', 0) == overrides.get('tlb_entries', 0)
    assert selected.get('dCacheRefillBytes', 8) == overrides.get('dcache_refill_bytes', 8)
    if overrides.get('supervisor_mode') or overrides.get('sv39'):
        assert selected['enableUserMode'] and selected['enableInterrupts']
    if selection.config != source:
        assert json.loads(selection.config.read_text()) == selected
    assert source.read_bytes() == original
print('Software configuration compatibility contracts passed', flush=True)

tops = (("production", "DitDahA1"), ("core", "DitDahA1Core"),
        ("frontend", "DitDahA1Frontend"), ("fabric", "DitDahA1MemoryFabric"), ("backend", "DitDahA1Backend"))
profiles = (*tops, *((directory + '-pmp16', top) for directory, top in tops if directory != 'fabric'),
                       *((directory + '-irq', top) for directory, top in tops if directory in ('production', 'core', 'backend')),
                       *((f'production-harts{count}', 'DitDahA1') for count in args.harts))
if args.data_cache:
    profiles = (('production-dcache', 'DitDahA1'), ('production-dcache-harts16', 'DitDahA1'),
                ('fabric-dcache', 'DitDahA1MemoryFabric'))
if args.supervisor or args.sv39:
    profiles = (('production-sv39' + (f'-tlb{args.tlb_entries}' if args.tlb_entries else '') if args.sv39 else 'production-supervisor', 'DitDahA1'),)
if args.burst_refill:
    profiles = (('production-burst', 'DitDahA1'),)
if args.pipeline:
    profiles = (('production-width2', 'DitDahA1'), ('production-prediction', 'DitDahA1'))
if args.dcache_refill_bytes == 64:
    profiles = (('production-data-line', 'DitDahA1'), ('production-data-line-burst', 'DitDahA1'))
for directory, top in profiles:
    burst = args.burst_refill or directory == 'production-data-line-burst'
    rtl = Path("result") / directory
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    assert manifest['implementation']['issueWidth'] == manifest['parameters']['issueWidth']
    count = manifest['parameters']['hartCount'] if args.supervisor or args.sv39 or burst or args.dcache_refill_bytes == 64 else int(directory.split('-harts')[1]) if '-harts' in directory else 1
    component = directory.split('-')[0]
    assert manifest['validationScope'] == {'production': 'system', 'core': 'core', 'frontend': 'frontend', 'fabric': 'fabric', 'backend': 'backend'}[component]
    interrupts = top != 'DitDahA1MemoryFabric' and (directory.endswith('-irq') or '-harts' in directory or args.data_cache or args.supervisor or args.sv39 or burst or args.dcache_refill_bytes == 64 or args.pipeline)
    enabled = (directory.endswith('-pmp16') or interrupts) and not args.pipeline
    if args.pipeline:
        prediction = directory == 'production-prediction'
        assert manifest['parameters']['issueWidth'] == (3 if prediction else 2)
        assert manifest['parameters']['enableBranchPrediction'] == prediction
    assert manifest['implementation']['machineInterrupts'] == interrupts
    assert manifest['implementation']['pmpEntries'] == (16 if enabled else 0)
    assert manifest['implementation']['pmpState'] == (enabled and top != 'DitDahA1Frontend')
    assert manifest['implementation']['hartCount'] == (count if top == 'DitDahA1' else int(top == 'DitDahA1Core'))
    assert manifest['implementation']['fabricRequesters'] == (2 * manifest['parameters']['hartCount'] if top in ('DitDahA1', 'DitDahA1MemoryFabric') else 0)
    read_slots = 2 if top in ('DitDahA1', 'DitDahA1MemoryFabric') and manifest['parameters']['hartCount'] > 1 else 0
    assert manifest['implementation']['fabricReadSlots'] == read_slots
    assert manifest['implementation']['enableBranchPrediction'] == (
        manifest['parameters']['enableBranchPrediction'] and top in ('DitDahA1', 'DitDahA1Core', 'DitDahA1Frontend'))
    files = (rtl / "filelist.f").read_text().splitlines()
    assert ('DitDahA1ReadQueue.sv' in files) == bool(read_slots)
    cache_bytes = manifest['parameters']['iCacheBytes'] if top in ('DitDahA1', 'DitDahA1Core', 'DitDahA1Frontend') else 0
    assert manifest['implementation']['iCacheBytes'] == cache_bytes
    assert ('DitDahA1InstructionCache.sv' in files) == bool(cache_bytes), 'Instruction cache bypass or module mismatch'
    data_cache = args.data_cache or args.supervisor or args.sv39 or burst or args.dcache_refill_bytes == 64 or (args.pipeline and directory == 'production-width2')
    assert manifest['implementation']['dCacheBytes'] == (8192 if data_cache and top == 'DitDahA1' else 0)
    assert manifest['implementation']['dataCoherence'] == data_cache
    assert manifest['parameters']['dCacheRefillBytes'] == args.dcache_refill_bytes
    assert manifest['implementation']['dCacheRefillBytes'] == (args.dcache_refill_bytes if data_cache and top == 'DitDahA1' else 0)
    assert ('DitDahA1DataCache.sv' in files) == (data_cache and top == 'DitDahA1')
    assert ('DitDahA1Coherence.sv' in files) == data_cache
    if args.supervisor or args.sv39:
        assert count == 16 and manifest['parameters']['enableSupervisorMode']
        assert manifest['implementation']['privilege'] == 'MSU' and 'sret' in manifest['implementation']['instructions']
    assert ('DitDahA1Translation.sv' in files) == args.sv39
    assert manifest['implementation']['tlbEntries'] == args.tlb_entries
    assert manifest['parameters']['enableBurstRefill'] == burst
    assert manifest['implementation']['enableBurstRefill'] == burst
    if top in ('DitDahA1', 'DitDahA1MemoryFabric'):
        axi = (rtl / 'DitDahA1Axi.sv').read_text()
        assert bool(re.search(r'\bbeat\b', axi)) == (burst or args.dcache_refill_bytes == 64), 'Burst state presence differs from configuration'
    if args.sv39:
        assert ('tlbValid' in (rtl / 'DitDahA1Translation.sv').read_text()) == bool(args.tlb_entries)
    if args.sv39:
        assert manifest['parameters']['virtualAddressBits'] == 39
        assert manifest['implementation']['translation'] == 'Sv39/Svade'
        assert 'sfence.vma' in manifest['implementation']['instructions']
    verify_storage(rtl, rtl / 'storage-check')
    assert files and all("DV" not in name and not name.startswith("ref_") for name in files)
    assert not list(rtl.glob("*DV*.sv")) and not list(rtl.glob("ref_*.sv"))
    header = (rtl / (top + ".sv")).read_text().split(");", 1)[0]
    assert "trace" not in header.lower()
    names = [f'interrupts_{h}_{name}' if top == 'DitDahA1' else f'interrupts_{name}'
             for h in range(count) for name in ('software', 'timer', 'external')]
    assert all((name in header) == interrupts for name in names)
    assert ('hartId' in header) == (top in ('DitDahA1Core', 'DitDahA1Backend'))
    if top == 'DitDahA1':
        assert re.findall(r'\bDitDahA1Core\s+(\w+)\s*\(', (rtl / (top + '.sv')).read_text()) == [f'core_{h}' for h in range(count)]
        assert re.findall(r'\bDitDahA1DataCache\s+(\w+)\s*\(', (rtl / (top + '.sv')).read_text()) == ([f'data_cache_{h}' for h in range(count)] if data_cache else [])
    if top in ("DitDahA1Core", "DitDahA1Frontend", "DitDahA1Backend"):
        assert "axi_" not in header
    else:
        width = max(1, (manifest['parameters']['hartCount'] - 1).bit_length())
        for channel in ('aw', 'ar', 'b', 'r'):
            port = next((m for m in re.finditer(r'\b(?:input|output)\s*(?:\[(\d+):0\])?([\s\S]*?)(?=\binput\b|\boutput\b|$)', header)
                         if re.search(r'\baxi_' + channel + r'_bits_id\b', m[2])), None)
            assert port and (int(port[1]) + 1 if port[1] else 1) == width, 'AXI hart identity width mismatch'
    if top == 'DitDahA1Backend':
        assert set(files) == {'DitDahA1' + name + '.sv' for name in ('Backend', 'Decode', 'Issue', 'Execute', 'Multiply', 'Commit', 'Gpr', 'Csr', 'Lsu', *(('Pmp',) if enabled else ()))}
        assert (rtl / (top + '.sv')).read_bytes() == Path('result/verify/' + ('irq-' if interrupts else '') + ('pmp16-' if enabled else '') + 'axi512/rtl', top + '.sv').read_bytes()
    if top == 'DitDahA1MemoryFabric':
        assert set(files) == {name + '.sv' for name in (top, 'DitDahA1MemoryArbiter', 'DitDahA1Memory', 'DitDahA1Axi',
            *(('DitDahA1ReadQueue',) if manifest['parameters']['hartCount'] > 1 else ()),
            *(('DitDahA1Coherence',) if args.data_cache else ()))}
        integrated = Path('result/production-dcache-harts16' if args.data_cache else 'result/production-harts16')
        assert all((rtl / name).read_bytes() == (integrated / name).read_bytes() for name in ('DitDahA1Memory.sv', 'DitDahA1Axi.sv'))
    subprocess.run(["verilator", "--lint-only", "--top-module", top,
                    *[str(rtl / name) for name in files]], check=True)
    print(f"{top} production interface and lint passed")

if args.data_cache or args.supervisor or args.sv39 or args.pipeline or args.dcache_refill_bytes == 64:
    raise SystemExit(0)

directory = Path('result/component-checks')
directory.mkdir(exist_ok=True)
parameters = json.loads(Path('result/production/ditdah_a1_config.json').read_text())['parameters']
for index, (top, overrides, diagnostic) in enumerate((
        ('DitDahA1', {'dCacheBytes': 16384}, 'RTL supports zero or 8192 data cache bytes'),
        ('DitDahA1', {'hartCount': 0}, 'hartCount must be between 1 and 16'),
        ('DitDahA1', {'hartCount': 17}, 'hartCount must be between 1 and 16'),
        ('DitDahA1Core', {'pmpEntries': 64}, 'RTL supports zero or sixteen PMP entries'),
        ('DitDahA1Frontend', {'pmpEntries': 64}, 'RTL supports zero or sixteen PMP entries'),
        ('DitDahA1Core', {'issueWidth': 0}, 'issueWidth must be between 1 and 3'),
        ('DitDahA1Backend', {'issueWidth': 4}, 'issueWidth must be between 1 and 3'),
        ('DitDahA1Frontend', {'resetVector': '2'}, 'Frontend requires a word-aligned resetVector'),
        ('DitDahA1MemoryFabric', {'axiDataBits': 96}, 'axiDataBits must be'),
        ('DitDahA1MemoryFabric', {'memoryRegions': [{'base': '0', 'size': '16'}, {'base': '8', 'size': '8'}]}, 'Memory regions must not overlap'),
        ('DitDahA1Core', {'virtualAddressBits': 48}, 'RTL supports Bare or Sv39 addressing'),
        ('DitDahA1Core', {'tlbEntries': 2}, 'Translation cache requires Sv39'))):
    config = directory / f'{top}-{index}.json'
    config.write_text(json.dumps(dict(parameters, **overrides)) + '\n')
    result = subprocess.run(['build-ditdah-a1', '--top', top, '--config', str(config),
                             '--output', str(directory / top)], capture_output=True, text=True, timeout=600)
    (directory / f'{top}-{index}.log').write_text(result.stdout + result.stderr)
    assert result.returncode and diagnostic in result.stdout + result.stderr, top
    print(f'{top} invalid configuration rejected')
