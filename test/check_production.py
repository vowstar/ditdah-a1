# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Check self-contained production artifacts and their external interfaces."""

from pathlib import Path
import argparse
import re
import json
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--harts', type=int, nargs='+', choices=(2, 3, 15, 16), default=[2])
args = parser.parse_args()

tops = (("production", "DitDahA1"), ("core", "DitDahA1Core"),
        ("frontend", "DitDahA1Frontend"), ("fabric", "DitDahA1MemoryFabric"), ("backend", "DitDahA1Backend"))
for directory, top in (*tops, *((directory + '-pmp16', top) for directory, top in tops if directory != 'fabric'),
                       *((directory + '-irq', top) for directory, top in tops if directory in ('production', 'core', 'backend')),
                       *((f'production-harts{count}', 'DitDahA1') for count in args.harts)):
    rtl = Path("result") / directory
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    count = int(directory.split('-harts')[1]) if '-harts' in directory else 1
    component = directory.split('-')[0]
    assert manifest['validationScope'] == {'production': 'system', 'core': 'core', 'frontend': 'frontend', 'fabric': 'fabric', 'backend': 'backend'}[component]
    interrupts = directory.endswith('-irq') or '-harts' in directory
    enabled = directory.endswith('-pmp16') or interrupts
    assert manifest['implementation']['machineInterrupts'] == interrupts
    assert manifest['implementation']['pmpEntries'] == (16 if enabled else 0)
    assert manifest['implementation']['pmpState'] == (enabled and top != 'DitDahA1Frontend')
    assert manifest['implementation']['hartCount'] == (count if top == 'DitDahA1' else int(top == 'DitDahA1Core'))
    assert manifest['implementation']['fabricRequesters'] == (2 * manifest['parameters']['hartCount'] if top in ('DitDahA1', 'DitDahA1MemoryFabric') else 0)
    files = (rtl / "filelist.f").read_text().splitlines()
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
    if top in ("DitDahA1Core", "DitDahA1Frontend", "DitDahA1Backend"):
        assert "axi_" not in header
    if top == 'DitDahA1Backend':
        assert set(files) == {'DitDahA1' + name + '.sv' for name in ('Backend', 'Decode', 'Issue', 'Execute', 'Multiply', 'Commit', 'Gpr', 'Csr', 'Lsu', *(('Pmp',) if enabled else ()))}
        assert (rtl / (top + '.sv')).read_bytes() == Path('result/verify/' + ('irq-' if interrupts else '') + ('pmp16-' if enabled else '') + 'axi512/rtl', top + '.sv').read_bytes()
    if top == 'DitDahA1MemoryFabric':
        assert set(files) == {name + '.sv' for name in (top, 'DitDahA1MemoryArbiter', 'DitDahA1Memory', 'DitDahA1Axi')}
        integrated = Path('result/verify/axi512/rtl')
        assert all((rtl / name).read_bytes() == (integrated / name).read_bytes() for name in ('DitDahA1Memory.sv', 'DitDahA1Axi.sv'))
    subprocess.run(["verilator", "--lint-only", "--top-module", top,
                    *[str(rtl / name) for name in files]], check=True)
    print(f"{top} production interface and lint passed")

directory = Path('result/component-checks')
directory.mkdir(exist_ok=True)
parameters = json.loads(Path('result/production/ditdah_a1_config.json').read_text())['parameters']
for index, (top, overrides, diagnostic) in enumerate((
        ('DitDahA1', {'iCacheBytes': 8192}, 'RTL supports uncached memory'),
        ('DitDahA1', {'hartCount': 0}, 'hartCount must be between 1 and 16'),
        ('DitDahA1', {'hartCount': 17}, 'hartCount must be between 1 and 16'),
        ('DitDahA1Core', {'pmpEntries': 64}, 'RTL supports zero or sixteen PMP entries'),
        ('DitDahA1Frontend', {'pmpEntries': 64}, 'RTL supports zero or sixteen PMP entries'),
        ('DitDahA1Core', {'issueWidth': 2}, 'Backend supports single issue'),
        ('DitDahA1Backend', {'issueWidth': 2}, 'Backend supports single issue'),
        ('DitDahA1Frontend', {'resetVector': '2'}, 'Frontend requires a word-aligned resetVector'),
        ('DitDahA1MemoryFabric', {'axiDataBits': 96}, 'axiDataBits must be'),
        ('DitDahA1MemoryFabric', {'memoryRegions': [{'base': '0', 'size': '16'}, {'base': '8', 'size': '8'}]}, 'Memory regions must not overlap'))):
    config = directory / f'{top}-{index}.json'
    config.write_text(json.dumps(dict(parameters, **overrides)) + '\n')
    result = subprocess.run(['build-ditdah-a1', '--top', top, '--config', str(config),
                             '--output', str(directory / top)], capture_output=True, text=True, timeout=600)
    (directory / f'{top}-{index}.log').write_text(result.stdout + result.stderr)
    assert result.returncode and diagnostic in result.stdout + result.stderr, top
    print(f'{top} invalid configuration rejected')
