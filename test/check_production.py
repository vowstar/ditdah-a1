# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Check self-contained production artifacts and their external interfaces."""

from pathlib import Path
import json
import subprocess

for directory, top in (("production", "DitDahA1"), ("core", "DitDahA1Core"),
                       ("frontend", "DitDahA1Frontend")):
    rtl = Path("result") / directory
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    assert manifest['validationScope'] == {'production': 'system', 'core': 'core', 'frontend': 'frontend'}[directory]
    files = (rtl / "filelist.f").read_text().splitlines()
    assert files and all("DV" not in name and not name.startswith("ref_") for name in files)
    assert not list(rtl.glob("*DV*.sv")) and not list(rtl.glob("ref_*.sv"))
    header = (rtl / (top + ".sv")).read_text().split(");", 1)[0]
    assert "trace" not in header.lower()
    if top != "DitDahA1":
        assert "axi_" not in header
    subprocess.run(["verilator", "--lint-only", "--top-module", top,
                    *[str(rtl / name) for name in files]], check=True)
    print(f"{top} production interface and lint passed")

directory = Path('result/component-checks')
directory.mkdir(exist_ok=True)
parameters = json.loads(Path('result/production/ditdah_a1_config.json').read_text())['parameters']
for top, overrides, diagnostic in (
        ('DitDahA1', {'iCacheBytes': 8192}, 'RTL supports uncached memory'),
        ('DitDahA1Core', {'issueWidth': 2}, 'Core supports single issue'),
        ('DitDahA1Frontend', {'resetVector': '2'}, 'Frontend requires a word-aligned resetVector')):
    config = directory / (top + '.json')
    config.write_text(json.dumps(dict(parameters, **overrides)) + '\n')
    result = subprocess.run(['build-ditdah-a1', '--top', top, '--config', str(config),
                             '--output', str(directory / top)], capture_output=True, text=True, timeout=600)
    (directory / (top + '.log')).write_text(result.stdout + result.stderr)
    assert result.returncode and diagnostic in result.stdout + result.stderr, top
    print(f'{top} invalid configuration rejected')
