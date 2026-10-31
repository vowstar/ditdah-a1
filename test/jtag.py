# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Exercise JTAG scanning and single-owner asynchronous DMI transport."""

import argparse
import hashlib
import json
import resource
from pathlib import Path

from verify import configuration, run


def main():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--use-generated', action='store_true')
    args = parser.parse_args()
    inputs = ('test/jtag.py', 'test/jtag_tb.sv', 'test/verify.py')
    hashes = {p: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in inputs}
    output = args.output
    output.mkdir(parents=True, exist_ok=True)
    config = output / 'input.json'
    idcode = 0xa1000000 | (0x13579b << 1) | 1
    config.write_text(json.dumps(dict(configuration(64), enableJtag=True, jtagIdcode=idcode)) + '\n')
    files, manifests = [], {}
    for name, top in [('dtm', 'DitDahA1JtagDtm'), ('bridge', 'DitDahA1DmiBridge')]:
        rtl = output / name
        if not args.use_generated:
            run(['build-ditdah-a1', '--top', top, '--config', config, '--output', rtl], output / f'{name}-build.log')
        manifests[name] = json.loads((rtl / 'ditdah_a1_config.json').read_text())
        assert manifests[name]['top'] == top
        assert manifests[name]['parameters']['jtagIdcode'] == idcode
        assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == value
                   for p, value in manifests[name]['sourceHashes'].items()), 'Stale transport RTL'
        files.extend((rtl / f).resolve() for f in (rtl / 'filelist.f').read_text().splitlines())
    build = (output / 'native').resolve()
    run(['verilator', '--binary', '--timing', '--assert', '-j', '2', '--top-module', 'jtag_tb',
         '-Wno-fatal', '--Mdir', build, *files, Path('test/jtag_tb.sv')], output / 'native-compile.log')
    binary = build / 'Vjtag_tb'
    results = []
    for half, seed in [(2, 17), (5, 73), (19, 109), (83, 271)]:
        log = output / f'clock-{half}-seed-{seed}.log'
        run([binary, f'+SYSTEM_HALF={half}', f'+SEED={seed}', f'+IDCODE={idcode:x}'], log, timeout=30)
        assert 'PASS\n' in log.read_text()
        results.append(dict(systemHalf=half, seed=seed, log=log.name))
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == value for p, value in hashes.items())
    report = dict(manifests=manifests, schedules=results,
                  testSourceHashes=hashes)
    (output / 'summary.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'JTAG transport checks passed: {len(results)} asynchronous clock schedules')


if __name__ == '__main__':
    main()
