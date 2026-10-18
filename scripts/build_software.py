# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Build a freestanding software image for an implemented configuration."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def load_configuration(args):
    original = args.config
    content = original.read_bytes()
    document = json.loads(content)
    config = document.get('parameters', document)
    if args.harts is None and args.icache_bytes is None:
        return config, {}
    if args.harts is not None:
        config['hartCount'] = args.harts
    if args.icache_bytes is not None:
        config['iCacheBytes'] = args.icache_bytes
    args.config = args.output / 'input.json'
    assert args.config.resolve() != original.resolve(), 'Derived configuration would overwrite its source'
    args.config.write_text(json.dumps(config, indent=2) + '\n')
    return config, {str(original): hashlib.sha256(content).hexdigest()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--program', type=Path, default=Path('software/tests/console.S'))
    parser.add_argument('--output', type=Path, default=Path('result/software/console'))
    parser.add_argument('--tool-prefix', default=os.environ.get('RISCV_PREFIX', 'riscv64-unknown-elf-'))
    parser.add_argument('--stack-bytes', type=int, default=1024)
    parser.add_argument('--console-base', type=lambda value: int(value, 0))
    parser.add_argument('--harts', type=int, choices=range(1, 17))
    parser.add_argument('--icache-bytes', type=int, choices=(0, 8192, 16384, 32768, 65536))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'manifest.json').unlink(missing_ok=True)
    config, configuration_sources = load_configuration(args)
    configuration_bytes = args.config.read_bytes()
    base, harts = int(config['resetVector']), config['hartCount']
    ram = next(r for r in config['memoryRegions'] if int(r['base']) == base and r['readable'] and r['writable'] and r['executable'] and not r['device'])
    assert 1 <= harts <= 16 and args.stack_bytes >= 16 and args.stack_bytes % 16 == 0
    assert harts * args.stack_bytes <= int(ram['size']), 'Software stacks exceed RAM'
    console = base + 0x5000 if args.console_base is None else args.console_base
    assert any(r['device'] and r['writable'] and not r['executable'] and int(r['base']) <= console and
               console + 4 * harts <= int(r['base']) + int(r['size']) for r in config['memoryRegions']), 'Console device region is missing'
    runtime = Path('software/runtime')
    sources = [runtime / 'start.S', runtime / 'console.S', args.program, runtime / 'link.ld']
    hashes = {**configuration_sources, **{str(p): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in [*sources, Path('scripts/build_software.py')]}}
    tool_versions = {tool: subprocess.check_output([args.tool_prefix + tool, '--version'], text=True).splitlines()[0]
                     for tool in ('gcc', 'ld', 'objdump', 'objcopy')}
    image = args.output / 'software.elf'
    definitions = dict(__ram_base=base, __ram_bytes=int(ram['size']), __hart_count=harts,
                       __stack_bytes=args.stack_bytes, __console_base=console)
    command = [args.tool_prefix + 'gcc', '-march=rv64i_zicsr_zifencei', '-mabi=lp64', '-mcmodel=medany',
               '-Os', '-ffreestanding', '-fno-builtin', '-fno-stack-protector', '-msmall-data-limit=0',
               '-nostdlib', '-nostartfiles', '-Wl,--no-relax', '-T', str(runtime / 'link.ld'),
               *(f'-Wl,--defsym={name}={value}' for name, value in definitions.items()),
               f'-Wl,-Map={args.output / "software.map"}', *map(str, sources[:3]), '-o', str(image)]
    with (args.output / 'build.log').open('w') as log:
        subprocess.run(command, check=True, stdout=log, stderr=subprocess.STDOUT)
    dump = subprocess.check_output([args.tool_prefix + 'objdump', '-d', '-M', 'no-aliases,numeric', str(image)], text=True)
    (args.output / 'software.dump').write_text(dump)
    symbols = {}
    for line in subprocess.check_output([args.tool_prefix + 'nm', '-g', '--defined-only', str(image)], text=True).splitlines():
        fields = line.split()
        if len(fields) == 3:
            symbols[fields[2]] = int(fields[0], 16)
    subprocess.run([args.tool_prefix + 'objcopy', '-O', 'binary', str(image), str(args.output / 'software.bin')], check=True)
    assert symbols['_start'] == base
    assert base <= symbols['__bss_end'] <= symbols['__stack_bottom'] < symbols['__stack_top'] <= base + int(ram['size'])
    assert all(hashlib.sha256(Path(name).read_bytes()).hexdigest() == expected for name, expected in hashes.items()), 'Software sources changed during build'
    assert args.config.read_bytes() == configuration_bytes, 'Configuration changed during build'
    manifest = dict(sourceHashes=hashes, configurationHash=hashlib.sha256(configuration_bytes).hexdigest(),
                    imageHash=hashlib.sha256(image.read_bytes()).hexdigest(), symbols=symbols, commands=[command],
                    toolVersions=tool_versions,
                    target=subprocess.check_output([args.tool_prefix + 'gcc', '-dumpmachine'], text=True).strip())
    (args.output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(image)


if __name__ == '__main__':
    main()
