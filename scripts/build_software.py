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
    issue_width = getattr(args, 'issue_width', None)
    sv39 = getattr(args, 'sv39', False)
    supervisor_mode = getattr(args, 'supervisor_mode', False) or sv39
    tlb_entries = getattr(args, 'tlb_entries', None)
    translation = {key: getattr(args, option, None) for key, option in
                   (('iTlbEntries', 'i_tlb_entries'), ('dTlbEntries', 'd_tlb_entries'), ('asidBits', 'asid_bits'))}
    translation = {key: value for key, value in translation.items() if value is not None}
    burst_refill = getattr(args, 'burst_refill', None)
    data_refill = getattr(args, 'dcache_refill_bytes', None)
    original = args.config
    content = original.read_bytes()
    document = json.loads(content)
    config = document.get('parameters', document)
    if args.harts is None and args.icache_bytes is None and args.dcache_bytes is None and not supervisor_mode and tlb_entries is None and burst_refill is None and data_refill is None and not translation and issue_width is None:
        return config, {}
    if issue_width is not None:
        config['issueWidth'] = issue_width
    if args.harts is not None:
        config['hartCount'] = args.harts
    if args.icache_bytes is not None:
        config['iCacheBytes'] = args.icache_bytes
    if args.dcache_bytes is not None:
        config['dCacheBytes'] = args.dcache_bytes
    if data_refill is not None:
        config['dCacheRefillBytes'] = data_refill
    if supervisor_mode:
        config.update(enableSupervisorMode=True, enableUserMode=True, enableInterrupts=True)
    if sv39:
        config['virtualAddressBits'] = 39
    config.update(translation)
    if tlb_entries is not None:
        config['tlbEntries'] = tlb_entries
    if burst_refill is not None:
        config['enableBurstRefill'] = burst_refill
    args.config = args.output / 'input.json'
    assert args.config.resolve() != original.resolve(), 'Derived configuration would overwrite its source'
    args.config.write_text(json.dumps(config, indent=2) + '\n')
    return config, {str(original): hashlib.sha256(content).hexdigest()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--issue-width', type=int, choices=(1, 2, 3))
    parser.add_argument('--isa', choices=tuple('rv64i' + m + a + fp + c for m in ('', 'm') for a in ('', 'a') for fp in ('', 'f', 'fd') for c in ('', 'c')), default='rv64i')
    parser.add_argument('--bitmanip', nargs='+', choices=('Zba', 'Zbb', 'Zbs'), default=[])
    parser.add_argument('--program', type=Path, default=Path('software/tests/console.S'))
    parser.add_argument('--output', type=Path, default=Path('result/software/console'))
    parser.add_argument('--tool-prefix', default=os.environ.get('RISCV_PREFIX', 'riscv64-unknown-elf-'))
    parser.add_argument('--stack-bytes', type=int, default=1024)
    parser.add_argument('--console-base', type=lambda value: int(value, 0))
    parser.add_argument('--ram-base', type=lambda value: int(value, 0))
    parser.add_argument('--clock-hz', type=int, default=100000000)
    parser.add_argument('--timebase-hz', type=int, default=100000000)
    parser.add_argument('--harts', type=int, choices=range(1, 17))
    parser.add_argument('--icache-bytes', type=int, choices=(0, 8192, 16384, 32768, 65536))
    parser.add_argument('--dcache-bytes', type=int, choices=(0, 8192, 16384, 32768, 65536))
    parser.add_argument('--dcache-refill-bytes', type=int, choices=(8, 64))
    parser.add_argument('--supervisor-mode', action='store_true')
    parser.add_argument('--sv39', action='store_true')
    parser.add_argument('--tlb-entries', type=int, choices=(0, 2, 4))
    for name in ('i-tlb-entries', 'd-tlb-entries', 'asid-bits'):
        parser.add_argument('--' + name, type=int, choices=(0, 4) if name == 'asid-bits' else (0, 2, 4))
    parser.add_argument('--burst-refill', action=argparse.BooleanOptionalAction, default=None)
    parser.add_argument('--expected-interrupt', type=int, choices=(1, 3, 5, 7, 9, 11), action='append', default=[])
    args = parser.parse_args()
    assert 0 < args.timebase_hz <= args.clock_hz <= 1000000000 and args.clock_hz % args.timebase_hz == 0
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'manifest.json').unlink(missing_ok=True)
    config, configuration_sources = load_configuration(args)
    configuration_bytes = args.config.read_bytes()
    base, harts = int(config['resetVector']) if args.ram_base is None else args.ram_base, config['hartCount']
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
    if config.get('localInterruptBase') is not None:
        definitions['__local_interrupt_base'] = int(config['localInterruptBase'])
    required_extensions = [name for name in ('M', 'A', 'F', 'D', 'C') if name.lower() in args.isa[5:]] + sorted(set(args.bitmanip))
    assert all((config.get('floatingPointBits', 0) >= (64 if name == 'D' else 32) if name in ('F', 'D') else config.get('enable' + name, name in ('M', 'A'))) for name in required_extensions), 'Software requires a disabled extension'
    command = [args.tool_prefix + 'gcc', '-march=' + args.isa + '_zicsr_zifencei' + ''.join('_' + name.lower() for name in sorted(set(args.bitmanip))),
               f'-DDITDAH_HART_COUNT={harts}',
               f'-DDITDAH_RAM_BASE={base}', f'-DDITDAH_RAM_BYTES={int(ram["size"])}',
               f'-DDITDAH_ASID_BITS={config.get("asidBits", 0)}',
               f'-DDITDAH_CONSOLE_BASE={console}', '-mabi=lp64', '-mcmodel=medany',
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
                    toolVersions=tool_versions, requiredExtensions=required_extensions,
                    target=subprocess.check_output([args.tool_prefix + 'gcc', '-dumpmachine'], text=True).strip(),
                    expectedInterruptCauses=args.expected_interrupt, entryAddress=base,
                    clockHz=args.clock_hz, timebaseHz=args.timebase_hz)
    (args.output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(image)


if __name__ == '__main__':
    main()
