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
    features = {key: value for key, value in ((key, getattr(args, option, None)) for key, option in
                (('enableCounters', 'counters'), ('hpmCounters', 'hpm_counters'), ('enableSstc', 'sstc'), ('enableMisaligned', 'misaligned'))) if value is not None}
    original = args.config
    content = original.read_bytes()
    document = json.loads(content)
    config = document.get('parameters', document)
    if args.harts is None and args.icache_bytes is None and args.dcache_bytes is None and not supervisor_mode and tlb_entries is None and burst_refill is None and data_refill is None and not translation and issue_width is None and not features:
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
    config.update(features)
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
    parser.add_argument('--scalar', nargs='+', choices=('Zicond', 'Zimop', 'Zcb', 'Zcmop', 'Zfa', 'Zfhmin', 'Zawrs', 'Zicbom', 'Zicboz'), default=[])
    parser.add_argument('--program', type=Path, default=Path('software/tests/console.S'))
    parser.add_argument('--zero-page-tables', action='store_true')
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
    parser.add_argument('--misaligned', action=argparse.BooleanOptionalAction, default=None)
    parser.add_argument('--counters', action=argparse.BooleanOptionalAction, default=None)
    parser.add_argument('--hpm-counters', type=int, choices=range(30))
    parser.add_argument('--sstc', action=argparse.BooleanOptionalAction, default=None)
    parser.add_argument('--sv39', action='store_true')
    parser.add_argument('--tlb-entries', type=int, choices=(0, 2, 4))
    for name in ('i-tlb-entries', 'd-tlb-entries', 'asid-bits'):
        parser.add_argument('--' + name, type=int, choices=(0, 4) if name == 'asid-bits' else (0, 2, 4))
    parser.add_argument('--burst-refill', action=argparse.BooleanOptionalAction, default=None)
    parser.add_argument('--expected-interrupt', type=int, choices=(1, 3, 5, 7, 9, 11, 13), action='append', default=[])
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
    required_extensions = [name for name in ('M', 'A', 'F', 'D', 'C') if name.lower() in args.isa[5:]] + sorted(set(args.bitmanip) | set(args.scalar))
    assert all((config.get('floatingPointBits', 0) >= (64 if name == 'D' else 32) if name in ('F', 'D') else config.get('enable' + name, name in ('M', 'A'))) for name in required_extensions), 'Software requires a disabled extension'
    assert not set(args.scalar) & {'Zcb', 'Zcmop'} or 'c' in args.isa[5:], 'Compressed scalar instructions require C'
    assert not set(args.scalar) & {'Zfa', 'Zfhmin'} or 'f' in args.isa[5:], 'Floating scalar instructions require F'
    assert 'Zawrs' not in args.scalar or 'a' in args.isa[5:], 'Reservation waits require A'
    counter_extensions = ['Zicntr', 'Zihpm'] if config.get('enableCounters') else []
    required_extensions += counter_extensions + (['Sscounterenw'] if counter_extensions and config.get('enableSupervisorMode') else [])
    required_extensions += (['Sscofpmf'] if counter_extensions and config.get('hpmCounters', 0) > 0 and config.get('enableInterrupts') else []) + (['Sstc'] if config.get('enableSstc') else [])
    counter_program = args.program.resolve() == Path('software/tests/counters.S').resolve()
    supervisor_memory = args.program.resolve() == Path('software/tests/virtual_memory.S').resolve() and all(config.get('enable' + name) for name in ('Svinval', 'Svpbmt', 'Svnapot', 'Ssnpm'))
    if supervisor_memory:
        assert config.get('virtualAddressBits') == 39 and 'Zicbom' in args.scalar, 'Supervisor memory software requires Sv39 and cache-block management'
        required_extensions += ['Svinval', 'Svpbmt', 'Svnapot', 'Ssnpm', 'Supm']
    assert not counter_program or config.get('pmpEntries', 0) > 0 and {'Sscofpmf', 'Sstc'} <= set(required_extensions), 'Counter software requires protection, overflow and supervisor timers'
    command = [args.tool_prefix + 'gcc', '-march=' + args.isa + '_zicsr_zifencei' + ''.join('_' + name.lower() for name in sorted(set(args.bitmanip) | set(args.scalar)) + counter_extensions),
               *(['-DDITDAH_ZERO_PAGE_TABLES'] if args.zero_page_tables else []),
               *(['-DDITDAH_SUPERVISOR_MEMORY'] if supervisor_memory else []),
               f'-DDITDAH_HART_COUNT={harts}',
               f'-DDITDAH_RAM_BASE={base}', f'-DDITDAH_RAM_BYTES={int(ram["size"])}',
               f'-DDITDAH_ASID_BITS={config.get("asidBits", 0)}',
               f'-DDITDAH_PMP_ENTRIES={config.get("pmpEntries", 0)}',
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
    required_instructions = []
    atomic_program = args.program.resolve() == Path('software/tests/atomic.c').resolve()
    if atomic_program or args.program.resolve() == Path('software/tests/virtual_memory.S').resolve():
        witnesses = {'Zicond': ('czero.eqz', 'czero.nez', 'pause', 'ntl.p1'), 'Zimop': ('mop.r.0', 'mop.rr.0'),
                     'Zcb': ('c.zext.b', 'c.mul'), 'Zcmop': ('c.mop.7',), 'Zfa': ('fli.s', 'froundnx.s'),
                     'Zfhmin': ('flh', 'fsh', 'fmv.x.h', 'fmv.h.x'), 'Zawrs': ('wrs.nto', 'wrs.sto'),
                     'Zicbom': ('cbo.inval', 'cbo.clean', 'cbo.flush'), 'Zicboz': ('cbo.zero',)}
        required_instructions = [name for extension in args.scalar if atomic_program or extension in ('Zawrs', 'Zicbom', 'Zicboz') for name in witnesses[extension]]
        if atomic_program and 'D' in required_extensions:
            required_instructions += (['fcvtmod.w.d'] if 'Zfa' in args.scalar else []) + (['fcvt.h.d', 'fcvt.d.h'] if 'Zfhmin' in args.scalar else [])
    manifest = dict(sourceHashes=hashes, configurationHash=hashlib.sha256(configuration_bytes).hexdigest(),
                    imageHash=hashlib.sha256(image.read_bytes()).hexdigest(), symbols=symbols, commands=[command],
                    toolVersions=tool_versions, requiredExtensions=required_extensions, requiredInstructions=required_instructions,
                    target=subprocess.check_output([args.tool_prefix + 'gcc', '-dumpmachine'], text=True).strip(),
                    expectedInterruptCauses=args.expected_interrupt, entryAddress=base,
                    requiredCsrs=[0x320, 0xb00, 0xb02, 0xc00, 0xc02, 0x306, 0x106, 0x30a, 0x323, 0xb03, 0x14d, 0xc01, 0xda0, 0x144] if counter_program else [0x30a, 0x10a, 0x180, 0x300] if supervisor_memory else [],
                    requiredWaitingHarts=list(range(harts)) if 'Zawrs' in args.scalar and args.program.resolve() in
                        [Path('software/tests/' + name).resolve() for name in ('atomic.c', 'virtual_memory.S', 'reservation.S')] else [],
                    clockHz=args.clock_hz, timebaseHz=args.timebase_hz)
    (args.output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(image)


if __name__ == '__main__':
    main()
