# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Build the machine-mode multicore software consumer."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from build_software import load_configuration

REVISION = 'dccb09599635bdff17633fa7e9dab014b91dce90'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def platform(config, ram, console, frequency, qemu):
    harts = config['hartCount']
    local = int(config['localInterruptBase'])
    cpus = []
    for hart in range(max(8, harts) if qemu else harts):
        cpus.append(f'''cpu@{hart:x} {{ device_type = "cpu"; compatible = "riscv"; reg = <{hart}>;
 status = "{'okay' if hart < harts else 'disabled'}"; riscv,isa-base = "rv64i";
 riscv,isa-extensions = "i", "a", "zicsr", "zifencei";
 hlic{hart}: interrupt-controller {{ compatible = "riscv,cpu-intc";
 #address-cells = <0>; #interrupt-cells = <1>; interrupt-controller; }}; }};''')
    timer_irqs = ' '.join(f'&hlic{hart} 7' for hart in range(harts))
    local_irqs = ' '.join(f'&hlic{hart} 3 &hlic{hart} 7' for hart in range(harts))
    cpu_nodes = f'cpus {{ #address-cells = <1>; #size-cells = <0>; timebase-frequency = <{frequency}>; {" ".join(cpus)} }};'
    header = '/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */\n/* SPDX-License-Identifier: MIT */\n'
    if qemu:
        assert int(ram['base']) == 0x80000000 and local == 0x2000000 and frequency == 10000000
        return header + f'''/ {{ {cpu_nodes} }};
&ram0 {{ reg = <0x80000000 0x{int(ram['size']):x}>; }};
&clint {{ interrupts-extended = <{local_irqs}>; }};
&mtimer {{ interrupts-extended = <{timer_irqs}>; }};
'''
    def reg(address, size):
        return f'<0x{address >> 32:x} 0x{address & 0xffffffff:x} 0x{size >> 32:x} 0x{size & 0xffffffff:x}>'
    return header + f'''/ {{ #address-cells = <2>; #size-cells = <2>;
 chosen {{ zephyr,sram = &ram0; }}; {cpu_nodes}
 ram0: memory@{int(ram['base']):x} {{ device_type = "memory"; reg = {reg(int(ram['base']), int(ram['size']))}; }};
 clint: interrupt-controller@{local:x} {{ compatible = "sifive,clint0"; reg = {reg(local, 65536)}; interrupts-extended = <{local_irqs}>; }};
 mtimer: timer@{local + 0xbff8:x} {{ compatible = "riscv,machine-timer";
 reg = {reg(local + 0xbff8, 8)}, {reg(local + 0x4000, 8)}; reg-names = "mtime", "mtimecmp"; interrupts-extended = <{timer_irqs}>; }};
 console_tx: console@{console:x} {{ compatible = "ditdah,console"; reg = {reg(console, 4 * harts)}; }};
}};
'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=Path('result/zephyr'))
    parser.add_argument('--zephyr-base', type=Path, default=os.environ.get('ZEPHYR_BASE'))
    parser.add_argument('--tool-prefix', default=os.environ.get('RISCV_PREFIX', 'riscv64-unknown-elf-'))
    parser.add_argument('--python', default=sys.executable)
    parser.add_argument('--console-base', type=lambda value: int(value, 0), required=True)
    parser.add_argument('--timebase-hz', type=int, required=True)
    parser.add_argument('--qemu', action='store_true')
    parser.add_argument('--harts', type=int, choices=range(1, 17))
    parser.add_argument('--icache-bytes', type=int, choices=(0, 8192, 16384, 32768, 65536))
    parser.add_argument('--dcache-bytes', type=int, choices=(0, 8192))
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    (output / 'manifest.json').unlink(missing_ok=True)
    assert args.zephyr_base is not None, 'Set ZEPHYR_BASE or --zephyr-base'
    upstream = args.zephyr_base.resolve()
    assert subprocess.check_output(['git', '-C', str(upstream), 'rev-parse', 'HEAD'], text=True).strip() == REVISION
    subprocess.run(['git', '-C', str(upstream), 'diff', '--exit-code', 'HEAD'], check=True, stdout=subprocess.DEVNULL)
    config, configuration_sources = load_configuration(args)
    configuration_bytes = args.config.read_bytes()
    harts, base = config['hartCount'], int(config['resetVector'])
    assert 1 <= harts <= 16 and args.timebase_hz > 0 and config['enableInterrupts']
    assert config['localInterruptBase'] is not None and config['pmpEntries'] in (0, 16)
    ram = next(r for r in config['memoryRegions'] if int(r['base']) == base and r['readable'] and r['writable'] and r['executable'] and r['atomic'] and not r['device'])
    console = args.console_base
    assert not base <= console < base + int(ram['size']), 'Console must be outside RAM'
    assert any(r['device'] and r['writable'] and not r['executable'] and not r['atomic'] and
               int(r['base']) <= console and console + 4 * harts <= int(r['base']) + int(r['size']) for r in config['memoryRegions'])
    source = Path('software/zephyr').resolve()
    paths = sorted(p for p in source.rglob('*') if p.is_file()) + [Path(__file__).resolve(), Path('scripts/build_software.py').resolve()]
    hashes = {**configuration_sources, **{str(p.relative_to(Path.cwd())): digest(p) for p in paths}}
    dts = output / ('platform.overlay' if args.qemu else 'platform.dtsi')
    dts.write_text(platform(config, ram, console, args.timebase_hz, args.qemu))
    profile = output / 'profile.conf'
    profile.write_text('# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>\n# SPDX-License-Identifier: MIT\n' +
        f'CONFIG_MP_MAX_NUM_CPUS={harts}\nCONFIG_SYS_CLOCK_HW_CYCLES_PER_SEC={args.timebase_hz}\n' +
        f'CONFIG_SPIN_VALIDATE={"y" if harts <= 4 else "n"}\nCONFIG_RISCV_PMP={"y" if config["pmpEntries"] else "n"}\n')
    build = output / 'build'
    board = ('qemu_riscv64/qemu_virt_riscv64/smp' if args.qemu else 'ditdah_a1')
    commands = [['cmake', '-G', 'Ninja', '-S', str(source), '-B', str(build), f'-DBOARD={board}',
        f'-DZEPHYR_MODULES={upstream}', f'-DPython3_EXECUTABLE={args.python}',
        f'-DUSER_CACHE_DIR={output / "cache"}', f'-DEXTRA_CONF_FILE={profile}',
        f'-DDTS_EXTRA_CPPFLAGS=-I{output}', '-DBUILD_VERSION=v4.4.2']]
    if args.qemu:
        commands[0].append(f'-DDTC_OVERLAY_FILE={dts}')
    commands.append(['cmake', '--build', str(build), '--parallel', '2'])
    env = dict(os.environ, ZEPHYR_BASE=str(upstream), ZEPHYR_TOOLCHAIN_VARIANT='cross-compile', CROSS_COMPILE=args.tool_prefix)
    with (output / 'build.log').open('w') as log:
        for command in commands:
            subprocess.run(command, check=True, env=env, stdout=log, stderr=subprocess.STDOUT)
    image = output / 'software.elf'
    shutil.copyfile(build / 'zephyr/zephyr.elf', image)
    stacks = []
    for line in subprocess.check_output([args.tool_prefix + 'nm', '-S', '--defined-only', str(image)], text=True).splitlines():
        fields = line.split()
        if len(fields) not in (3, 4):
            continue
        address, name = int(fields[0], 16), fields[-1]
        if len(fields) == 4 and fields[2] in ('B', 'b') and name.endswith(('_stack', '_stacks')):
            size = int(fields[1], 16)
            count = harts if name.endswith('_stacks') else 1
            assert size and size % count == 0
            stacks.append(dict(symbol=name, address=address, size=size, count=count, stride=size // count))
    symbols = {fields[2]: int(fields[0], 16) for line in subprocess.check_output(
        [args.tool_prefix + 'nm', '-g', '--defined-only', str(image)], text=True).splitlines()
        if len(fields := line.split()) == 3}
    assert symbols['__start'] == symbols['_start'] == base and stacks
    assert symbols['__bss_start'] <= symbols['__test_results'] < symbols['__bss_end']
    assert all(digest(Path(name)) == value for name, value in hashes.items()), 'Software sources changed during build'
    assert args.config.read_bytes() == configuration_bytes, 'Configuration changed during build'
    assert subprocess.check_output(['git', '-C', str(upstream), 'rev-parse', 'HEAD'], text=True).strip() == REVISION
    subprocess.run(['git', '-C', str(upstream), 'diff', '--exit-code', 'HEAD'], check=True, stdout=subprocess.DEVNULL)
    manifest = dict(sourceHashes=hashes, configurationHash=hashlib.sha256(configuration_bytes).hexdigest(),
        imageHash=digest(image), symbols=symbols, commands=commands,
        target=subprocess.check_output([args.tool_prefix + 'gcc', '-dumpmachine'], text=True).strip(),
        toolVersions={tool: subprocess.check_output([args.tool_prefix + tool, '--version'], text=True).splitlines()[0] for tool in ('gcc', 'ld', 'objdump')},
        upstreamRevision=REVISION, sdkMinimumVersion=(upstream / 'SDK_VERSION').read_text().strip(),
        generatedHashes={p.name: digest(p) for p in (dts, profile)}, timebaseHz=args.timebase_hz,
        console=dict(transport='uart' if args.qemu else 'word', base=console),
        layout=dict(kind='zephyr', entrySymbol='__start', entryAlias='_start', bssStart=symbols['__bss_start'],
                    bssEnd=symbols['__bss_end'], stacks=stacks),
        spinValidation=dict(enabled=harts <= 4, maximumHarts=4))
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(image)


if __name__ == '__main__':
    main()
