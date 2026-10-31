# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Build the processor with boot storage, application RAM and serial output."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--config', type=Path, default=Path('software/platform.json'))
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--harts', type=int, choices=range(1, 17))
    parser.add_argument('--clock-hz', type=int, required=True)
    parser.add_argument('--baud', type=int, default=115200)
    parser.add_argument('--timebase-hz', type=int, default=1000000)
    parser.add_argument('--jtag-idcode', type=lambda x: int(x, 0), required=True)
    args = parser.parse_args()
    assert 0 < args.baud <= args.clock_hz <= 1000000000 and 0 < args.timebase_hz <= args.clock_hz
    assert args.clock_hz % args.timebase_hz == 0
    bit_cycles = (args.clock_hz + args.baud//2)//args.baud
    assert abs(args.clock_hz - args.baud*bit_cycles)*100 <= 2*args.baud*bit_cycles, 'Serial baud error exceeds two percent'
    paths = [args.config, Path(__file__), Path('rtl/DitDahA1PlatformMemory.sv')]
    hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    config = json.loads(args.config.read_text())
    config = config.get('parameters', config)
    ram = next(r for r in config['memoryRegions'] if int(r['base']) == int(config['resetVector']) and
               not r['device'] and r['readable'] and r['writable'] and r['executable'])
    console, = [r for r in config['memoryRegions'] if r['device'] and r['writable'] and not r['readable']]
    assert config['physicalAddressBits'] == 32 and config['axiDataBits'] == 64
    assert config['enableInterrupts'] and config.get('localInterruptBase') is not None
    assert int(ram['base']) % 8 == 0 and int(ram['size']) % 8 == 0
    config.update(resetVector='4096', enableJtag=True, debugBase='65536',
                  jtagIdcode=args.jtag_idcode, enableTrace=False)
    if args.harts is not None:
        config['hartCount'] = args.harts
    config['memoryRegions'].append(dict(base='4096', size='4096', readable=True, writable=False,
                                       executable=True, device=False, atomic=False, dataCacheable=False))
    root = args.output.resolve()
    root.mkdir(parents=True, exist_ok=True)
    (root / 'manifest.json').unlink(missing_ok=True)
    (root / 'input.json').write_text(json.dumps(config, indent=2)+'\n')
    subprocess.run(['python3', 'scripts/build_rtl.py', '--config', root / 'input.json', '--no-trace', '--output', root], check=True)
    cpu = json.loads((root / 'ditdah_a1_config.json').read_text())
    ports, direction, width = [], None, ''
    header = (root / 'DitDahA1.sv').read_text().split('module DitDahA1(', 1)[1].split(');', 1)[0]
    for item in header.split(','):
        match = re.fullmatch(r'\s*(?:(input|output)\s+)?(\[\d+:\d+\])?\s*(\w+)\s*', item)
        assert match, item
        new_direction, new_width, name = match.groups()
        if new_direction:
            direction, width = new_direction, new_width or ''
        ports.append((direction, width, name))
    external = {'clock', 'reset', 'systemReset', 'systemResetActive', 'jtag_tck', 'jtag_trstN',
                'jtag_tms', 'jtag_tdi', 'jtag_tdo', 'jtag_tdoEnable'}
    text = '// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>\n// SPDX-License-Identifier: MIT\n'
    text += 'module DitDahA1Platform(\n' + ',\n'.join(
        f'  {direction} wire {width} {name}' for direction, width, name in ports if name in external)
    text += ',\n  output wire tx\n);\n'
    text += ''.join(f'  wire {width} {name};\n' for _, width, name in ports if name not in external)
    for direction, _, name in ports:
        if direction == 'input' and name not in external and not name.startswith('axi_') and name != 'timeTick':
            assert name.startswith('interrupts_'), name
            text += f"  assign {name} = '0;\n"
    text += '  DitDahA1 processor (.*);\n'
    id_width = next(width for _, width, name in ports if name == 'axi_ar_bits_id')
    parameters = dict(ID_BITS=int(id_width[1:].split(':')[0])+1 if id_width else 1, HARTS=config['hartCount'],
                      ENABLE_A=int(config.get('enableA', True)), RAM_BASE=int(ram['base']),
                      RAM_BYTES=int(ram['size']), CONSOLE_BASE=int(console['base']), CLOCK_HZ=args.clock_hz,
                      BAUD=args.baud, TIMEBASE_HZ=args.timebase_hz)
    text += '  DitDahA1PlatformMemory #(\n' + ',\n'.join(f'    .{k}({v})' for k, v in parameters.items())
    text += '\n  ) memory (.reset(systemResetActive), .*);\nendmodule\n'
    (root / 'DitDahA1Platform.sv').write_text(text)
    shutil.copy2('rtl/DitDahA1PlatformMemory.sv', root / 'DitDahA1PlatformMemory.sv')
    with (root / 'filelist.f').open('a') as stream:
        stream.write('DitDahA1PlatformMemory.sv\nDitDahA1Platform.sv\n')
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == digest for p, digest in hashes.items())
    (root / 'manifest.json').write_text(json.dumps(dict(sourceHashes=hashes, processor=cpu,
        parameters=parameters, clockHz=args.clock_hz, timebaseHz=args.timebase_hz,
        baud=args.baud, serialBitCycles=bit_cycles, applicationEntry=int(ram['base'])), indent=2)+'\n')


if __name__ == '__main__':
    main()
