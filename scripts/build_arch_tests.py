# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Build selected scalar self-checking executables for one machine-mode hart."""

import argparse
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

REVISION = '6e8a45123f14cebfb3df151a0e7b849b4389b33b'
ARCHITECTURE = 'rv64i2p1_zicsr2p0_zifencei2p0'
M_ARCHITECTURE = 'rv64i2p1_m2p0_zicsr2p0_zifencei2p0_zmmul1p0'
A_ARCHITECTURES = {name: ARCHITECTURE + '_' + name.lower() + '1p0' for name in ('Zaamo', 'Zalrsc')}
C_ARCHITECTURE = ARCHITECTURE + '_zca1p0'
B_ARCHITECTURES = {name: ARCHITECTURE + '_' + name.lower() + '1p0' for name in ('Zba', 'Zbb', 'Zbs')}
FP_ARCHITECTURES = {'F': 'rv64i2p1_f2p2_zicsr2p0_zifencei2p0', 'D': 'rv64i2p1_f2p2_d2p2_zicsr2p0_zifencei2p0',
                    'Zcd': 'rv64i2p1_f2p2_d2p2_zicsr2p0_zifencei2p0_zca1p0_zcd1p0'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def instructions(data, start, end, compressed=False):
    address = start
    while address < end:
        size = 4 if int.from_bytes(data[address:address + 2], 'little') & 3 == 3 else 2
        assert address % (2 if compressed else 4) == 0 and (size == 4 or compressed) and address + size <= end, 'Invalid instruction boundary or unsupported compressed encoding'
        yield address, int.from_bytes(data[address:address + size], 'little')
        address += size


def code_spans(elf, architecture=ARCHITECTURE, mapped_architectures=()):
    attributes = elf.get_section_by_name('.riscv.attributes')
    assert attributes is not None, 'Missing instruction architecture attributes'
    architectures = [a.value for sub in attributes.iter_subsections() for group in sub.iter_subsubsections()
                     for a in group.iter_attributes() if a.tag == 'TAG_ARCH']
    assert architectures == [architecture], 'Unsupported instruction architecture'
    mapping_profiles = (('rv64i2p1_f2p2_zicsr2p0',) if architecture in FP_ARCHITECTURES.values() else ()) + ((FP_ARCHITECTURES['D'],) if architecture == FP_ARCHITECTURES['Zcd'] else ())
    table, spans = elf.get_section_by_name('.symtab'), []
    assert table is not None, 'Missing code mapping symbols'
    for index, section in enumerate(elf.iter_sections()):
        if not section['sh_flags'] & 4 or not section['sh_size']:
            continue
        start, data = section['sh_addr'], section.data()
        markers = sorted((s['st_value'], s.name) for s in table.iter_symbols()
                         if s['st_shndx'] == index and (s.name.startswith('$x') or s.name == '$d'))
        assert markers and markers[0][0] == start, 'Unmapped executable section'
        for (address, name), (end, _) in zip(markers, [*markers[1:], (start + len(data), '$d')]):
            assert start <= address <= end <= start + len(data), 'Invalid code mapping bounds'
            if not name.startswith('$x') or address == end:
                continue
            compressed = '_c2p0' in architecture or '_zca1p0' in architecture
            assert address % (2 if compressed else 4) == 0
            words = [word for _, word in instructions(data, address - start, end - start, compressed)]
            if '_zca1p0' not in name and '_c2p0' not in name:
                assert all(word & 3 == 3 or compressed and word == 1 for word in words), 'Compressed encoding in an uncompressed code mapping'
            assert name[2:] in (architecture, *mapped_architectures, *mapping_profiles, *((ARCHITECTURE,) if architecture == C_ARCHITECTURE or architecture == FP_ARCHITECTURES['Zcd'] else ())) or all(word == 0x13 or compressed and word == 1 for word in words), 'Unsupported code mapping architecture'
            spans.append(dict(section=section.name, start=address, end=end, architecture=name[2:]))
    assert spans, 'Missing executable code mappings'
    return spans


def main():
    from elftools.elf.elffile import ELFFile
    import pyjson5
    from ruamel.yaml import YAML

    parser = argparse.ArgumentParser()
    parser.add_argument('--extensions', nargs='+', choices=('I', 'M', 'Zaamo', 'Zalrsc', 'Zca', *B_ARCHITECTURES, *FP_ARCHITECTURES), default=['I'])
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=Path('result/arch-test'))
    parser.add_argument('--arch-test-dir', type=Path, default=os.environ.get('ARCH_TEST_DIR'))
    parser.add_argument('--sail', default=os.environ.get('SAIL_RISCV_SIM', 'sail_riscv_sim'))
    parser.add_argument('--tool-prefix', default=os.environ.get('RISCV_PREFIX', 'riscv64-unknown-elf-'))
    parser.add_argument('--console-base', type=lambda value: int(value, 0), required=True)
    args = parser.parse_args()
    output, source = args.output.resolve(), Path('software/arch-test')
    output.mkdir(parents=True, exist_ok=True)
    (output / 'manifest.json').unlink(missing_ok=True)
    for old in output.glob('*/manifest.json'):
        old.unlink()
    assert args.arch_test_dir is not None, 'Set ARCH_TEST_DIR or --arch-test-dir'
    upstream = args.arch_test_dir.resolve()
    def clean_revision():
        assert subprocess.check_output(['git', '-C', str(upstream), 'rev-parse', 'HEAD'], text=True).strip() == REVISION
        assert not subprocess.check_output(['git', '-C', str(upstream), 'status', '--porcelain'], text=True).strip(), 'Architecture test source changed'
    clean_revision()
    assert importlib.metadata.version('act') == '0.3.0', 'Unsupported architecture test tool version'
    assert subprocess.check_output([args.sail, '--version'], text=True).strip() == '0.13.1'
    configuration = args.config.read_bytes()
    document = json.loads(configuration)
    config = document.get('parameters', document)
    base, console = int(config['resetVector']), args.console_base
    extensions = tuple(sorted(set(args.extensions)))
    assert len(extensions) == len(args.extensions), 'Duplicate extension selection'
    platform_name = 'ditdah-a1-' + hashlib.sha256(configuration + ','.join(extensions).encode()).hexdigest()[:12]
    assert 'M' not in extensions or config.get('enableM', True), 'M tests require enabled arithmetic'
    atomic = bool(set(extensions) & A_ARCHITECTURES.keys())
    assert not atomic or config.get('enableA', True), 'Atomic tests require enabled A'
    assert 'Zca' not in extensions or config.get('enableC'), 'Compressed tests require enabled C'
    fp = bool(set(extensions) & FP_ARCHITECTURES.keys())
    double = bool(set(extensions) & {'D', 'Zcd'})
    assert not fp or config.get('floatingPointBits', 0) >= (64 if double else 32), 'Floating tests require enabled precision'
    assert 'Zcd' not in extensions or config.get('enableC'), 'Compressed floating tests require C'
    assert all(config.get('enable' + name) for name in set(extensions) & B_ARCHITECTURES.keys()), 'Bit manipulation tests require enabled extensions'
    assert config['hartCount'] == 1 and config['pmpEntries'] == 0 and not config['virtualAddressBits']
    ram = next(r for r in config['memoryRegions'] if int(r['base']) == base and r['readable'] and r['writable'] and r['executable'] and not r['device'])
    assert int(ram['size']) >= 0x80000 and not base <= console < base + int(ram['size'])
    assert console % 4 == 0 and any(r['device'] and r['writable'] and not r['executable'] and not r['atomic'] and int(r['base']) <= console and console + 4 <= int(r['base']) + int(r['size']) for r in config['memoryRegions'])
    paths = [*sorted(source.iterdir()), Path(__file__), *sorted((upstream / 'tests/env').glob('*.*')),
             *(p for extension in extensions for p in sorted((upstream / 'tests/rv64i' / extension).glob('*.S')))]
    hashes = {str(p): digest(p) for p in paths if p.is_file()}
    platform = output / 'platform'
    platform.mkdir(exist_ok=True)
    shutil.copyfile(source / 'rvmodel_macros.h', platform / 'rvmodel_macros.h')
    linker = platform / 'link.ld'
    linker.write_text(f'__ram_base = {base};\n__ram_bytes = {int(ram["size"])};\n__console_base = {console};\n' + (source / 'link.ld').read_text())
    udb = YAML(typ='safe').load((source / 'rv64-integer.yaml').read_text())
    udb['name'] = platform_name
    udb['params']['PHYS_ADDR_WIDTH'] = config['physicalAddressBits']
    if 'M' in extensions:
        udb['implemented_extensions'] += [dict(name='M', version='= 2.0'), dict(name='Zmmul', version='= 1.0')]
        udb['params']['MUTABLE_MISA_M'] = False
    if atomic:
        udb['implemented_extensions'] += [dict(name=name, version=version) for name, version in (('A', '= 2.1'), ('Zaamo', '= 1.0'), ('Zalrsc', '= 1.0'))]
        udb['params'].update(MISALIGNED_AMO=False, MUTABLE_MISA_A=False, LRSC_FAIL_ON_VA_SYNONYM=False, LRSC_FAIL_ON_NON_EXACT_LRSC=True,
                             LRSC_RESERVATION_STRATEGY='reserve exactly enough to cover the access', LRSC_MISALIGNED_BEHAVIOR='always raise misaligned exception')
    if set(extensions) & {'Zca', 'Zcd'}:
        udb['implemented_extensions'] += [dict(name='C', version='= 2.0'), dict(name='Zca', version='= 1.0')]
        udb['params']['MUTABLE_MISA_C'] = False
    udb['implemented_extensions'] += [dict(name=name, version='= 1.0') for name in extensions if name in B_ARCHITECTURES]
    if fp:
        udb['implemented_extensions'] += [dict(name='F', version='= 2.2')] + ([dict(name='D', version='= 2.2')] if double else [])
        udb['params'].update(MUTABLE_MISA_F=False, HW_MSTATUS_FS_DIRTY_UPDATE='precise', MSTATUS_FS_LEGAL_VALUES=[0, 1, 2, 3])
        if double: udb['params']['MUTABLE_MISA_D'] = False
        if 'Zcd' in extensions: udb['implemented_extensions'] += [dict(name='Zcd', version='= 1.0')]
    (platform / 'udb.json').write_text(json.dumps(udb, indent=2) + '\n')
    sail = pyjson5.loads(subprocess.check_output([args.sail, '--print-default-config'], text=True))
    def disable(node):
        if isinstance(node, dict):
            for key, value in node.items():
                if key == 'supported': node[key] = False
                elif key == 'support_level': node[key] = 'Disabled'
                else: disable(value)
    disable(sail['extensions'])
    for name in ('Zicsr', 'Zifencei'): sail['extensions'][name]['supported'] = True
    if 'M' in extensions:
        sail['extensions']['M']['supported'] = True
        sail['extensions']['Zmmul']['supported'] = True
    if atomic:
        for name in ('A', 'Zaamo', 'Zalrsc'): sail['extensions'][name]['supported'] = True
        sail['memory']['misaligned']['exceptions'].update(amo=dict(Some='AlignmentException'), lrsc='AlignmentException')
        sail['platform']['reservation'].update(require_exact_reservation_addr=True, invalidate_on_same_hart_store=True)
    if set(extensions) & {'Zca', 'Zcd'}:
        sail['extensions']['Zca']['supported'] = True
    for name in set(extensions) & B_ARCHITECTURES.keys(): sail['extensions'][name]['supported'] = True
    if fp:
        sail['extensions']['F']['supported'] = True
        if double: sail['extensions']['D']['supported'] = True
        if 'Zcd' in extensions: sail['extensions']['Zcd']['supported'] = True
    sail['base']['writable_misa'] = False
    sail['base']['mtvec']['vectored']['supported'] = False
    sail['base']['privileged_isa_version'] = 'Privileged_ISA_1_12'
    sail['base']['mstatus'] = {key: 'ExtContext_Off' for key in sail['base']['mstatus']}
    if fp: sail['base']['mstatus']['fs_legal_states'] = 'ExtContext_FourState'
    sail['memory']['physaddr_bits'] = config['physicalAddressBits']
    sail['memory']['pmp'].update(count=0, usable_count=0)
    sail['memory']['misaligned']['exceptions']['load_store'] = dict(Some='AlignmentException')
    memory = sail['memory']['regions'][-1]
    memory['base']['value'], memory['size']['value'] = hex(base), hex(int(ram['size']))
    memory['attributes']['misaligned_exceptions']['load_store'] = dict(Some='AlignmentException')
    memory['attributes'].update(atomic_support='AMONone', reservability='RsrvNone', supports_cbo_zero=False,
                                supports_pte_read=False, supports_pte_write=False)
    if atomic:
        memory['attributes'].update(atomic_support='AMOArithmetic', reservability='RsrvEventual')
        memory['attributes']['misaligned_exceptions']['amo'] = 'AlignmentException'
    (platform / 'sail.json').write_text(json.dumps(sail, indent=2) + '\n')
    test_config = dict(name=platform_name, compiler_exe=args.tool_prefix + 'gcc', objdump_exe=args.tool_prefix + 'objdump',
                       ref_model_exe=args.sail, udb_config='udb.json', linker_script='link.ld', dut_include_dir='.', include_priv_tests=False)
    (platform / 'test_config.json').write_text(json.dumps(test_config, indent=2) + '\n')
    command = [sys.executable, '-m', 'act.act', str(platform / 'test_config.json'), '--test-dir', str(upstream / 'tests'),
               '--coverpoint-dir', str(upstream / 'coverpoints'), '--workdir', str(output / 'act'), '--extensions', ','.join(extensions), '--jobs', '2']
    with (output / 'build.log').open('w') as log:
        subprocess.run(command, check=True, stdout=log, stderr=subprocess.STDOUT, timeout=600)
    generated = {str(p.relative_to(output)): digest(p) for p in [*platform.iterdir(), *(output / f'act/{platform_name}').glob('*.h')] if p.is_file()}
    reports, manifests = [], []
    for image in sorted(p for extension in extensions for p in (output / f'act/{platform_name}/elfs/rv64i' / extension).glob('*.elf')):
        architecture = C_ARCHITECTURE if image.parent.name == 'Zca' else M_ARCHITECTURE if image.parent.name == 'M' else (A_ARCHITECTURES | B_ARCHITECTURES | FP_ARCHITECTURES).get(image.parent.name, ARCHITECTURE)
        target = output / image.stem
        target.mkdir(exist_ok=True)
        shutil.copyfile(image, target / 'software.elf')
        with image.open('rb') as stream:
            elf = ELFFile(stream)
            table = elf.get_section_by_name('.symtab')
            symbols = {s.name: s['st_value'] for s in table.iter_symbols() if s['st_info']['bind'] in ('STB_GLOBAL', 'STB_WEAK') and s['st_shndx'] != 'SHN_UNDEF'}
            all_symbols = {s.name: s['st_value'] for s in table.iter_symbols()}
            spans, table_hash = code_spans(elf, architecture), hashlib.sha256(table.data()).hexdigest()
        assert base <= symbols['__bss_start'] <= symbols['__test_results'] < symbols['__bss_end'] <= symbols['__stack_bottom'] < symbols['__stack_top'] <= base + int(ram['size'])
        reference = output / f'act/{platform_name}/build/rv64i' / image.parent.name / image.stem
        assert 'SUCCESS' in Path(str(reference) + '.sig.log').read_text()
        with Path(str(reference) + '.sig.elf').open('rb') as stream:
            reference_symbols = {s.name: s['st_value'] for s in ELFFile(stream).get_section_by_name('.symtab').iter_symbols()}
        assert all(all_symbols.get(name) == reference_symbols.get(name) for name in
                   ('rvtest_code_begin', 'rvtest_code_end', 'scratch', 'begin_signature', 'end_signature', 'signature_base')), 'Reference test addresses differ'
        manifest = dict(profile='arch-test', testInstruction=image.stem.split('-')[1], requiredExtensions=['C', 'F', 'D'] if image.parent.name == 'Zcd' else ['C'] if image.parent.name == 'Zca' else ['F', 'D'] if image.parent.name == 'D' else [image.parent.name] if image.parent.name in (*B_ARCHITECTURES, 'F') else [], instructionArchitecture=architecture, sourceHashes=hashes, configurationHash=hashlib.sha256(configuration).hexdigest(),
            imageHash=digest(image), symbols=symbols, codeSpans=spans, symbolTableHash=table_hash, commands=[command],
            upstreamRevision=REVISION, generatedHashes=generated, referenceHashes={suffix: digest(Path(str(reference) + suffix)) for suffix in ('.sig.elf', '.sig', '.results', '.sig.log')},
            toolVersions={tool: subprocess.check_output([tool, '--version'], text=True).splitlines()[0] for tool in (args.sail, args.tool_prefix + 'gcc', args.tool_prefix + 'ld', args.tool_prefix + 'objdump')},
            console=dict(transport='word', base=console), expectedConsole=[f'\nRVCP-SUMMARY: TEST PASSED - Test File "{image.stem}.S"\n\n'],
            layout=dict(kind='arch-test', entrySymbol='rvtest_entry_point', entryAlias='_start', bssStart=symbols['__bss_start'], bssEnd=symbols['__bss_end'],
                        stacks=[dict(symbol='__stack_bottom', address=symbols['__stack_bottom'], size=symbols['__stack_bytes'], count=1, stride=symbols['__stack_bytes'])]))
        manifests.append((target, manifest))
    assert len(manifests) == sum({'I': 51, 'M': 13, 'Zaamo': 18, 'Zalrsc': 4, 'Zca': 32, 'Zba': 8, 'Zbb': 24, 'Zbs': 8, 'F': 82, 'D': 114, 'Zcd': 4}[extension] for extension in extensions), 'Unexpected architecture test selection'
    assert args.config.read_bytes() == configuration and all(digest(Path(p)) == h for p, h in hashes.items()), 'Build inputs changed'
    clean_revision()
    for target, manifest in manifests:
        (target / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        reports.append(dict(test=target.name, manifestHash=digest(target / 'manifest.json')))
    (output / 'manifest.json').write_text(json.dumps(dict(scope='selected scalar self-checking images; not full ISA compliance', tests=reports), indent=2) + '\n')


if __name__ == '__main__':
    main()
