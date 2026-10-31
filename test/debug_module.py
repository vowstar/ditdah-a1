# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Exercise a shared execution-based debug module with real scalar cores."""

import argparse
import hashlib
import json
from pathlib import Path
import resource

from formal import module_ports
from model import Model
from programs import Program, addi, alu, csr, ld, lw, sd, sw
from verify import configuration, run


def software(config, output, ready_base=0x300):
    p = Program(0)
    for r in range(1, 32):
        p.emit(addi(r, 0, 0x100 + r))
    p.address(30, 0x10000)
    p.emit(lw(25, 30))
    p.address(30, 0x101a0)
    p.emit(sw(4, 30), csr(31, 0xf14, 0, True), alu(31, 31, 3, 1, immediate=True))
    p.address(30, ready_base)
    p.emit(alu(30, 30, 31, 0), addi(29, 0, 1), sd(29, 30))
    p.finish()
    (output / 'image.hex').write_text('@0\n' + '\n'.join(f'{p.memory.get(n, 0):02x}' for n in range(16384)) + '\n')
    expected = []
    for hart in range(config['hartCount']):
        model = Model(config, p.memory, p.faults, hart_id=hart)
        for _ in range(200):
            if model.pc == p.stop:
                break
            model.step()
        assert model.pc == p.stop and model.csrs[0x342] == 7
        expected += [f"    expected[{hart}][{r}] = 64'h{value:016x};" for r, value in enumerate(model.registers)]
    (output / 'debug_module_expected.svh').write_text('\n'.join(expected) + '\n')
    ready = ' && '.join(f"memory['h{ready_base+8*h:x}] == 1" for h in range(config['hartCount']))
    return p.stop, ready


def commands(loop):
    body = f'''    select_hart(0);
    put('h20, 32'h{csr(13, 0x7b1, 0, True):08x}); put('h21, 'h00100073); execute();
    read_gpr(13, value64); check(value64 == 'h{loop:x}, "DPC identifies the stopped normal instruction");
    put('h20, 32'h{csr(13, 0x342, 0, True):08x}); execute();
    read_gpr(13, value64); check(value64 == 7, "Debug execution preserves normal trap state");
    write_gpr(10, 'h600); write_gpr(11, 64'hdeadc0de12345678);
    put('h20, 32'h{sd(11, 10):08x}); put('h21, 32'h{ld(12, 10):08x}); put('h22, 'h00100073); execute();
    read_gpr(12, value64); check(value64 == 64'hdeadc0de12345678, "Program Buffer uses the real LSU and ordinary memory");
    put('h17, 'h3207b0); complete_command(2); put('h16, 'h700);
    @(negedge clock); memory_stall = 1;
    put('h17, 'h321008); get('h16, value); check(value[12], "Command remains active under memory backpressure");
    select_hart(HARTS == 1 ? 0 : 1); get('h10, value); check(value[25:16] == 0, "Busy command keeps its selected hart");
    put(4, 'h11111111); put('h20, 'h11111111);
    @(negedge clock); memory_stall = 0; complete_command(1);
    get('h20, value); check(value == 32'h{sd(11, 10):08x}, "Busy writes cannot replace the Program Buffer");
    get(4, value); check(value == expected[0][8][31:0], "Busy data writes cannot replace a running transfer");
    put('h16, 'h700);
    put('h20, 'hffffffff); put('h17, 'h40000); complete_command(3); put('h16, 'h700);
    read_gpr(8, value64); check(value64 == expected[0][8], "Program Buffer exception preserves the park-loop register");
    put('h20, 32'h{csr(13, 0x7b0, 0, True):08x}); put('h21, 32'h{alu(13, 13, 4, 6, immediate=True):08x});
    put('h22, 32'h{csr(0, 0x7b0, 13):08x}); put('h23, 'h00100073); execute();
    select_hart(0, 'h40000000);
    do get('h11, value); while (!value[17] || !value[9]);
    put('h20, 32'h{csr(13, 0x7b0, 0, True):08x}); put('h21, 'h00100073); execute();
    read_gpr(13, value64); check(value64[8:6] == 4, "Resume with step executes one ordinary instruction");
    put('h20, 32'h{alu(13, 13, -5, 7, immediate=True):08x}); put('h21, 32'h{csr(0, 0x7b0, 13):08x});
    put('h22, 'h00100073); execute();
    for (integer hart = 0; hart < HARTS; hart++) begin
      select_hart(hart, 'h40000000);
      do get('h11, value); while (!value[17] || !value[11]);
      select_hart(hart, 'h90000000); do get('h11, value); while (!value[9]);
      check(value[19:18] == 0, "Initial reset indication was acknowledged");
      read_gpr(8, value64); check(value64 == expected[hart][8], "Shared commands preserve other hart state");
    end
'''
    body += '''    if (HARTS == 3) begin
      select_hart(3); get('h11, value); check(value[15:14] == 3, "Nonexistent hart is discoverable");
      put('h17, 'h321000); complete_command(4); put('h16, 'h700);
    end
    for (integer hart = 0; hart < HARTS; hart++) select_hart(hart, 'h80000000);
    put(4, 'h12345678); put('h27, 'h55555555); put('h10, ((HARTS-1) << 16) | 'h80000003);
    get('h11, value); check(!value[24] && value[13:12] == 3, "Non-debug reset leaves the debug module accessible");
    put('h10, ((HARTS-1) << 16) | 'h80000001);
    get(4, value); check(value == 'h12345678, "Non-debug reset retains debug data");
    get('h27, value); check(value == 'h55555555, "Non-debug reset retains Program Buffer contents");
'''
    body += f'''    for (integer hart = 0; hart < HARTS; hart++) begin
      select_hart(hart, 'h80000000); do get('h11, value); while (!value[9]);
      check(value[19:18] == 3, "Reset is recorded for each hart");
      put('h20, 32'h{csr(13, 0x7b1, 0, True):08x}); put('h21, 'h00100073); execute();
      read_gpr(13, value64); check(value64 == 0, "Reset halt precedes the first ordinary instruction");
      select_hart(hart, 'h10000000); get('h11, value); check(value[19:18] == 0, "Reset acknowledgement is per hart");
    end
'''
    return body


def main():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    parser = argparse.ArgumentParser()
    parser.add_argument('--harts', type=int, choices=(1, 3, 16), required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--use-generated', action='store_true')
    args = parser.parse_args()
    output = args.output
    output.mkdir(parents=True, exist_ok=True)
    inputs = ('test/debug_module.py', 'test/debug_module_tb.sv', 'test/memory_port.svh', 'test/model.py', 'test/programs.py', 'test/verify.py', 'test/formal.py')
    hashes = {p: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in inputs}
    config = dict(configuration(64), enableJtag=True, debugBase='65536', hartCount=args.harts,
                  issueWidth=1 if args.harts == 1 else 3, enableC=args.harts == 3,
                  enableM=False, enableA=False)
    path = output / 'input.json'
    path.write_text(json.dumps(config, indent=2) + '\n')
    files, manifests = {}, {}
    for name, top in [('module', 'DitDahA1DebugModule'), ('core', 'DitDahA1Core'), ('arbiter', 'DitDahA1MemoryArbiter')]:
        rtl = output / name
        if not args.use_generated:
            run(['build-ditdah-a1', '--top', top, '--config', path, '--output', rtl], output / f'{name}-build.log')
        m = json.loads((rtl / 'ditdah_a1_config.json').read_text())
        assert m['top'] == top and m['parameters']['hartCount'] == args.harts
        assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in m['sourceHashes'].items())
        manifests[name] = m
        for p in (rtl / 'filelist.f').read_text().splitlines():
            assert p not in files or files[p].read_bytes() == (rtl / p).read_bytes()
            files[p] = (rtl / p).resolve()
    bindings = ['.clock(clock)', '.reset(reset)', '.hartsReset(core_reset)', '.ndmreset(ndmreset)',
                '.memoryHart(owner)', '`PORT(memory, debug_memory)']
    for _, _, p in module_ports(files['DitDahA1DebugModule.sv'].read_text()):
        if p.startswith('dmi_'):
            bindings.append(f'.{p}({p})')
    for hart in range(args.harts):
        for field, signal in [('mode', 'debug_mode'), ('haltReq', 'halt_req'), ('entryPc', 'debug_entry'), ('exceptionPc', 'debug_exception')]:
            bindings.append(f'.harts_{hart}_{field}({signal}[{hart}])')
    declaration = 'DitDahA1DebugModule dm(' + ',\n'.join(bindings) + ');\n'
    bindings = ['.clock(clock)', '.reset(core_reset)', '.hartId(owner)', '`PORT(downstream, shared)']
    bindings += [f'`PORT(ports_{n}, client[{n}])' for n in range(2 * args.harts)]
    declaration += 'DitDahA1MemoryArbiter arbiter(' + ',\n'.join(bindings) + ');\n'
    (output / 'debug_module_bindings.svh').write_text(declaration)
    loop, ready = software(config, output)
    (output / 'debug_module_commands.svh').write_text(commands(loop))
    binary = (output / 'native/Vdebug_module_tb').resolve()
    run(['verilator', '--binary', '--timing', '--assert', '-j', '2', '--top-module', 'debug_module_tb', '-Wno-fatal',
         '-DDEBUG_MEMORY', f'-DHARTS={args.harts}', f'-DSELECT_MASK={(1 << (args.harts - 1).bit_length()) - 1}', f'-DREADY_HARTS=({ready})',
         '-I' + str(output.resolve()), '-I' + str(Path('test').resolve()), '--Mdir', binary.parent,
         *files.values(), Path('test/debug_module_tb.sv')], output / 'compile.log')
    run([binary, '+IMAGE=' + str((output / 'image.hex').resolve())], output / 'run.log', timeout=120)
    text = (output / 'run.log').read_text()
    assert 'PASS\n' in text and text.count('register access passed') == args.harts
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in hashes.items())
    (output / 'summary.json').write_text(json.dumps(dict(manifests=manifests, testSourceHashes=hashes,
        scope='DMI, shared module, real cores and serialized memory arbiter; Bare without private caches or PMP; routing belongs to the fixture, debug origin is captured in the real fetch and LSU',
        harts=args.harts, normalProgramCounter=loop, expectedNormalFaults=2*args.harts), indent=2) + '\n')
    print(f'Debug module checks passed: {args.harts} real harts')


if __name__ == '__main__':
    main()
