# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Exercise production debug wiring through JTAG and external debug tools."""

import argparse
from collections import deque
import hashlib
import json
import os
import re
from pathlib import Path
import socket
import shutil
import subprocess
import time
import xml.etree.ElementTree as ET

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge, Timer

from debug_module import software
from formal import module_ports
from model import Model
from programs import csr, ld, sd
from verify import configuration, run


class Jtag:
    def __init__(self, dut):
        self.dut = dut

    async def cycle(self, tms, tdi=0):
        d = self.dut
        d.jtag_tms.value, d.jtag_tdi.value = int(tms), tdi
        await Timer(10, unit='ns')
        value = int(d.jtag_tdo.value)
        d.jtag_tck.value = 1
        await Timer(10, unit='ns')
        d.jtag_tck.value = 0
        await Timer(10, unit='ns')
        return value

    async def idle(self, count=32):
        for _ in range(count):
            await self.cycle(0)

    async def scan(self, value, width, instruction=False):
        await self.cycle(1)
        if instruction:
            await self.cycle(1)
        await self.cycle(0)
        await self.cycle(0)
        result = 0
        for bit in range(width):
            result |= await self.cycle(bit == width-1, value >> bit & 1) << bit
        await self.cycle(1)
        await self.cycle(0)
        return result

    async def reset(self):
        for _ in range(6):
            await self.cycle(1)
        await self.cycle(0)

    async def access(self, op, address, data=0):
        await self.scan(17, 5, True)
        await self.scan(address << 34 | data << 2 | op, 41)
        for _ in range(100):
            await self.idle()
            reply = await self.scan(0, 41)
            if reply & 3 != 3:
                assert reply & 3 == 0, f'DMI status at {address:x}: {reply:x}'
                return reply >> 2 & 0xffffffff
            await self.scan(16, 5, True)
            await self.scan(1 << 16, 32)
            await self.scan(17, 5, True)
        raise AssertionError('DMI did not complete')

    async def command(self, value):
        await self.access(2, 0x17, value)
        for _ in range(200):
            status = await self.access(1, 0x16)
            if not status & (1 << 12):
                return status >> 8 & 7
        raise AssertionError('Abstract command did not complete')

    async def register(self, index, value=None):
        if value is not None:
            await self.access(2, 4, value & 0xffffffff)
            await self.access(2, 5, value >> 32)
        assert await self.command(0x321000 | index | (int(value is not None) << 16)) == 0
        return await self.access(1, 4) | await self.access(1, 5) << 32

    async def hart(self, index, resume=False):
        await self.access(2, 0x10, 1 | index << 16 | 1 << (30 if resume else 31))
        for _ in range(200):
            status = await self.access(1, 0x11)
            if status & (1 << (10 if resume else 9)):
                return status
        raise AssertionError(f'Hart {index} did not {"resume" if resume else "halt"}')

    async def memory(self, address, value=None):
        await self.register(10, address)
        if value is not None:
            await self.register(11, value)
        assert await self.program(sd(11, 10) if value is not None else ld(12, 10)) == 0
        if value is None:
            return await self.register(12)

    async def program(self, *words):
        for index, word in enumerate((*words, 0x00100073)):
            await self.access(2, 0x20 + index, word)
        return await self.command(1 << 18)


async def memory_service(dut, memory, debug_base):
    reads, writes, payloads = deque(), deque(), deque()
    beat = None
    write_reply = None
    cycles = 0
    def get(name):
        return int(getattr(dut, 'axi_' + name).value)
    def put(name, value):
        getattr(dut, 'axi_' + name).value = value
    while True:
        await FallingEdge(dut.clock)
        reset = int(dut.systemResetActive.value)
        if reset:
            reads.clear(); writes.clear(); payloads.clear()
            beat = write_reply = None
        if beat is None and reads:
            address, ident, size, remaining = reads[0]
            aligned = address & -8
            data = sum(memory.get(aligned+n, 0) << (8*n) for n in range(8))
            beat = (data, ident, int(remaining == 0))
        for name, value in dict(ar_ready=not reset and cycles % 3 != 0,
                                aw_ready=not reset and cycles % 5 != 0,
                                w_ready=not reset and cycles % 7 != 0,
                                r_valid=not reset and beat is not None,
                                r_bits_data=beat[0] if beat else 0,
                                r_bits_id=beat[1] if beat else 0,
                                r_bits_last=beat[2] if beat else 0, r_bits_resp=0,
                                b_valid=not reset and write_reply is not None,
                                b_bits_id=write_reply or 0, b_bits_resp=0).items():
            put(name, int(value))
        await RisingEdge(dut.clock)
        if reset:
            continue
        cycles += 1
        if get('r_valid') and get('r_ready'):
            address, ident, size, remaining = reads.popleft()
            if remaining:
                reads.appendleft((address + (1 << size), ident, size, remaining-1))
            beat = None
        if get('b_valid') and get('b_ready'):
            write_reply = None
        if get('ar_valid') and get('ar_ready'):
            address = get('ar_bits_addr')
            assert not debug_base <= address < debug_base+4096, 'Debug request escaped to AXI'
            reads.append((address, get('ar_bits_id'), get('ar_bits_size'), get('ar_bits_len')))
        if get('aw_valid') and get('aw_ready'):
            address = get('aw_bits_addr')
            assert not debug_base <= address < debug_base+4096, 'Debug write escaped to AXI'
            assert get('aw_bits_len') == 0 and not get('aw_bits_lock')
            writes.append((address & -8, get('aw_bits_id')))
        if get('w_valid') and get('w_ready'):
            assert get('w_bits_last')
            payloads.append((get('w_bits_data'), get('w_bits_strb')))
        if writes and payloads and write_reply is None:
            address, write_reply = writes.popleft()
            data, mask = payloads.popleft()
            for n in range(8):
                if mask >> n & 1:
                    memory[address+n] = data >> (8*n) & 255


async def remote_bitbang(dut, listener):
    connection = None
    try:
        while connection is None:
            try:
                connection, _ = listener.accept()
                connection.setblocking(False)
                connection.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            except BlockingIOError:
                time.sleep(0.0001)
                await Timer(100, unit='ns')
        while True:
            try:
                payload = connection.recv(4096)
            except BlockingIOError:
                time.sleep(0.0001)
                await Timer(100, unit='ns')
                continue
            if not payload:
                return
            for value in payload:
                if 48 <= value <= 55:
                    bits = value-48
                    dut.jtag_tck.value, dut.jtag_tms.value, dut.jtag_tdi.value = bits >> 2, bits >> 1 & 1, bits & 1
                elif value == ord('R'):
                    connection.sendall(b'1' if int(dut.jtag_tdo.value) else b'0')
                elif ord('r') <= value <= ord('u'):
                    bits = value-ord('r')
                    dut.jtag_trstN.value, dut.systemReset.value = int(not bits & 2), bits & 1
                elif value == ord('Q'):
                    return
                await Timer(10, unit='ns')
    finally:
        if connection:
            connection.close()


async def process_done(process, timeout=120):
    deadline = time.monotonic() + timeout
    while process.poll() is None:
        assert time.monotonic() < deadline, 'External debug tool timed out'
        time.sleep(0.0001)
        await Timer(100, unit='ns')
    assert process.returncode == 0, f'External debug tool exited {process.returncode}'


async def protected_debug(jtag):
    async def write_csr(address, value):
        await jtag.register(14, value)
        assert await jtag.program(csr(0, address, 14)) == 0
    await write_csr(0x3b0, 0x41ff)
    await write_csr(0x3b1, 0x1fff)
    await write_csr(0x3a0, 0x9f98)
    assert await jtag.register(9) == 0x109
    await jtag.memory(0x2000, 0xc01)
    await jtag.memory(0x3008, 0xcf)
    await write_csr(0x180, (8 << 60) | 2)
    status = (1 << 17) | (1 << 11)
    await write_csr(0x300, status)
    assert await jtag.register(9) == 0x109, 'Internal transfers survive unmapped debug VA and locked PMP'
    await jtag.register(10, 0x200600)
    assert await jtag.program(ld(12, 10)) == 0
    assert await jtag.register(12) == 0xdeadc0de12345678
    await jtag.register(10, 0x10000)
    assert await jtag.program(ld(12, 10)) == 3, 'Program Buffer must translate ordinary data VAs'
    await jtag.access(2, 0x16, 0x700)
    await jtag.register(10, 0x300000)
    assert await jtag.program(ld(12, 10)) == 3, 'Program Buffer must retain ordinary PMP checks'
    await jtag.access(2, 0x16, 0x700)
    assert await jtag.program(csr(13, 0x300, 0, True)) == 0
    assert await jtag.register(13) & ((1 << 17) | (3 << 11)) == status
    assert await jtag.program(csr(13, 0x342, 0, True)) == 0
    assert await jtag.register(13) == 7


async def coherent_debug(jtag, memory):
    def raw():
        return sum(memory.get(0x980+n, 0) << (8*n) for n in range(8))
    seed, dirty, final = 0x193a5c7e9fb0d2f4, 0x8e6c4a2806fdb975, 0x75b9fd06284a6c8e
    await jtag.hart(1)
    await jtag.memory(0x980, seed)
    assert await jtag.memory(0x980) == seed
    await jtag.memory(0x980, dirty)
    assert raw() == seed, 'Peer must retain a real dirty owner'
    await jtag.hart(1, resume=True)
    await jtag.hart(0)
    assert await jtag.memory(0x980) == dirty, 'Debug load must recall running peer dirty bytes'
    assert raw() == dirty, 'Running peer must finish the recall writeback'
    await jtag.memory(0x980, final)
    assert raw() == dirty, 'Stopped hart must retain dirty ownership'
    await jtag.hart(1)
    assert await jtag.memory(0x980) == final, 'Debug load must recall stopped peer dirty bytes'
    assert raw() == final, 'Stopped peer cache must complete probes'
    await jtag.hart(0)


def openocd_configuration(config, bitbang_port, port):
    names = [f'ditdah.hart{n}' for n in range(config['hartCount'])]
    commands = ['adapter driver remote_bitbang', 'transport select jtag',
                'remote_bitbang host 127.0.0.1', f'remote_bitbang port {bitbang_port}',
                f'gdb port {port}', 'tcl port disabled', 'telnet port disabled', 'reset_config none',
                f'jtag newtap ditdah cpu -irlen 5 -expected-id {config["jtagIdcode"]}']
    for n, name in enumerate(names):
        commands += [f'target create {name} riscv -chain-position ditdah.cpu -coreid {n}',
                     'riscv set_mem_access progbuf',
                     f'{name} configure -event resume-end {{poll on}}',
                     f'{name} configure -event halted {{poll off}}']
    if len(names) > 1:
        commands += ['target smp ' + ' '.join(names), f'{names[0]} configure -rtos hwthread']
    commands += ['init', 'reset halt', 'poll off', 'echo DEBUG_READY']
    return commands


async def tool_debug(dut, root, config):
    with socket.socket() as listener, socket.socket() as reservation:
        listener.bind(('127.0.0.1', 0))
        listener.listen(1)
        listener.setblocking(False)
        reservation.bind(('127.0.0.1', 0))
        port = reservation.getsockname()[1]
        reservation.close()
        commands = openocd_configuration(config, listener.getsockname()[1], port)
        names = [f'ditdah.hart{n}' for n in range(config['hartCount'])]
        (root / 'openocd.cfg').write_text('\n'.join(commands)+'\n')
        image = {n: int(v, 16) for n, v in enumerate((root / 'image.hex').read_text().splitlines()[1:])}
        if config['enableC']:
            image.update({0: 0x85, 1: 0})
        expected = Model(config, image, {})
        expected.step()
        step = expected.pc
        script = ['set confirm off', 'set pagination off', f'set remotetimeout {max(30, 5*config["hartCount"])}',
                  f'target extended-remote 127.0.0.1:{port}',
                  'set {unsigned long long}0x680 = 0x12345678cafebabe',
                  'p/x *(unsigned long long*)0x680',
                  'if *(unsigned long long*)0x680 != 0x12345678cafebabe', 'quit 1', 'end',
                  'set $ra = 0', 'set $pc = 0', 'stepi', 'p/x $pc', f'if $pc != {step}', 'quit 1', 'end',
                  f'if $ra != {expected.registers[1]}', 'quit 1', 'end',
                  'info threads', 'disconnect', 'quit']
        checks = []
        for hart in range(config['hartCount']):
            checks += [f'thread {hart+1}', f'set $s0 = {0xfedcba9876543210 ^ hart:#x}', 'stepi', 'p/x $s0',
                       f'if $s0 != {0xfedcba9876543210 ^ hart:#x}', 'quit 1', 'end']
        script[4:4] = checks + ['thread 1']
        if len(names) > 1:
            script.insert(4, 'set scheduler-locking step')
        if config['enableC']:
            script.insert(script.index('set $pc = 0'), 'set {unsigned short}0 = 0x0085')
        if config['floatingPointBits']:
            field = 'double' if config['floatingPointBits'] == 64 else 'float'
            position = script.index('set {unsigned long long}0x680 = 0x12345678cafebabe')
            script[position:position] = ['set $ft0 = 1.5', 'set $ft1 = -2.25', 'set $ft11 = 0.125',
                'set $fcsr = 0x25', 'stepi', 'p $ft0', 'p $ft1', 'p $ft11', 'p/x $fcsr',
                'python', 'for name, wanted in (("ft0", 1.5), ("ft1", -2.25), ("ft11", 0.125)):',
                ' value = gdb.parse_and_eval("$"+name)',
                f' if value.type.strip_typedefs().code == gdb.TYPE_CODE_UNION: value = value["{field}"]',
                ' assert float(value) == wanted', 'end', 'if $fcsr != 0x25', 'quit 1', 'end']
        script[script.index('info threads'):script.index('info threads')] = [
            f'file {root / "probe.elf"}', 'load', 'compare-sections',
            'if *(unsigned long long*)0x800 != 0x0075051300000513 || *(unsigned long long*)0x808 != 0x0000006f00100073', 'quit 1', 'end',
            'set $pc = 0x800', 'stepi', 'if $pc != 0x804 || $a0 != 0', 'quit 1', 'end',
            'break *0x804', 'set $pc = 0x800', 'continue',
            'if $pc != 0x804 || $a0 != 0', 'quit 1', 'end', 'delete breakpoints', 'stepi',
            'if $pc != 0x808 || $a0 != 7', 'quit 1', 'end']
        cached_peers = config['hartCount'] if config['iCacheBytes'] and config['hartCount'] > 1 else 0
        if cached_peers:
            checks = ['set scheduler-locking on']
            for hart in range(cached_peers):
                checks += [f'thread {hart+1}', 'set $pc = 0x800', 'stepi', 'stepi',
                           'if $pc != 0x808 || $a0 != 7', 'quit 1', 'end']
            checks += ['thread 1', 'set {unsigned int}0x804 = 0x00b50513']
            for hart in range(cached_peers):
                checks += [f'thread {hart+1}', 'set $pc = 0x800', 'continue',
                           'if $pc != 0x808 || $a0 != 11', 'quit 1', 'end']
            checks += ['thread 1', 'set {unsigned int}0x804 = 0x00750513',
                       'set scheduler-locking step', 'echo ALL_CACHED_HARTS_REFETCHED\\n']
            position = script.index('info threads')
            script[position:position] = checks
        position = script.index('info threads')
        script[position:position+1] = ['python',
            'for thread in sorted(gdb.selected_inferior().threads(), key=lambda t: t.num): print(thread.num, thread.name)', 'end']
        (root / 'gdb.commands').write_text('\n'.join(script)+'\n')
        bridge = cocotb.start_soon(remote_bitbang(dut, listener))
        process = debugger = None
        try:
            with (root / 'openocd.log').open('w') as log, (root / 'gdb.log').open('w') as gdb_log:
                process = subprocess.Popen([os.environ['A1_DEBUG_OPENOCD'], '-f', root / 'openocd.cfg'],
                                           stdout=log, stderr=subprocess.STDOUT)
                deadline = time.monotonic()+90+40*config['hartCount']
                while 'DEBUG_READY' not in (root / 'openocd.log').read_text():
                    assert process.poll() is None and time.monotonic() < deadline, (root / 'openocd.log').read_text()
                    time.sleep(0.0001)
                    await Timer(100, unit='ns')
                debugger = subprocess.Popen([os.environ['A1_DEBUG_GDB'], '-q', '-nx', '-batch', '-x', root / 'gdb.commands'],
                                            stdout=gdb_log, stderr=subprocess.STDOUT)
                await process_done(debugger, 120+75*config['hartCount'])
            output = (root / 'gdb.log').read_text()
            assert '0xfedcba9876543210' in output and '0x12345678cafebabe' in output and f'0x{step:x}' in output
            assert 'matched.' in output and 'MIS-MATCHED!' not in output
            assert not cached_peers or 'ALL_CACHED_HARTS_REFETCHED' in output
            assert len(re.findall(r'^\s*\*?\s*\d+\s+', output, re.M)) == config['hartCount']
            (root / 'tools-summary.json').write_text(json.dumps(dict(harts=config['hartCount'], registers=True,
                programBufferMemory=True, executableLoad=True, softwareBreakpoint=True,
                floatingPointBits=config['floatingPointBits'], singleStepBytes=step,
                cachedCodeVisibilityHarts=cached_peers, output=output))+'\n')
        finally:
            for child in (debugger, process):
                if child is not None and child.poll() is None:
                    child.terminate()
                    deadline = time.monotonic()+5
                    while child.poll() is None and time.monotonic() < deadline:
                        time.sleep(0.0001)
                        await Timer(100, unit='ns')
                    if child.poll() is None:
                        child.kill()
                    child.wait()
            bridge.cancel()


@cocotb.test()
async def debug_system(dut):
    root = Path(os.environ['A1_DEBUG_TEST_ROOT'])
    manifest = json.loads((root / 'manifest.json').read_text())
    config = manifest['parameters']
    harts, base = config['hartCount'], int(config['debugBase'])
    memory = {n: int(v, 16) for n, v in enumerate((root / 'image.hex').read_text().splitlines()[1:])}
    dut.clock.value = dut.jtag_tck.value = dut.jtag_tdi.value = dut.systemReset.value = 0
    dut.reset.value = dut.jtag_trstN.value = dut.jtag_tms.value = 1
    for n in range(harts):
        for field in ('software', 'timer', 'external'):
            if config['enableInterrupts']:
                getattr(dut, f'interrupts_{n}_{field}').value = 0
    if config['localInterruptBase'] is not None:
        dut.timeTick.value = 0
    cocotb.start_soon(Clock(dut.clock, 10, unit='ns').start())
    cocotb.start_soon(memory_service(dut, memory, base))
    await Timer(40, unit='ns')
    dut.reset.value = 0
    for _ in range(30000):
        if all(memory.get(0x5000+8*n) == 1 for n in range(harts)):
            break
        await Timer(10, unit='ns')
    else:
        raise AssertionError('Ordinary software did not reach all hart markers')
    jtag = Jtag(dut)
    await jtag.reset()
    await jtag.scan(1, 5, True)
    assert await jtag.scan(0, 32) == config['jtagIdcode']
    await jtag.access(2, 0x10, 1)
    for hart in range(harts):
        await jtag.hart(hart)
        assert await jtag.register(8) == 0x108
        assert await jtag.register(9) == 0x109
        value = 0x1234567887654321 ^ hart
        await jtag.register(8, value)
        assert await jtag.register(8) == value
        assert await jtag.register(9) == 0x109
    await jtag.access(2, 0x10, 1)
    assert await jtag.program(csr(0, 0x301, 0), csr(13, 0x301, 0, True)) == 0
    assert await jtag.register(13) == Model(config, {}, {}).csrs[0x301]
    assert await jtag.program(csr(13, 0x7b0, 0, True)) == 0
    assert await jtag.register(13) >> 6 & 7 == 3
    await jtag.register(10, 0x600)
    await jtag.register(11, 0xdeadc0de12345678)
    assert await jtag.program(sd(11, 10), ld(12, 10)) == 0
    assert await jtag.register(12) == 0xdeadc0de12345678
    assert await jtag.program(csr(13, 0x342, 0, True)) == 0
    assert await jtag.register(13) == 7
    if harts > 1 and config['dCacheWriteback']:
        await coherent_debug(jtag, memory)
    if config['virtualAddressBits'] == 39:
        await protected_debug(jtag)
    await jtag.access(2, 4, 0x12345678)
    await jtag.access(2, 0x27, 0x55555555)
    await jtag.access(2, 0x10, 0x80000003)
    assert int(dut.systemResetActive.value)
    assert await jtag.access(1, 0x11) & 0x3000 == 0x3000
    assert await jtag.access(1, 4) == 0x12345678
    assert await jtag.access(1, 0x27) == 0x55555555
    await jtag.access(2, 0x10, 0x80000001)
    for hart in range(harts):
        status = await jtag.hart(hart)
        assert status & 0xc0000 == 0xc0000
        assert await jtag.program(csr(13, 0x7b1, 0, True)) == 0
        assert await jtag.register(13) == 0
    (root / 'pin-summary.json').write_text(json.dumps(dict(harts=harts, productionTop=True,
        debugWindowStaysInternal=True, nonDebugReset=True, protectedTranslation=config['virtualAddressBits'] == 39,
        dirtyPeerCoherence=harts > 1 and config['dCacheWriteback']))+'\n')
    if os.environ.get('A1_DEBUG_GDB'):
        await tool_debug(dut, root, config)


def main():
    from cocotb_tools.runner import get_runner
    parser = argparse.ArgumentParser()
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument('--rtl', type=Path)
    source.add_argument('--profile', choices=('single', 'pair', 'compressed', 'supervisor', 'coherent', 'shared', 'float32', 'float64', 'smp'))
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--openocd', type=Path)
    parser.add_argument('--gdb', type=Path)
    args = parser.parse_args()
    assert (args.openocd is None) == (args.gdb is None), 'Provide both external debug tools'
    root = args.output.resolve()
    root.mkdir(parents=True, exist_ok=True)
    inputs = ('test/debug_system.py', 'test/debug_module.py', 'test/programs.py', 'test/model.py', 'test/verify.py')
    hashes = {p: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in inputs}
    rtl = args.rtl.resolve() if args.rtl else root / 'rtl'
    if args.profile:
        harts = dict(single=1, pair=2, compressed=3, supervisor=1, coherent=2, shared=2, float32=1, float64=1, smp=16)[args.profile]
        config = dict(configuration(64), enableJtag=True, debugBase='65536', jtagIdcode=0xa126afff,
                      hartCount=harts, issueWidth=min(harts, 3), enableC=args.profile == 'compressed', enableM=False, enableA=True)
        if args.profile in ('supervisor', 'coherent', 'shared'):
            config.update(enableUserMode=True, enableSupervisorMode=True, enableInterrupts=True,
                          virtualAddressBits=39, pmpEntries=16, iCacheBytes=8192, dCacheBytes=8192, dCacheWriteback=True, issueWidth=3)
            config['memoryRegions'][0]['dataCacheable'] = True
        if args.profile == 'shared':
            config['l2CacheBytes'] = 131072
        if args.profile in ('float32', 'float64'):
            config.update(floatingPointBits=int(args.profile[5:]), issueWidth=3)
        (root / 'input.json').write_text(json.dumps(config, indent=2)+'\n')
        run(['build-ditdah-a1', '--config', root / 'input.json', '--output', rtl], root / 'build.log')
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    assert manifest['top'] == 'DitDahA1' and manifest['parameters']['axiDataBits'] == 64
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in manifest['sourceHashes'].items())
    (root / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    software(manifest['parameters'], root, ready_base=0x5000)
    if args.gdb:
        source = root / 'probe.S'
        source.write_text('/* SPDX-' 'FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */\n'
            '/* SPDX-' 'License-Identifier: MIT */\n.option norvc\n.option norelax\n.section .text\n.globl _start\n'
            '_start: addi a0, zero, 0\naddi a0, a0, 7\nebreak\nj .\n')
        run(['riscv64-unknown-elf-gcc', '-march=rv64i_zicsr_zifencei', '-mabi=lp64', '-nostdlib', '-nostartfiles',
             '-Wl,-Ttext=0x800', source, '-o', root / 'probe.elf'], root / 'probe-build.log')
    for name in ('pin-summary.json', 'tools-summary.json', 'summary.json'):
        (root / name).unlink(missing_ok=True)
    runner = get_runner('verilator')
    visibility = root / 'ports.vlt'
    visibility.write_text('`verilator_config\n' + ''.join(f'public_flat_rw -module "DitDahA1" -var "{port}"\n'
        for _, _, port in module_ports((rtl / 'DitDahA1.sv').read_text())))
    runner.build(sources=[rtl / p for p in (rtl / 'filelist.f').read_text().splitlines()],
                 hdl_toplevel='DitDahA1', build_dir=root / 'native', build_args=['-Wno-fatal', '--no-public-flat-rw', str(visibility), '-j', '2'],
                 timescale=('1ns', '1ps'), log_file=root / 'compile.log')
    environment = {'A1_DEBUG_TEST_ROOT': str(root), 'A1_DEBUG_GDB': '', 'A1_DEBUG_OPENOCD': ''}
    if args.gdb:
        for name, tool in [('A1_DEBUG_GDB', args.gdb), ('A1_DEBUG_OPENOCD', args.openocd)]:
            path = shutil.which(str(tool))
            assert path, 'External debug tools are required'
            environment[name] = str(Path(path).resolve())
    os.environ.update(environment)
    results = runner.test(test_module='debug_system', hdl_toplevel='DitDahA1', test_dir=root,
                extra_env=environment,
                log_file=root / 'run.log')
    assert (root / 'pin-summary.json').is_file()
    report = ET.parse(results)
    assert len(report.findall('.//testcase')) == 1 and not any(report.findall('.//' + kind) for kind in ('failure', 'error', 'skipped'))
    if args.gdb:
        assert (root / 'tools-summary.json').is_file()
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in hashes.items())
    tools = {name: dict(sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest(),
                       version=subprocess.check_output([path, '--version'], stderr=subprocess.STDOUT, text=True))
             for name, path in environment.items() if name in ('A1_DEBUG_GDB', 'A1_DEBUG_OPENOCD') and path}
    (root / 'summary.json').write_text(json.dumps(dict(manifest=manifest, testSourceHashes=hashes,
        cocotb=cocotb.__version__, tools=tools, externalTools=bool(args.gdb)), indent=2)+'\n')


if __name__ == '__main__':
    main()
