# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Check boot memory, exclusive accesses and serial output at platform pins."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import shutil
import socket
import subprocess
import time
import xml.etree.ElementTree as ET

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, Combine, FallingEdge, RisingEdge, Timer
from cocotb_tools.runner import get_runner

from model import ExclusiveMonitor
from debug_system import Jtag, openocd_configuration, process_done, remote_bitbang
from formal import module_ports
from programs import csr, sw
from verify import load_software, run


class Axi:
    def __init__(self, dut):
        self.dut = dut

    async def send(self, channel, fields, wait=True):
        d = self.dut
        if wait:
            await FallingEdge(d.clock)
        for name, value in fields.items():
            getattr(d, 'axi_'+channel+'_bits_'+name).value = value
        getattr(d, 'axi_'+channel+'_valid').value = 1
        for _ in range(100000):
            await RisingEdge(d.clock)
            if int(getattr(d, 'axi_'+channel+'_ready').value):
                break
        else:
            raise AssertionError('AXI request stalled: '+channel)
        await FallingEdge(d.clock)
        getattr(d, 'axi_'+channel+'_valid').value = 0

    async def receive(self, channel, hold=0):
        d = self.dut
        names = ('data', 'resp', 'id', 'last') if channel == 'r' else ('resp', 'id')
        def payload():
            return tuple(int(getattr(d, 'axi_'+channel+'_bits_'+name).value) for name in names)
        for _ in range(100000):
            await RisingEdge(d.clock)
            await Timer(1, unit='ns')
            if int(getattr(d, 'axi_'+channel+'_valid').value):
                break
        else:
            raise AssertionError('AXI response stalled: '+channel)
        result = payload()
        for _ in range(hold):
            await RisingEdge(d.clock)
            await Timer(1, unit='ns')
            assert int(getattr(d, 'axi_'+channel+'_valid').value) and payload() == result
        await FallingEdge(d.clock)
        getattr(d, 'axi_'+channel+'_ready').value = 1
        await RisingEdge(d.clock)
        await FallingEdge(d.clock)
        getattr(d, 'axi_'+channel+'_ready').value = 0
        return result

    async def read(self, address, size=3, identity=0, lock=0, count=1, hold=0):
        await self.send('ar', dict(addr=address, size=size, id=identity, lock=lock, burst=1, len=count-1))
        return [await self.receive('r', hold) for _ in range(count)]

    async def write(self, address, value, size=3, identity=0, lock=0, data_first=False, strobe=None):
        fields = dict(addr=address, size=size, id=identity, lock=lock, burst=1, len=0)
        payload = dict(data=value << (8*(address%8)), strb=((1 << (1 << size))-1) << (address%8) if strobe is None else strobe, last=1)
        first, second = ('w', payload), ('aw', fields)
        if not data_first:
            first, second = second, first
        await self.send(*first)
        await self.send(*second)
        return await self.receive('b', 3)


async def serial_output(dut, period, output):
    while True:
        await FallingEdge(dut.tx)
        await Timer(period*1.5, unit='ns')
        value = 0
        for bit in range(8):
            value |= int(dut.tx.value) << bit
            await Timer(period, unit='ns')
        assert int(dut.tx.value) == 1, 'UART stop bit'
        output.append(value)


@cocotb.test()
async def endpoint(dut):
    root = Path(os.environ['A1_PLATFORM_ROOT'])
    dut.reset.value = 1
    for channel in ('ar', 'aw', 'w'):
        getattr(dut, 'axi_'+channel+'_valid').value = 0
    dut.axi_r_ready.value = dut.axi_b_ready.value = 0
    cocotb.start_soon(Clock(dut.clock, 10, unit='ns').start())
    for _ in range(4):
        await RisingEdge(dut.clock)
    await FallingEdge(dut.clock)
    dut.reset.value = 0
    ticks = []
    for cycle in range(30):
        await RisingEdge(dut.clock)
        await Timer(1, unit='ns')
        if int(dut.timeTick.value):
            ticks.append(cycle)
    assert len(ticks) == 3 and all(b-a == 10 for a, b in zip(ticks, ticks[1:]))
    output = []
    cocotb.start_soon(serial_output(dut, 87*10, output))
    bus, monitor = Axi(dut), ExclusiveMonitor()
    ram = 0x80000000
    assert (await bus.read(0x1000, identity=15, hold=4))[0] == (0x0000006f0000006f, 0, 15, 1)
    assert await bus.write(0x1000, 0) == (2, 0)
    values = [0x1234567800000000+n for n in range(8)]
    for n, value in enumerate(values):
        assert await bus.write(ram+8*n, value, identity=n, data_first=n%2) == (0, n)
    burst = await bus.read(ram, identity=9, count=8, hold=2)
    assert burst == [(value, 0, 9, int(n == 7)) for n, value in enumerate(values)]
    assert await bus.write(ram+4, 0xabcdef12, size=2, data_first=True) == (0, 0)
    assert (await bus.read(ram))[0][0] == 0xabcdef1200000000
    assert (await bus.read(ram+1))[0][1] == 3
    assert (await bus.read(0xdead0000))[0][1] == 3
    assert await bus.write(ram, 0, size=2, strobe=0xf0) == (2, 0)
    for identity in (0, 15):
        assert (await bus.read(ram, identity=identity, lock=1))[0][1] == 1
        monitor.reserve(identity, ram, 8)
    assert await bus.write(ram, 17, identity=15, lock=1) == (int(monitor.conditional(15, ram, 8)), 15)
    assert await bus.write(ram, 19, identity=0, lock=1) == (int(monitor.conditional(0, ram, 8)), 0)
    assert (await bus.read(ram))[0][0] == 17
    await bus.read(ram, identity=2, lock=1)
    monitor.reserve(2, ram, 8)
    assert await bus.write(ram+4, 21, size=2, identity=7) == (0, 7)
    monitor.write(ram+4, 4)
    assert await bus.write(ram, 23, identity=2, lock=1) == (int(monitor.conditional(2, ram, 8)), 2)
    await bus.read(ram, identity=3, lock=1)
    assert await bus.write(ram+8, 29, identity=3, lock=1) == (0, 3)
    assert await bus.write(ram, 31, identity=3, lock=1) == (0, 3)
    for previous, replacement, written in ((ram+8, ram+64, ram), (ram, ram+64, ram), (ram, ram+64, ram+64)):
        await bus.read(previous, identity=8, lock=1)
        aw = cocotb.start_soon(bus.send('aw', dict(addr=written, size=3, id=9, lock=0, burst=1, len=0)))
        w = cocotb.start_soon(bus.send('w', dict(data=33, strb=255, last=1)))
        await Combine(aw, w)
        assert int(dut.axi_aw_ready.value) == int(dut.axi_w_ready.value) == 0
        await bus.send('ar', dict(addr=replacement, size=3, id=8, lock=1, burst=1, len=0), wait=False)
        monitor.reserve(8, replacement, 8)
        monitor.write(written, 8)
        assert (await bus.receive('r'))[1:] == (1, 8, 1)
        assert await bus.receive('b') == (0, 9)
        expected = int(monitor.conditional(8, replacement, 8))
        actual = await bus.write(replacement, 35, identity=8, lock=1)
        dut._log.info('reservation old=%x new=%x write=%x expected=%d actual=%s',
                      previous, replacement, written, expected, actual)
        assert actual == (expected, 8), 'Disjoint old write cleared the replacement reservation'
    for size in (2, 3):
        await bus.read(ram+128, size=size, identity=10, lock=1)
        await bus.read(ram+128, size=size, identity=11, lock=1)
        assert await bus.write(ram+128, 1, size=size, identity=12, lock=1) == (0, 12)
        assert await bus.write(ram+128+(1 << size), 3, size=size, identity=9) == (0, 9)
        assert await bus.write(ram+128, 5, size=size, identity=10, lock=1) == (1, 10)
        assert await bus.write(ram+128, 7, size=size, identity=11, lock=1) == (0, 11)
    await bus.send('ar', dict(addr=ram+192, size=3, id=13, lock=1, burst=1, len=0))
    held = cocotb.start_soon(bus.receive('r', hold=32))
    assert await bus.write(ram+192, 41, identity=14) == (0, 14)
    assert not held.done(), 'LR response must remain held through the interfering write'
    assert int(dut.axi_r_valid.value) == 1 and int(dut.axi_r_ready.value) == 0
    assert (await held)[1:] == (1, 13, 1)
    assert await bus.write(ram+192, 43, identity=13, lock=1) == (0, 13)
    for size, offset, mask in ((2, 0, 0xf0), (2, 4, 0x0f), (2, 0, 0x0f), (3, 0, 0xf0), (2, 0, 0)):
        assert await bus.write(ram+256, 0x0123456789abcdef) == (0, 0)
        assert (await bus.read(ram+256+offset, size=size, identity=8, lock=1))[0][1] == 1
        monitor.reserve(8, ram+256+offset, 1 << size)
        assert await bus.write(ram+256, 0xfedcba9876543210, identity=9, strobe=mask) == (0, 9)
        for byte in range(8):
            if mask >> byte & 1: monitor.write(ram+256+byte, 1)
        assert (await bus.read(ram+256))[0][0] == sum((((0xfedcba9876543210 if mask >> byte & 1 else 0x0123456789abcdef) >> (8*byte)) & 255) << (8*byte) for byte in range(8))
        assert await bus.write(ram+256+offset, 7, size=size, identity=8, lock=1) == (int(monitor.conditional(8, ram+256+offset, 1 << size)), 8)
    aw = cocotb.start_soon(bus.send('aw', dict(addr=ram, size=3, id=6, lock=0, burst=1, len=0)))
    w = cocotb.start_soon(bus.send('w', dict(data=37, strb=255, last=1)))
    await Combine(aw, w)
    await bus.send('ar', dict(addr=ram, size=3, id=4, lock=1, burst=1, len=0), wait=False)
    assert (await bus.receive('r'))[1] == 1
    assert await bus.receive('b') == (0, 6)
    assert await bus.write(ram, 41, identity=4, lock=1) == (0, 4)
    assert (await bus.read(ram))[0][0] == 37
    await bus.send('aw', dict(addr=ram, size=3, id=12, lock=0, burst=1, len=1))
    await bus.send('w', dict(data=43, strb=255, last=0))
    await bus.send('w', dict(data=47, strb=255, last=1))
    assert await bus.receive('b', 3) == (2, 12)
    assert (await bus.read(ram))[0][0] == 37
    for n, value in enumerate(b'AB\n'):
        assert await bus.write(0x10000000+4*n, value, size=2) == (0, 0)
    for _ in range(1000):
        await RisingEdge(dut.clock)
        if len(output) == 3:
            break
    assert bytes(output) == b'AB\n'
    await bus.read(ram, identity=5, lock=1)
    await bus.send('aw', dict(addr=ram, size=3, id=0, lock=0, burst=1, len=0))
    await bus.send('ar', dict(addr=ram, size=3, id=0, lock=0, burst=1, len=0))
    for _ in range(3):
        await RisingEdge(dut.clock)
    assert int(dut.axi_r_valid.value)
    await FallingEdge(dut.clock)
    dut.reset.value = 1
    await RisingEdge(dut.clock)
    await FallingEdge(dut.clock)
    dut.reset.value = 0
    assert int(dut.axi_r_valid.value) == int(dut.axi_b_valid.value) == 0
    assert await bus.write(ram, 53, identity=5, lock=1) == (0, 5)
    assert (await bus.read(ram))[0][0] == 37
    (root / 'endpoint-summary.json').write_text(json.dumps(dict(independentChannels=True,
        readBurst=True, replyStability=True, exclusiveModel=True, concurrentInvalidation=True,
        resetRetainsRam=True, serial=bytes(output).decode()))+'\n')


@cocotb.test()
async def system(dut):
    os.chdir(Path(__file__).resolve().parents[1])
    root = Path(os.environ['A1_PLATFORM_ROOT'])
    platform = json.loads((root / 'platform.json').read_text())
    config = platform['processor']['parameters']
    virtual = bool(platform.get('virtualMemoryTest'))
    config_path = Path(os.environ['A1_PLATFORM_RTL']) / 'input.json'
    _, program, manifest = load_software(root / 'software/software.elf', config_path)
    assert (program.software['clockHz'], program.software['timebaseHz']) == (platform['clockHz'], platform['timebaseHz'])
    harts, output = config['hartCount'], []
    dut.reset.value, dut.systemReset.value = 1, 0
    dut.jtag_tck.value, dut.jtag_tms.value, dut.jtag_tdi.value, dut.jtag_trstN.value = 0, 1, 0, 1
    period = 1000000000/platform['clockHz']
    cocotb.start_soon(Clock(dut.clock, period, unit='ns').start())
    cocotb.start_soon(serial_output(dut, platform['serialBitCycles']*period, output))
    for _ in range(8):
        await RisingEdge(dut.clock)
    await FallingEdge(dut.clock)
    dut.reset.value = 0
    for _ in range(100):
        await RisingEdge(dut.clock)
    jtag = Jtag(dut)
    await jtag.reset()
    await jtag.access(2, 0x10, 1)
    for hart in range(harts):
        await jtag.hart(hart)
        assert await jtag.program(csr(12, 0x7b1, 0, True)) == 0
        assert await jtag.register(12) == int(config['resetVector'])
    await jtag.hart(0)
    local = int(config['localInterruptBase'])
    before = await jtag.memory(local+0xbff8)
    after = await jtag.memory(local+0xbff8)
    assert after > before
    await jtag.memory(local+0x4000, 0)
    await jtag.register(10, local)
    await jtag.register(11, 1)
    assert await jtag.program(sw(11, 10)) == 0
    assert await jtag.program(csr(12, 0x344, 0, True)) == 0
    assert await jtag.register(12) & 0x88 == 0x88
    await jtag.register(11, 0)
    assert await jtag.program(sw(11, 10)) == 0
    await jtag.memory(local+0x4000, (1<<64)-1)
    bss_start, bss_end = program.software['bss']
    poison = 0xa5a5a5a5a5a5a5a5
    stride = 4096 if virtual else 8
    poisoned = {*range(bss_start, bss_end, stride), bss_end-8}
    if virtual:
        poisoned.add(manifest['symbols']['__atomic_count'])
    for address in poisoned:
        await jtag.memory(address, poison)
    assert await jtag.memory(bss_start) == await jtag.memory(bss_end-8) == poison
    with socket.socket() as listener, socket.socket() as reservation:
        listener.bind(('127.0.0.1', 0)); listener.listen(1); listener.setblocking(False)
        reservation.bind(('127.0.0.1', 0))
        port = reservation.getsockname()[1]
        reservation.close()
        commands = openocd_configuration(config, listener.getsockname()[1], port)
        (root / 'openocd.cfg').write_text('\n'.join(commands)+'\n')
        script = ['set confirm off', 'set pagination off', f'set remotetimeout {max(30, 5*harts)}',
                  f'file {root / "software/software.elf"}', f'target extended-remote 127.0.0.1:{port}',
                  'load', 'compare-sections',
                  f'if *(unsigned long long*){bss_start} != {poison:#x} || *(unsigned long long*){bss_end-8} != {poison:#x}' +
                  (f' || *(unsigned long long*)&__atomic_count != {poison:#x}' if virtual else ''), 'quit 1', 'end']
        script += [f'monitor if {{[llength [target names]] != {harts}}} {{error "Hart count mismatch"}}',
                   'monitor foreach target [target names] {targets $target; reg pc '+str(program.entry)+'}',
                   'monitor targets ditdah.hart0', 'maintenance flush register-cache', 'continue']
        if virtual:
            script.insert(-1, 'echo ALL_HART_ENTRY_SET\\n')
            script += ['thread 1', 'maintenance flush register-cache', 'set $result_failure = 0']
            script += [f'if *(unsigned long long*)&__atomic_count != {harts}', 'quit 1', 'end',
                       'echo ALL_HART_ATOMICS_MATCHED\\n']
        for hart in range(harts):
            address = program.software['results']+8*hart
            script += [f'set $result = *(unsigned long long*){address}',
                       f'printf "hart {hart:x} result=%llu\\n", $result']
            if virtual:
                script += [f'set $result_{hart} = $result', 'if $result != 1', 'set $result_failure = 1', 'end']
            else:
                script += ['if $result != 1', 'quit 1', 'end']
        if virtual:
            for hart in range(harts):
                address = program.software['results']+8*hart
                script += [f'if $result_{hart} != 1', 'thread 1',
                    f'printf "hart {hart:x} observer=0 result=%llu\\n", *(unsigned long long*){address}',
                    f'thread {hart+1}',
                    f'printf "hart {hart:x} observer={hart:x} result=%llu\\n", *(unsigned long long*){address}', 'thread 1', 'end']
            script += ['if $result_failure', 'quit 1', 'end']
        script += ['echo ALL_HART_RESULTS_MATCHED\\n', 'disconnect', 'quit']
        (root / 'gdb.commands').write_text('\n'.join(script)+'\n')
        bridge = cocotb.start_soon(remote_bitbang(dut, listener))
        debugger = server = None
        try:
            with (root / 'openocd.log').open('w') as log, (root / 'gdb.log').open('w') as debug_log:
                server = subprocess.Popen([os.environ['A1_PLATFORM_OPENOCD'], '-f', root / 'openocd.cfg'], stdout=log, stderr=subprocess.STDOUT)
                deadline = time.monotonic()+90+40*harts
                while 'DEBUG_READY' not in (root / 'openocd.log').read_text():
                    assert server.poll() is None and time.monotonic() < deadline
                    time.sleep(0.0001)
                    await Timer(100, unit='ns')
                debugger = subprocess.Popen([os.environ['A1_PLATFORM_GDB'], '-q', '-nx', '-batch', '-x', root / 'gdb.commands'], stdout=debug_log, stderr=subprocess.STDOUT)
                deadline = time.monotonic()+180+60*harts
                if virtual:
                    while 'ALL_HART_ENTRY_SET' not in (root / 'gdb.log').read_text().splitlines():
                        assert debugger.poll() is None and time.monotonic() < deadline, 'Software entry preparation did not finish'
                        time.sleep(0.0001)
                        await Timer(100, unit='ns')
                    deadline = time.monotonic()+1800
                expected = ''.join(program.software['expectedConsole']).encode()
                while len(output) < len(expected):
                    assert debugger.poll() is None and time.monotonic() < deadline, 'Serial software did not finish'
                    time.sleep(0.0001)
                    await Timer(100, unit='ns')
                assert bytes(output) == expected
                if virtual: await ClockCycles(dut.clock, 8192 * harts)
                debugger.send_signal(signal.SIGINT)
                await process_done(debugger, 120+30*harts)
                assert bytes(output) == expected
            text = (root / 'gdb.log').read_text()
            assert 'matched.' in text and 'MIS-MATCHED!' not in text and 'ALL_HART_RESULTS_MATCHED' in text
            assert not virtual or 'ALL_HART_ATOMICS_MATCHED' in text
            (root / 'system-summary.json').write_text(json.dumps(dict(harts=harts, bootRom=True,
                allHartResume=True, serialConsole=True, coherentResults=True, localInterrupts=True,
                nonzeroBss=True, softwareAtomics=bool(config['enableA']),
                clockHz=platform['clockHz'], timebaseHz=platform['timebaseHz']))+'\n')
        except AssertionError:
            if virtual and debugger is not None and debugger.poll() is None:
                debugger.send_signal(signal.SIGINT)
                try: await process_done(debugger, 120+30*harts)
                except AssertionError as diagnostic: dut._log.warning(str(diagnostic))
            raise
        finally:
            for process in (debugger, server):
                if process is not None and process.poll() is None:
                    process.terminate()
                    deadline = time.monotonic()+5
                    while process.poll() is None and time.monotonic() < deadline:
                        time.sleep(0.0001)
                        await Timer(100, unit='ns')
                    if process.poll() is None:
                        process.kill()
                    process.wait()
            bridge.cancel()
            (root / 'console.log').write_bytes(bytes(output))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rtl', type=Path)
    parser.add_argument('--virtual-memory', action='store_true')
    parser.add_argument('--gdb', type=Path)
    parser.add_argument('--openocd', type=Path)
    parser.add_argument('--mutation', choices=('exclusive-read',))
    args = parser.parse_args()
    assert not args.mutation or args.rtl, 'Select a platform for the negative control'
    root = args.output.resolve()
    root.mkdir(parents=True, exist_ok=True)
    assert not args.virtual_memory or not args.mutation
    paths = [Path(name) for name in ('test/platform_system.py', 'test/model.py', 'rtl/DitDahA1PlatformMemory.sv',
             'test/debug_system.py', 'test/debug_module.py', 'test/formal.py', 'test/programs.py', 'test/verify.py')]
    program = 'software/tests/virtual_memory.S' if args.virtual_memory else 'software/tests/serial.c'
    paths += [Path(program), Path('software/platform.json'), Path('scripts/build_platform.py')]
    hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    for name in ('endpoint-summary.json', 'system-summary.json', 'summary.json'):
        (root / name).unlink(missing_ok=True)
    runner = get_runner('verilator')
    sources = [Path('rtl/DitDahA1PlatformMemory.sv').resolve()]
    tools = {}
    top, parameters, build_args, kind = 'DitDahA1PlatformMemory', dict(ID_BITS=4, HARTS=16), ['--assert', '-j', '2'], 'endpoint'
    if args.virtual_memory:
        assert args.gdb and args.openocd
        config = json.loads(Path('software/platform.json').read_text())
        config.update(hartCount=16, virtualAddressBits=39, enableSupervisorMode=True, enableUserMode=True,
            enableA=True, issueWidth=3, loadQueueEntries=2, fabricReadSlots=2, iCacheBytes=8192,
            dCacheBytes=8192, dCacheWays=2, dCacheRefillBytes=64, dCacheWriteback=True,
            l2CacheBytes=131072, tlbEntries=4, iTlbEntries=4, dTlbEntries=2, asidBits=4)
        (root / 'input.json').write_text(json.dumps(config)+'\n')
        if args.rtl is None:
            args.rtl = root / 'rtl'
            run(['python3', 'scripts/build_platform.py', '--config', root / 'input.json', '--harts', '16',
                 '--clock-hz', '10000000', '--jtag-idcode', '0xa126afff', '--output', args.rtl], root / 'rtl-build.log')
    if args.rtl:
        assert args.gdb and args.openocd
        rtl = args.rtl.resolve()
        platform = json.loads((rtl / 'manifest.json').read_text())
        if args.virtual_memory:
            assert platform['clockHz'] == 10000000 and platform['timebaseHz'] == 1000000 and platform['applicationEntry'] == int(config['resetVector'])
            assert all(platform['processor']['parameters'][k] == v for k, v in config.items() if k not in ('resetVector', 'enableTrace', 'memoryRegions'))
            assert platform['processor']['parameters']['memoryRegions'][:len(config['memoryRegions'])] == config['memoryRegions']
        assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == digest for section in
                   (platform['sourceHashes'], platform['processor']['sourceHashes']) for p, digest in section.items())
        if args.mutation and not platform['processor']['parameters']['enableA']:
            (root / 'summary.json').write_text(json.dumps(dict(status='not_applicable', mutation=args.mutation,
                reason='atomic instructions disabled', sourceHashes=hashes))+'\n')
            return
        assert not args.mutation or platform['processor']['parameters']['hartCount'] == 1
        platform['virtualMemoryTest'] = args.virtual_memory
        (root / 'platform.json').write_text(json.dumps(platform, indent=2)+'\n')
        console = platform['parameters']['CONSOLE_BASE']
        run(['python3', 'scripts/build_software.py', '--config', rtl / 'input.json', '--ram-base', str(platform['applicationEntry']),
             '--isa', 'rv64ia' if platform['processor']['parameters']['enableA'] else 'rv64i',
             '--clock-hz', str(platform['clockHz']), '--timebase-hz', str(platform['timebaseHz']),
             '--console-base', str(console), '--program', program, *(['--zero-page-tables'] if args.virtual_memory else []),
             '--output', root / 'software'], root / 'software-build.log')
        dump = (root / 'software/software.dump').read_text()
        assert (all(op in dump for op in ('lr.d', 'sc.d')) if args.virtual_memory else 'amoadd.d' in dump) == platform['processor']['parameters']['enableA']
        sources = [rtl / name for name in (rtl / 'filelist.f').read_text().splitlines()]
        if args.mutation:
            name = 'DitDahA1PlatformMemory.sv'
            original = (rtl / name).read_text()
            anchor = 'axi_r_bits_data <= ram[(read_address-RAM_BASE)>>3];'
            assert original.count(anchor) == 1
            changed = original.replace(anchor, "axi_r_bits_data <= ram[(read_address-RAM_BASE)>>3] ^ (read_exclusive ? 64'h1 : 64'h0);")
            (root / name).write_text(changed)
            sources = [root / name if p.name == name else p for p in sources]
            (root / 'mutation.json').write_text(json.dumps(dict(original=hashlib.sha256(original.encode()).hexdigest(),
                mutated=hashlib.sha256(changed.encode()).hexdigest(), fault=args.mutation))+'\n')
        top, parameters, kind = 'DitDahA1Platform', {}, 'system'
        visibility = root / 'ports.vlt'
        visibility.write_text('`verilator_config\n' + ''.join(f'public_flat_rw -module "{top}" -var "{port}"\n'
            for _, _, port in module_ports((rtl / (top+'.sv')).read_text().replace(' wire ', ' '))))
        build_args += ['--no-public-flat-rw', str(visibility)]
        os.environ['A1_PLATFORM_RTL'] = str(rtl)
        for name, tool in (('A1_PLATFORM_GDB', args.gdb), ('A1_PLATFORM_OPENOCD', args.openocd)):
            resolved = shutil.which(str(tool))
            assert resolved, 'External debug tools are required'
            os.environ[name] = str(Path(resolved).resolve())
            tools[name] = dict(path=os.environ[name], sha256=hashlib.sha256(Path(os.environ[name]).read_bytes()).hexdigest(),
                version=subprocess.check_output([os.environ[name], '--version'], stderr=subprocess.STDOUT, text=True))
        (root / 'tools.json').write_text(json.dumps(tools, indent=2)+'\n')
    runner.build(sources=sources, hdl_toplevel=top, parameters=parameters,
        build_dir=root / 'native', build_args=build_args,
        timescale=('1ns', '1ps'), log_file=root / 'compile.log')
    os.environ['A1_PLATFORM_ROOT'] = str(root)
    results = runner.test(test_module='platform_system', hdl_toplevel=top, test_filter=kind+'$',
                          test_dir=root, log_file=root / 'run.log')
    report = ET.parse(results)
    selected = report.findall(f'.//testcase[@name="{kind}"]')
    assert len(selected) == 1
    if args.mutation:
        failure = selected[0].find('failure')
        assert failure is not None and failure.get('error_msg', '').startswith('External debug tool exited 1')
        output = (root / 'gdb.log').read_text()
        assert 'hart 0 result=2' in output and 'ALL_HART_RESULTS_MATCHED' not in output
    else:
        assert not any(selected[0].find(tag) is not None for tag in ('failure', 'error', 'skipped'))
        assert (root / (kind+'-summary.json')).is_file()
    assert all(case.get('name') == kind or case.find('skipped') is not None for case in report.findall('.//testcase'))
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == digest for p, digest in hashes.items())
    assert all(hashlib.sha256(Path(tool['path']).read_bytes()).hexdigest() == tool['sha256'] for tool in tools.values())
    (root / 'summary.json').write_text(json.dumps(dict(sourceHashes=hashes, cocotb=cocotb.__version__, tools=tools,
        status='counterexample' if args.mutation else 'pass', mutation=args.mutation), indent=2)+'\n')


if __name__ == '__main__':
    main()
