# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Exercise cancellation, authorization and backpressure on unit interfaces."""

from pathlib import Path
import hashlib
import json
import re
import random
import subprocess

from programs import addi, alu, amo, beq, csr, sd, mul, muldiv, ld, lw, sw, load, store, fence
from model import BITMANIP_ENCODINGS, ATOMIC_OPERATIONS, Fault, LocalInterrupts, Model, MASK, atomic_value, compressed_instruction, muldiv_value, pmp_allowed, signed, sv39_walk


def backend_control_signals(source):
    assert re.search(r'assign redirect\s*=\s*flushYounger;', source), 'Unknown recovery connection'
    match = re.search(r'\bwire\s+flushYounger\s*=\s*(\w+)\s*\|\s*(\w+);', source)
    assert match and match[2].startswith('earlyRedirect'), 'Unknown early recovery connection'
    return match[1], match[2]


def verify_storage(rtl, directory):
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    size = manifest['implementation']['iCacheBytes']
    data_size = manifest['implementation'].get('dCacheBytes', 0)
    shared_size = manifest['implementation'].get('l2CacheBytes', 0)
    ways = manifest['parameters'].get('dCacheWays', 1)
    way_size = data_size // ways
    files = (rtl / 'filelist.f').read_text().splitlines()
    slots = manifest['implementation']['fabricReadSlots']
    assert ('DitDahA1ReadQueue.sv' in files) == bool(slots)
    if slots:
        queue = (rtl / 'DitDahA1ReadQueue.sv').read_text()
        assert len(re.findall(r'\breg\s+\[2:0\]\s+state(?:_\d+)?\s*;', queue)) == slots, 'Read queue geometry'
        parameter = manifest['parameters']
        wide_line = parameter['axiDataBits'] > 64 and (parameter['enableBurstRefill'] or parameter['dCacheRefillBytes'] == 64)
        assert len(re.findall(r'\breg\s+\[\d+:0\]\s+block\s*;', queue)) == int(bool(wide_line)), 'Shared beat storage'
        assert bool(re.search(r'\bbeat\b', queue)) == bool(parameter['enableBurstRefill'] or parameter['dCacheRefillBytes'] == 64)
    arrays = {file[:-3]: tuple(map(int, re.search(r'_(\d+)x(\d+)\.sv$', file).groups()))
              for file in files if file.startswith(('instructions_', 'tags_', 'data_', 'dataTags_', 'dataDirty_', 'sharedData_', 'sharedTags_', 'mem_'))}
    assert ('DitDahA1InstructionCache.sv' in files) == bool(size)
    assert ('DitDahA1DataCache.sv' in files) == bool(data_size)
    banks = manifest['implementation']['fetchWords']
    expected = {} if not size else {'instructions': (size // (4 * banks), 32),
        'tags': (size // 64, manifest['parameters']['physicalAddressBits'] - (size // 64).bit_length() - 5)}
    if data_size:
        expected.update(data=(way_size // 8, 64),
                        dataTags=(way_size // 64, manifest['parameters']['physicalAddressBits'] - (way_size // 64).bit_length() - 5))
    if data_size and manifest['parameters'].get('dCacheWriteback'):
        expected['dataDirty'] = (way_size // 8, 8)
    if shared_size:
        expected.update(sharedData=(shared_size // (manifest['parameters']['axiDataBits'] // 8), manifest['parameters']['axiDataBits']),
                        sharedTags=(shared_size // 64, manifest['parameters']['physicalAddressBits'] - (shared_size - 1).bit_length()))
    assert ('DitDahA1SharedCache.sv' in files) == bool(shared_size)
    assert set(arrays.values()) == set(expected.values())
    if size:
        cache = (rtl / 'DitDahA1InstructionCache.sv').read_text()
        assert len(re.findall(r'^\s*instructions_\d+x32\s+\w+\s*\(', cache, re.M)) == banks
    if data_size:
        cache = (rtl / 'DitDahA1DataCache.sv').read_text()
        sets = data_size // (64 * ways)
        lru = re.search(r'\breg\s+\[(\d+):0\]\s+lru\s*;', cache)
        assert bool(lru) == (ways == 2) and (not lru or int(lru[1]) + 1 == sets), 'Replacement state geometry'
        assert bool(re.search(r'\breg\s+way\s*;', cache)) == (ways == 2), 'Redundant or missing way state'
        for name, width in (('data', 64), ('dataTags', expected['dataTags'][1]), ('dataDirty', 8)):
            expected_count = ways if name != 'dataDirty' or manifest['parameters']['dCacheWriteback'] else 0
            depth = way_size // (64 if name == 'dataTags' else 8)
            assert len(re.findall(rf'^\s*\w+_{depth}x{width}\s+{name}_ext(?:_\d+)?\s*\(', cache, re.M)) == expected_count, 'Physical cache way count'
    modules = {Path(file).stem: (rtl / file).read_text() for file in files if file.endswith('.sv')}
    instances = {}

    def visit(name, ancestors=()):
        assert name not in ancestors, 'Recursive storage hierarchy'
        instances[name] = instances.get(name, 0) + 1
        for child in re.findall(r'^\s*(\w+)\s+\w+\s*\(', modules[name], re.M):
            if child in modules:
                visit(child, (*ancestors, name))

    visit(manifest['top'])
    expected_caches = manifest['parameters']['hartCount'] if manifest['top'] == 'DitDahA1' else 1
    assert instances.get('DitDahA1DataCache', 0) == (expected_caches if data_size else 0), 'Physical cache instance count'
    assert instances.get('DitDahA1SharedCache', 0) == int(bool(shared_size)), 'Physical shared cache instance count'
    report = []
    directory.mkdir(parents=True, exist_ok=True)
    for module, (depth, width) in arrays.items():
        name = module.rsplit('_', 1)[0]
        netlist = directory / (module + '.json')
        command = f'read_verilog "{(rtl / (module + ".sv")).resolve()}"; hierarchy -top {module}; proc; memory_collect; write_json "{netlist.resolve()}"'
        result = subprocess.run(['yosys', '-Q', '-T', '-p', command], capture_output=True, text=True, timeout=30)
        (directory / (module + '.log')).write_text(result.stdout + result.stderr)
        assert result.returncode == 0, 'Storage structure elaboration failed'
        cells = json.loads(netlist.read_text())['modules'][module]['cells'].values()
        memories = [cell for cell in cells if cell['type'] == '$mem_v2']
        assert len(memories) == 1 and all(int(memories[0]['parameters'][key], 2) == value
                                        for key, value in (('SIZE', depth), ('WIDTH', width), ('RD_PORTS', 1), ('WR_PORTS', 1))), 'Storage geometry mismatch'
        state = sum(len(cell['connections']['Q']) for cell in cells if cell['type'].startswith('$dff'))
        assert state <= 3 * width + 4 * depth.bit_length(), 'Storage expanded into word registers'
        report.append(dict(array=name, depth=depth, width=width, registerBits=state,
                           instances=instances[module], storageBits=instances[module] * depth * width))
    (directory / 'summary.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


FETCH = r'''
    request_bits_pc = 64'h100; request_bits_tag = 8'h21;
    request_valid = 1;
    tick(); request_valid = 0;
    repeat (3) begin
      check(memory_request_valid && memory_request_bits_address == 64'h100 && memory_request_bits_tag == 8'h21 && memory_request_bits_size == 2 && memory_request_bits_mask == 0, "Fetch request hold");
      tick();
    end
    cancel = 1; tick(); cancel = 0;
    check(memory_request_valid, "Cancellation withdrew a pending request");
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_valid = 1; memory_response_bits_data = 64'h13; memory_response_bits_tag = 8'h21;
    check(memory_response_ready, "Cancelled response must drain");
    tick(); memory_response_valid = 0;
    check(!output_valid, "Cancelled fetch escaped");
    tick(); check(request_ready, "Fetch did not recover");

    request_bits_pc = 64'h104; request_bits_tag = 8'h22; request_valid = 1;
    tick(); request_valid = 0;
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    cancel = 1; tick(); cancel = 0;
    repeat (3) tick();
    memory_response_valid = 1; memory_response_bits_fault = 1; memory_response_bits_tag = 8'h22;
    tick(); memory_response_valid = 0; memory_response_bits_fault = 0;
    check(!output_valid, "Cancelled fault escaped");
    tick();

    request_bits_pc = 64'h108; request_bits_tag = 8'h23; request_valid = 1;
    tick(); request_valid = 0;
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_valid = 1; memory_response_bits_data = 64'h12345037; memory_response_bits_tag = 8'h23;
    tick(); memory_response_valid = 0;
    repeat (3) begin
      check(output_valid && output_bits_pc == 64'h108 && output_bits_tag == 8'h23 && output_bits_instruction == 32'h12345037 && !output_bits_fault, "Fetch result hold");
      tick();
    end
    cancel = 1; tick(); cancel = 0;
    check(!output_valid && request_ready, "Buffered cancellation failed");

    request_bits_pc = 64'h102; request_valid = 1;
    tick(); request_valid = 0;
    check(output_valid && output_bits_fault && output_bits_cause == 0 && output_bits_tval == 64'h102 && !memory_request_valid, "Fetch alignment fault");
    output_ready = 1; tick(); output_ready = 0;

    request_bits_pc = 64'h10c; request_valid = 1;
    tick(); request_valid = 0;
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_valid = 1; memory_response_bits_fault = 1;
    tick(); memory_response_valid = 0;
    check(output_valid && output_bits_fault && output_bits_cause == 1 && output_bits_tval == 64'h10c && output_bits_instruction == 0, "Fetch access fault");
    output_ready = 1; tick(); output_ready = 0;

    request_bits_pc = 64'h110; request_bits_tag = 8'h24; request_valid = 1;
    tick(); request_valid = 0;
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_valid = 1; memory_response_bits_fault = 0; memory_response_bits_tag = 8'h23;
    tick(); memory_response_valid = 0;
    check(output_valid && output_bits_tag == 8'h24 && output_bits_fault && output_bits_cause == 1 && output_bits_tval == 64'h110 && output_bits_instruction == 0, "Mismatched fetch response tag");
    output_ready = 1; tick();
'''

LSU = r'''
    input_bits_memorySize = 3;
    input_bits_instruction_pc = 64'h100;
    input_bits_instruction_instruction = 32'h00003023;
    input_bits_instruction_length = 4;
    input_bits_instruction_tag = 8'h51;
    memory_response_bits_tag = 8'h51;
    input_bits_address = 64'h1080;
    input_bits_storeData = 64'hfedcba9876543210;
    input_bits_store = 1;
    input_valid = 1;
    repeat (3) begin
      check(!input_ready && !memory_request_valid, "Unauthorized store");
      tick();
    end
    storeAllowed = 1; tick(); input_valid = 0; storeAllowed = 0;
    repeat (3) begin
      check(memory_request_valid && memory_request_bits_write && memory_request_bits_address == 64'h1080 && memory_request_bits_data == 64'hfedcba9876543210 && memory_request_bits_tag == 8'h51 && memory_request_bits_size == 3 && memory_request_bits_mask == 8'hff, "Authorized request hold");
      tick();
    end
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    repeat (3) begin check(!output_valid && !memory_request_valid, "Store completed before response"); tick(); end
    memory_response_valid = 1; memory_response_bits_fault = 1;
    tick(); memory_response_valid = 0;
    repeat (3) begin
      check(output_valid && output_bits_instruction_fault && output_bits_instruction_cause == 7 && output_bits_instruction_tval == 64'h1080, "Store fault hold");
      tick();
    end
    output_ready = 1; tick(); output_ready = 0;

    input_bits_store = 0; input_bits_load = 1;
    input_bits_address = 64'h1002;
    input_valid = 1; tick(); input_valid = 0;
    check(output_valid && output_bits_instruction_fault && output_bits_instruction_cause == 4 && !memory_request_valid, "Misaligned load escaped");
    output_ready = 1; tick(); output_ready = 0;

    input_bits_address = 64'h1008;
    input_bits_rd = 7; input_bits_rdWrite = 1;
    input_valid = 1; tick(); input_valid = 0;
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_valid = 1; memory_response_bits_fault = 0;
    memory_response_bits_data = 64'h8000000012345678;
    tick(); memory_response_valid = 0;
    repeat (3) begin
      check(output_valid && !output_bits_instruction_fault && output_bits_rd == 7 && output_bits_value == 64'h8000000012345678, "Load result hold");
      tick();
    end
    output_ready = 1; tick(); output_ready = 0;

    input_bits_instruction_tag = 8'h52;
    input_valid = 1; tick(); input_valid = 0;
    check(memory_request_valid && memory_request_bits_tag == 8'h52 && memory_request_bits_size == 3 && memory_request_bits_mask == 0, "Load request metadata");
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_valid = 1;
    tick(); memory_response_valid = 0;
    check(output_valid && output_bits_instruction_tag == 8'h52 && output_bits_instruction_fault && output_bits_instruction_cause == 5 && output_bits_instruction_tval == 64'h1008, "Mismatched load response tag");
    output_ready = 1; tick(); output_ready = 0;

    input_bits_address = 64'h1002;
    input_bits_store = 1; input_bits_load = 0;
    input_bits_instruction_fault = 1;
    input_bits_instruction_cause = 2;
    input_bits_instruction_tval = 64'hffffffff;
    input_valid = 1; tick(); input_valid = 0;
    check(output_valid && output_bits_instruction_cause == 2 && !memory_request_valid, "Faulting operation accessed memory");

    reset = 1; tick(); reset = 0; tick();
    input_bits_instruction_fault = 0; input_bits_address = 'h1080;
    input_bits_load = 1; input_bits_store = 1; input_bits_atomic = 1; storeAllowed = 0;
    input_bits_instruction_instruction = 32'h0020b4af;
    input_bits_storeData = 13; input_bits_rd = 9; input_bits_rdWrite = 1;
    input_valid = 1;
    repeat (3) begin check(!input_ready && !memory_request_valid, "Unauthorized atomic operation"); tick(); end
    storeAllowed = 1; tick(); input_valid = 0; storeAllowed = 0;
    repeat (3) begin
      check(memory_request_valid && memory_request_bits_atomic && memory_request_bits_write && !memory_request_bits_fetch && memory_request_bits_data == 13 && memory_request_bits_mask == 255 && memory_request_bits_size == 3, "Atomic request retention"); tick();
    end
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    repeat (3) begin check(!output_valid && !memory_request_valid, "Atomic completion waits for final response"); tick(); end
    memory_response_bits_data = 7; memory_response_bits_fault = 0;
    memory_response_bits_tag = input_bits_instruction_tag; memory_response_valid = 1;
    tick(); memory_response_valid = 0;
    repeat (3) begin
      check(output_valid && !output_bits_instruction_fault && output_bits_rd == 9 && output_bits_rdWrite && output_bits_value == 7, "Atomic old-value writeback"); tick();
    end
    output_ready = 1; tick(); output_ready = 0;
    input_bits_load = 0; input_bits_store = 0; input_bits_atomic = 0;
'''
for size, unsigned in ((0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)):
    expected = 0x8765c3a1 & ((1 << (8 << size)) - 1)
    expected = expected if unsigned else signed(expected, 8 << size)
    LSU += f'''
    input_bits_memorySize = {size}; input_bits_unsignedLoad = {unsigned};
    input_bits_address = 'h1004; input_bits_load = 1; input_bits_store = 0;
    input_bits_rdWrite = 1; input_valid = 1; tick(); input_valid = 0;
    while (!memory_request_valid) begin check(!output_valid, "Scalar load permission completion"); tick(); end
    repeat (3) begin
      check(memory_request_valid && memory_request_bits_address == 'h1004 && memory_request_bits_size == {size} && memory_request_bits_mask == 0, "Scalar load request"); tick();
    end
    memory_response_bits_tag = input_bits_instruction_tag;
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_data = 64'h123456788765c3a1; memory_response_valid = 1;
    tick(); memory_response_valid = 0;
    repeat (3) begin
      check(output_valid && !output_bits_instruction_fault && output_bits_value == 64'h{expected & MASK:016x}, "Scalar load extension and retention"); tick();
    end
    output_ready = 1; tick(); output_ready = 0;
'''
for size in range(3):
    LSU += f'''
    input_bits_memorySize = {size}; input_bits_address = 'h{0x1000 + (3 if size == 0 else 2 if size == 1 else 4):x}; input_bits_load = 0; input_bits_store = 1;
    storeAllowed = 1; input_valid = 1; tick(); input_valid = 0; storeAllowed = 0;
    repeat (3) begin
      check(memory_request_valid && memory_request_bits_write && memory_request_bits_size == {size} && memory_request_bits_mask == {(1 << (1 << size)) - 1}, "Scalar store mask and retention"); tick();
    end
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_data = 0; memory_response_valid = 1; tick(); memory_response_valid = 0;
    output_ready = 1; tick(); output_ready = 0;
'''
LSU += '''
    input_bits_address = 'h1002; input_bits_load = 1; input_bits_store = 0;
    input_valid = 1; tick(); input_valid = 0;
    check(output_valid && output_bits_instruction_fault && output_bits_instruction_cause == 4 && !memory_request_valid, "Word alignment fault");
    output_ready = 1; tick(); output_ready = 0;
    input_bits_memorySize = 3; input_bits_unsignedLoad = 0;
    input_bits_load = 0; input_bits_store = 0;
'''


def lsu_queue_contract(parameters):
    translated = parameters.get('virtualAddressBits') == 39 and parameters.get('enableSupervisorMode')
    user = parameters.get('enableUserMode', False)
    pmp_address = (1 << (parameters['physicalAddressBits'] - 2)) - 1

    def submit(address, pc, rd, operation=None, physical=None, overlap=False):
        instruction = ld(rd, 1) if operation is None else amo(operation, rd, 1, 0 if operation == 2 else 2)
        body = f'''    privilege = {0 if user else 3}; input_bits_instruction_pc = 'h{pc:x}; input_bits_instruction_tag = 73;
    input_bits_instruction_instruction = 32'h{instruction:x}; input_bits_instruction_length = 4;
    input_bits_address = 'h{address:x}; input_bits_rd = {rd}; input_bits_rdWrite = 1;
    input_bits_load = {int(operation != 3)}; input_bits_store = {int(operation is not None and operation != 2)};
    input_bits_atomic = {int(operation is not None)}; input_bits_memorySize = 3;
    input_valid = 1; #1; while (!input_ready) tick(); tick(); input_valid = 0;
'''
        if overlap:
            body += '    memory_response_valid = 0;\n'
        if translated:
            body += f'''    while (!translation_request_valid) tick();
    check(translation_request_bits_address == 'h{address:x}, "Translation retains its input owner");
    translation_request_ready = 1; tick(); translation_request_ready = 0;
    translation_response_bits_address = 'h{address if physical is None else physical:x}; translation_response_valid = 1;
    while (!translation_response_ready) tick(); tick(); translation_response_valid = 0;
'''
        return body

    def issue(index, address, write=False):
        return f'''    while (!memory_request_valid) tick();
    bus_id[{index}] = memory_request_bits_tag; privilege = 3;
    repeat (3) begin
      check(memory_request_valid && memory_request_bits_address == 'h{address:x} && memory_request_bits_tag == bus_id[{index}] && memory_request_bits_write == {int(write)} && memory_request_bits_privileged == {int(not user)}, "Memory offer retains context and effective privilege"); tick();
    end
    memory_request_ready = 1; tick(); memory_request_ready = 0;
'''

    def respond(index, value, fault=False, last=True):
        return f'''    memory_response_bits_tag = bus_id[{index}]; memory_response_bits_data = {value};
    memory_response_bits_fault = {int(fault)}; memory_response_bits_last = {int(last)}; memory_response_valid = 1;
    check(memory_response_ready, "Owned response can drain"); tick(); memory_response_valid = 0;
'''

    def complete(pc, rd, value, fault=False):
        payload = f'output_bits_value == {value}' if value is not None else "1'b1"
        failure = f" && output_bits_instruction_cause == 5 && output_bits_instruction_tval == 'h{0x1000 + 16 * (pc - 0x100):x}" if fault else ''
        return f'''    while (!output_valid) tick();
    repeat (3) begin
      check(output_valid && output_bits_instruction_pc == 'h{pc:x} && output_bits_instruction_tag == 73 && output_bits_rd == {rd} && {payload} && output_bits_instruction_fault == {int(fault)}{failure}, "In-order completion retains instruction, value and fault"); tick();
    end
    output_ready = 1; tick(); output_ready = 0;
'''

    body = '''    begin
      integer bus_id[2];
      storeAllowed = 1;
'''
    if parameters['pmpEntries']:
        body += f"    pmp_config = 'h1f; pmp_address = 'h{pmp_address:x};\n"
    for fault in (False, True):
        body += submit(0x1000, 0x100, 5) + issue(0, 0x1000)
        body += submit(0x1040, 0x104, 6) + issue(1, 0x1040)
        body += '''    check(bus_id[0] != bus_id[1] && !input_ready && !output_valid, "Two real reads own distinct contexts before either returns");
'''
        body += respond(1, 202)
        body += '    repeat (3) begin check(!output_valid, "Younger return cannot pass the completion head"); tick(); end\n'
        body += respond(0, 101, fault) + complete(0x100, 5, 101, fault) + complete(0x104, 6, 202)
        body += '    check(input_ready && !output_valid, "Completed contexts can be reused");\n'
    body += submit(0x1080, 0x108, 7) + issue(0, 0x1080)
    body += submit(0x10c0, 0x10c, 8)
    body += '''    while (!memory_request_valid) tick(); bus_id[1] = memory_request_bits_tag;
    repeat (2) tick(); cancel = 1;
    check(memory_request_valid && memory_request_bits_tag == bus_id[1], "Cancellation cannot withdraw a sampled read"); tick(); cancel = 0;
    repeat (3) begin
      check(memory_request_valid && memory_request_bits_tag == bus_id[1] && memory_request_bits_address == 'h10c0 && !input_ready, "Cancellation retains the offered read"); tick();
    end
    memory_request_ready = 1; tick(); memory_request_ready = 0;
'''
    body += respond(1, 404) + respond(0, 303) + complete(0x108, 7, 303) + complete(0x10c, 8, 404)
    body += '    check(input_ready && !memory_request_valid, "Cancelled ownership drains before reuse");\n'
    body += submit(0x1000, 0x100, 5) + issue(0, 0x1000)
    body += '    memory_response_bits_tag = bus_id[0]; memory_response_bits_data = 505; memory_response_valid = 1;\n'
    body += submit(0x1040, 0x104, 6, overlap=True) + issue(1, 0x1040) + respond(1, 606)
    body += complete(0x100, 5, 505) + complete(0x104, 6, 606)
    body += submit(0x1000, 0x100, 5) + issue(0, 0x1000) + submit(0x1000, 0x104, 6)
    body += '    repeat (4) begin check(!memory_request_valid, "Same physical word waits for its older reply"); tick(); end\n'
    body += respond(0, 101) + issue(1, 0x1000) + respond(1, 202)
    body += complete(0x100, 5, 101) + complete(0x104, 6, 202)
    if translated:
        body += submit(0x1000, 0x100, 5, physical=0x3000) + issue(0, 0x3000)
        body += submit(0x2000, 0x104, 6, physical=0x3000)
        body += '    repeat (4) begin check(!memory_request_valid, "Virtual aliases serialize by their physical word"); tick(); end\n'
        body += respond(0, 101, True) + issue(1, 0x3000) + respond(1, 202)
        body += complete(0x100, 5, 101, True) + complete(0x104, 6, 202)
    devices = [int(region['base']) for region in parameters['memoryRegions'] if region['device']]
    if devices:
        body += submit(devices[0], 0x100, 5) + '    storeAllowed = 0;\n' + issue(0, devices[0])
        body += respond(0, 707) + complete(0x100, 5, 707) + '    storeAllowed = 1;\n'
        body += submit(0x1000, 0x100, 5) + issue(0, 0x1000)
        body += '    storeAllowed = 0;\n' + submit(devices[0], 0x104, 6)
        body += '    repeat (3) begin check(!memory_request_valid, "Device read waits behind its older owner"); tick(); end\n'
        body += respond(0, 101) + complete(0x100, 5, 101)
        body += '''    repeat (3) begin check(!memory_request_valid, "Oldest device read still needs effect permission"); tick(); end
    storeAllowed = 1; tick(); storeAllowed = 0;
'''
        body += issue(1, devices[0]) + respond(1, 202) + complete(0x104, 6, 202) + '    storeAllowed = 1;\n'
        body += submit(0x1000, 0x100, 5) + issue(0, 0x1000)
        body += '    storeAllowed = 0;\n' + submit(devices[0], 0x104, 6)
        body += '    repeat (4) begin check(!memory_request_valid, "Younger device read has no effect permission"); tick(); end\n'
        body += respond(0, 101, True)
        body += '''    check(output_valid && output_bits_instruction_fault, "Older fault precedes device cancellation");
    cancel = 1; output_ready = 1; tick(); cancel = 0; output_ready = 0;
    while (!output_valid) begin check(!memory_request_valid, "Cancelled device read cannot issue"); tick(); end
'''
        body += complete(0x104, 6, None) + '    storeAllowed = 1;\n'
    if parameters['pmpEntries']:
        body += "    pmp_config = 'h98; pmp_address = 'h400;\n" + submit(0x1000, 0x100, 5)
        body += '''    while (!output_valid) begin check(!memory_request_valid, "Denied load cannot issue a request"); tick(); end
    check(output_bits_instruction_fault && output_bits_instruction_cause == 5 && output_bits_instruction_tval == 'h1000, "Protection fault retains its original address");
    output_ready = 1; tick(); output_ready = 0; reset = 1; tick();
'''
        body += f"    pmp_config = 'h1f; pmp_address = 'h{pmp_address:x}; reset = 0; tick();\n"
    body += submit(0x1000, 0x100, 5, 2) + issue(0, 0x1000)
    body += '''    input_bits_atomic = 0; input_bits_store = 0; input_bits_load = 1; input_valid = 1;
    repeat (3) begin check(!input_ready, "Pending atomic excludes younger data requests"); tick(); end
    input_valid = 0;
'''
    body += respond(0, 101) + complete(0x100, 5, 101)
    body += submit(0x1000, 0x104, 6, 3)
    body += '    while (!memory_request_valid) tick(); check(memory_request_bits_scEligible, "Shared reservation survives its completed LR");\n'
    body += issue(1, 0x1000, True) + respond(1, 0) + complete(0x104, 6, 0)
    body += submit(0x1000, 0x100, 5, 3)
    body += '    while (!memory_request_valid) tick(); check(!memory_request_bits_scEligible, "SC consumes the shared reservation");\n'
    body += issue(0, 0x1000, True) + respond(0, 1) + complete(0x100, 5, 1)
    body += submit(0x1000, 0x100, 5) + issue(0, 0x1000) + submit(0x1040, 0x104, 6) + issue(1, 0x1040)
    body += respond(0, 101, last=False) + respond(1, 202)
    body += '    repeat (3) begin check(!output_valid, "Nonterminal response retains its owner"); tick(); end\n'
    body += respond(0, 303) + complete(0x100, 5, 303, True) + complete(0x104, 6, 202)
    body += submit(0x1000, 0x100, 5) + issue(0, 0x1000) + submit(0x1040, 0x104, 6) + issue(1, 0x1040)
    body += '''    memory_response_bits_tag = 2; memory_response_valid = 1; tick(); memory_response_valid = 0;
    check(!output_valid && !input_ready, "Unknown context cannot complete a real owner");
'''
    body += respond(1, 202) + respond(0, 101) + complete(0x100, 5, 101, True) + complete(0x104, 6, 202, True)
    return body + '''    check(!input_ready && !memory_request_valid, "Protocol containment blocks new ownership");
    reset = 1; tick(); reset = 0; tick();
    check(input_ready && !output_valid, "Reset clears drained context state");
    end
'''


def lsu_reservation_contract(parameters):
    body, serial = '', 0

    def transfer(operation, address=0x1000, value=0, fault=False, eligible=False, local_fault=0, wrong_tag=False, size=3):
        nonlocal body, serial
        serial += 1
        tag = 80 + serial
        body += f'''    input_bits_atomic = 1; input_bits_instruction_instruction = 32'h{amo(operation, 7, 1, 0 if operation == 2 else 2, size=size):x};
    input_bits_instruction_fault = 0; input_bits_instruction_tag = {tag}; input_bits_memorySize = {size};
    input_bits_load = {int(operation != 3)}; input_bits_store = {int(operation != 2)};
    input_bits_address = 64'h{address:x}; input_bits_storeData = 9; input_bits_rd = 7; input_bits_rdWrite = 1;
    input_valid = 1; storeAllowed = 1; tick(); input_valid = 0; storeAllowed = 0;
    input_bits_atomic = 0; input_bits_address = 0;
'''
        if local_fault:
            body += f'    check(output_valid && output_bits_instruction_fault && output_bits_instruction_cause == {local_fault} && !memory_request_valid, "Reservation local fault");\n'
        else:
            body += f'''    repeat (3) begin
      check(memory_request_valid && memory_request_bits_atomic && memory_request_bits_atomicOperation == {operation} && memory_request_bits_scEligible == {int(eligible)} && memory_request_bits_address == 64'h{address:x} && memory_request_bits_mask == {0 if operation == 2 else (1 << (1 << size)) - 1}, "Reservation request capture"); tick();
    end
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_tag = {tag + int(wrong_tag)}; memory_response_bits_fault = {int(fault)};
    memory_response_bits_data = 64'h{value:x}; memory_response_valid = 1; tick(); memory_response_valid = 0;
    repeat (3) begin
      check(output_valid && output_bits_instruction_fault == {int(fault or wrong_tag)} && output_bits_rd == 7 && output_bits_rdWrite && output_bits_value == 64'h{signed(value, 32) & MASK if size == 2 else value:x}, "Reservation result retention"); tick();
    end
'''
            if fault or wrong_tag:
                body += f'    check(output_bits_instruction_cause == {5 if operation == 2 else 7} && output_bits_instruction_tval == 64\'h{address:x}, "Reservation response fault");\n'
        body += '    output_ready = 1; tick(); output_ready = 0; memory_response_bits_fault = 0;\n'

    transfer(3, value=1)
    transfer(2, value=MASK)
    transfer(3, eligible=True)
    transfer(3, value=1)
    transfer(2)
    transfer(2, 0x1008)
    transfer(3, value=1)
    transfer(3, 0x1008, value=1)
    for fault, wrong_tag in ((True, False), (False, True)):
        transfer(2, fault=fault, wrong_tag=wrong_tag)
        transfer(3, value=1)
    transfer(2)
    transfer(3, fault=True, eligible=True)
    transfer(3, value=1)
    transfer(2)
    transfer(3, 0x1002, local_fault=6)
    transfer(3, value=1)
    transfer(2)
    transfer(3, (1 << parameters['physicalAddressBits']) + 0x1000, value=1,
             local_fault=7 if parameters['pmpEntries'] else 0)
    transfer(3, value=1)
    for operation in (0, 1, 8):
        transfer(2)
        transfer(operation, 0x1008)
        transfer(3, value=1)
    transfer(2)
    body += '    reset = 1; tick(); reset = 0; tick();\n'
    transfer(3, value=1)
    if parameters['pmpEntries']:
        body += "    pmp_config = 'h99; pmp_address = 'h400;\n"
        transfer(2, value=7)
        transfer(3, local_fault=7)
        transfer(0, local_fault=7)
        body += '    pmp_config = 0; pmp_address = 0;\n'
    for size in (2, 3):
        transfer(2, value=0x80000000, size=size)
        transfer(3, eligible=True, size=size)
        transfer(3, value=1, size=size)
        transfer(2, size=size)
        transfer(3, value=1, size=5-size)
        transfer(2, 0x1004 if size == 2 else 0x1008, size=size)
        transfer(3, value=1, size=size)
    return body + '    input_bits_atomic = 0; input_bits_load = 0; input_bits_store = 0;\n'


def arbiter_contract(parameters):
    count = 2 * parameters['hartCount']
    body = ''.join(f"    ports_{i}_request_valid = 1; ports_{i}_response_ready = 1;\n"
                   f"    ports_{i}_request_bits_address = {0x100 + 8*i};\n"
                   f"    ports_{i}_request_bits_data = {0x1000 + i};\n"
                   f"    ports_{i}_request_bits_tag = 7; ports_{i}_request_bits_size = 3;\n"
                   f"    ports_{i}_request_bits_mask = 255; ports_{i}_request_bits_write = {i % 2};\n"
                   f"    ports_{i}_request_bits_fetch = {1-i % 2}; ports_{i}_request_bits_atomic = {i % 2};\n"
                   f"    ports_{i}_request_bits_atomicOperation = {i % 9}; ports_{i}_request_bits_scEligible = {i % 2};\n" for i in range(count))
    no_ready = ' && '.join(f'!ports_{i}_request_ready' for i in range(count))
    for owner in list(range(count)) * 2:
        ready = ' && '.join(f'ports_{i}_request_ready == {int(i == owner)}' for i in range(count))
        response = ' && '.join(f'ports_{i}_response_valid == {int(i == owner)}' for i in range(count))
        body += f'''    check({ready}, "Round-robin service order"); tick();
    ports_{owner}_request_valid = 0; ports_{owner}_request_bits_address = 0;
    ports_{owner}_request_bits_atomicOperation = 31; ports_{owner}_request_bits_scEligible = {1-owner % 2};
    repeat (3) begin
      check(downstream_request_valid && hartId == {owner // 2} && downstream_request_bits_address == {0x100+8*owner} && downstream_request_bits_data == {0x1000+owner} && downstream_request_bits_tag == 7 && downstream_request_bits_size == 3 && downstream_request_bits_mask == 255 && downstream_request_bits_write == {owner % 2} && downstream_request_bits_fetch == {1-owner % 2} && downstream_request_bits_atomic == {owner % 2} && downstream_request_bits_atomicOperation == {owner % 9} && downstream_request_bits_scEligible == {owner % 2} && {no_ready}, "Captured request survives contention and backpressure"); tick();
    end
    ports_{owner}_request_bits_address = {0x100+8*owner}; ports_{owner}_request_valid = 1;
    ports_{owner}_request_bits_atomicOperation = {owner % 9}; ports_{owner}_request_bits_scEligible = {owner % 2};
    downstream_request_ready = 1; tick(); downstream_request_ready = 0;
    downstream_response_valid = 1; downstream_response_bits_data = {0x2000+owner};
    downstream_response_bits_tag = 7; downstream_response_bits_fault = {owner % 2};
    ports_{owner}_response_ready = 0;
    repeat (3) begin
      check({response} && !downstream_response_ready && {no_ready} && ports_{owner}_response_bits_data == {0x2000+owner} && ports_{owner}_response_bits_tag == 7 && ports_{owner}_response_bits_fault == {owner % 2}, "Retained response owner with colliding tags"); tick();
    end
    ports_{owner}_response_ready = 1; tick(); downstream_response_valid = 0;
'''
    if parameters.get('enableBurstRefill') or parameters.get('dCacheRefillBytes') == 64:
        body += ''.join(f"    ports_{i}_request_valid = 0;\n" for i in range(count))
        body += "    ports_0_request_valid = 1; ports_0_request_bits_size = 6; tick(); ports_0_request_valid = 0;\n"
        body += "    downstream_request_ready = 1; tick(); downstream_request_ready = 0; ports_1_request_valid = 1;\n"
        body += "    for (integer chunk = 0; chunk < 8; chunk++) begin\n"
        body += f"""    downstream_response_bits_last = chunk == 7; downstream_response_bits_data = chunk;
    downstream_response_valid = 1; ports_0_response_ready = 0;
    repeat (3) begin
      check(ports_0_response_valid && !ports_1_response_valid && !ports_1_request_ready && ports_0_response_bits_data == chunk && ports_0_response_bits_last == (chunk == 7) && hartId == 0, "Stream retains owner and stalled chunk"); tick();
    end
    ports_0_response_ready = 1; tick(); downstream_response_valid = 0;
    end
    check(ports_1_request_ready, "Peer is served after terminal chunk");
"""
    return body


def compressed_fetch_contract(parameters, frontend=False):
    base = int(parameters['resetVector'])
    prefix = 'output_bits_packets_0_' if frontend else 'output_bits_'
    translated = parameters.get('virtualAddressBits') == 39
    body = f'''    begin
      reg [63:0] expected_pc, address;
      integer size, tag, count;
      expected_pc = 'h{base:x};
      fork
        begin forever begin
          @(negedge clock); memory_request_ready=1;
          if (memory_request_valid) begin
            address=memory_request_bits_address; size=memory_request_bits_size; tag=memory_request_bits_tag;
            check(size == 1 || size == 2 || size == 6, "Parcel, word or line fetch size");
            tick(); memory_request_ready=0;
            for (integer beat=0; beat<(size==6 ? 8 : 1); beat=beat+1) begin
              repeat (2) tick(); memory_response_bits_data=0;
              for (integer b=0; b<(size==6 ? 8 : 1<<size); b=b+1) begin
                case ((address-'h{base:x}) + 8*beat+b)
                  'h3e: memory_response_bits_data[8*b+:8]='h93;
                  'h3f: memory_response_bits_data[8*b+:8]='h00;
                  'h40: memory_response_bits_data[8*b+:8]='h70;
                  'h41: memory_response_bits_data[8*b+:8]='h00;
                  default: memory_response_bits_data[8*b+:8]=((address+8*beat+b)&1) ? 0 : 1;
                endcase
              end
              memory_response_bits_tag=tag; memory_response_bits_last=(size!=6 || beat==7);
              memory_response_valid=1;
              while (!memory_response_ready) tick(); tick(); memory_response_valid=0;
            end
          end
        end end
      join_none
'''
    if translated:
        body += '''      translation_request_ready=1;
      fork begin forever begin
        @(negedge clock);
        translation_response_valid=translation_request_valid;
        translation_response_bits_address=translation_request_bits_address;
      end end join_none
'''
    if frontend:
        body += f'''      output_ready=0; repeat (150) tick();
      output_ready=1; count=0;
      while (count<40) begin
        @(negedge clock);
        if (output_valid) begin
'''
        for lane in range(parameters['issueWidth']):
            p = f'output_bits_packets_{lane}_'
            body += f'''          if (output_bits_count>{lane}) begin
            check({p}pc == expected_pc && !{p}fault && {p}instruction == (expected_pc=='h{base+0x3e:x} ? 'h00700093 : 1) && {p}length == (expected_pc=='h{base+0x3e:x} ? 4 : 2), "Mixed-length frontend queue, raw encoding and sequential PC");
            expected_pc=expected_pc+(expected_pc=='h{base+0x3e:x} ? 4 : 2); count=count+1;
          end
'''
        body += '        end\n        tick();\n      end\n'
    else:
        for n, offset in enumerate((0, 2, 0x3e, 0x42)):
            body += f'''      request_valid=1; request_bits_pc='h{base+offset:x}; request_bits_tag={n+1};
       #1; while (!request_ready) tick(); tick(); request_valid=0;
      while (!output_valid) tick();
      repeat (3) begin
        check({prefix}pc == 'h{base+offset:x} && {prefix}tag == {n+1} && !{prefix}fault && {prefix}instruction == 'h{0x00700093 if offset==0x3e else 1:x} && {prefix}length == {4 if offset==0x3e else 2}, "Parcel assembly across words and lines, raw encoding and backpressure"); tick();
      end
      output_ready=1; tick(); output_ready=0;
'''
        body += f'''      request_bits_pc='h{base+1:x}; request_valid=1;
       #1; while (!request_ready) tick(); tick(); request_valid=0;
      check(output_valid && output_bits_fault && output_bits_cause==0 && output_bits_tval=='h{base+1:x}, "Odd instruction address fault");
      cancel=1; tick(); cancel=0;
      check(!output_valid, "Cancelled compressed fault escaped");
'''
    return body + '    end\n'


def compressed_decode_contract(directory):
    table = directory / 'compressed.hex'
    values = []
    for raw in range(65536):
        insn = compressed_instruction(raw)
        opcode, f = insn & 127, (insn >> 12) & 7
        rs1, rs2, rd = (insn >> 15) & 31, (insn >> 20) & 31, (insn >> 7) & 31
        op = {0x37: 1, 0x13: 3 if f == 0 else 21, 0x1b: 23,
              0x33: 4 if f == 0 and insn >> 25 == 0 else 22, 0x3b: 24,
              0x03: 18 if f == 2 else 8, 0x23: 20 if f == 2 else 9,
              0x63: 5 if f == 0 else 25, 0x6f: 6, 0x67: 7, 0x73: 12}.get(opcode, 0)
        immediate = signed(insn >> 20, 12)
        if opcode == 0x37:
            immediate = signed(insn & ~4095, 32)
        elif opcode == 0x23:
            immediate = signed(((insn >> 25) << 5) | ((insn >> 7) & 31), 12)
        elif opcode == 0x63:
            immediate = signed(((insn >> 31) << 12) | (((insn >> 7) & 1) << 11) | (((insn >> 25) & 63) << 5) | (((insn >> 8) & 15) << 1), 13)
        elif opcode == 0x6f:
            immediate = signed(((insn >> 31) << 20) | (((insn >> 12) & 255) << 12) | (((insn >> 20) & 1) << 11) | (((insn >> 21) & 1023) << 1), 21)
        use1 = op in (3, 4, 5, 7, 8, 9, 18, 20, 21, 22, 23, 24, 25)
        use2 = op in (4, 5, 9, 20, 22, 24, 25)
        write = op not in (0, 5, 9, 12, 20, 25)
        value = 0
        for field, bits in ((op, 5), (rs1, 5), (rs2, 5), (rd, 5), (immediate & MASK, 64),
                            (((insn >> 30) & 1) * 8 + f, 4), (int(use1), 1), (int(use2), 1), (int(write), 1)):
            value = (value << bits) | field
        values.append(f'{value:023x}')
    table.write_text('\n'.join(values) + '\n')
    return f'''    begin
      reg [90:0] expected [0:65535];
      $readmemh("{table.resolve()}", expected);
      input_valid=1; output_ready=1; input_bits_length=2;
      for (integer n=0; n<65536; n=n+1) begin
        input_bits_instruction=n;
        check({{output_bits_operation, output_bits_rs1, output_bits_rs2, output_bits_rd,
          output_bits_immediate, output_bits_functionCode, output_bits_usesRs1,
          output_bits_usesRs2, output_bits_writesRd}} == expected[n] &&
          output_bits_instruction_instruction == n && output_bits_instruction_length == 2 && !output_bits_serializing,
          "Exhaustive compressed decode, immediate, dependencies and raw encoding");
      end
    end
    input_bits_length=4;
'''


def decode_contract(parameters, directory):
    cases = ((0x12345337, 0, 0, 1), (0x12345317, 0, 0, 1),
             (0x12328313, 1, 0, 1), (0x00728333, 1, 1, 1),
             (0x00728463, 1, 1, 0), (0x0080036f, 0, 0, 1),
             (0x00428367, 1, 0, 1), (0x0082b303, 1, 0, 1),
             (0x0072b423, 1, 1, 0), (0x34029373, 1, 0, 1),
             (0x3402a373, 1, 0, 1), (0x00000073, 0, 0, 0), (0x00100073, 0, 0, 0),
             (0x30200073, 0, 0, 0), (0x10500073, 0, 0, 0), (0x10400073, 0, 0, 0), (0x10508073, 0, 0, 0), (0x105000f3, 0, 0, 0), (0xffffffff, 0, 0, 0))
    cases += ((mul(6, 5, 7), 1, 1, 1), (mul(6, 5, 7) | (1 << 12), 1, 1, 1))
    cases += ((lw(6, 5, 4), 1, 0, 1), (lw(6, 5, 4, True), 1, 0, 1), (sw(7, 5, 4), 1, 1, 0))
    extra = {alu(6, 5, 7, f): 22 for f in range(1, 8)}
    extra.update({alu(6, 5, 7, f, immediate=True): 21 for f in range(1, 8)})
    extra.update({alu(6, 5, 7, f, word=True, immediate=imm): 23 if imm else 24 for imm in (False, True) for f in (0, 1, 5)})
    extra.update({beq(5, 7, 8) | (f << 12): 25 for f in (1, 4, 5, 6, 7)})
    extra.update({load(6, 5, 4, s, u): 26 for s in (0, 1) for u in (False, True)})
    extra.update({store(7, 5, 4, s): 27 for s in (0, 1)})
    extra.update({csr(6, 0x340, 5, function=f): 28 for f in (3, 5, 6, 7)})
    extra.update({amo(op, 6, 5, 0 if op == 2 else 7, order, size): 15 if op == 0 and size == 3 else 30
                  for op in (*ATOMIC_OPERATIONS, 2, 3) for size in (2, 3) for order in range(4)})
    extra.update({muldiv(6, 5, 7, function, word): 14 for word in (False, True) for function in ((0, 4, 5, 6, 7) if word else range(8))})
    if parameters.get('enableSupervisorMode'):
        extra[0x10200073] = 31
    cases += tuple((word, int(op != 31 and (op != 28 or (word >> 12) & 4 == 0)), int(op in (14, 15, 22, 24, 25, 27) or op == 30 and word >> 27 != 2), int(op not in (25, 27, 31))) for word, op in extra.items())
    invalid = {amo(op, 6, 5, 0 if op == 2 else 7) ^ ((3 ^ size) << 12) for op in (*ATOMIC_OPERATIONS, 2, 3) for size in range(8) if size not in (2, 3)}
    invalid.update(amo(op, 6, 5, 7) for op in range(32) if op not in (*ATOMIC_OPERATIONS, 2, 3))
    invalid.update(amo(2, 6, 5, rs) for rs in (1, 31))
    invalid.update((0x00108073, 0x001000f3, 0x00200073, 0x000000f3))
    invalid.update(muldiv(6, 5, 7, function, True) for function in (1, 2, 3))
    cases += tuple((word, 0, 0, 0) for word in sorted(invalid))
    cases += ((alu(6, 5, 32, 1, True, True), 0, 0, 0), (alu(6, 5, 64, 1, immediate=True), 0, 0, 0), (csr(6, 0x340, 5, function=4), 0, 0, 0))
    cases += tuple((0x0072b32f | (ordering << 25), 1, 1, 1) for ordering in range(4))
    cases += tuple((fence(instruction, reserved), 0, 0, 0) for instruction in (False, True)
                   for reserved in (0, 0x83328880, 0xffff8f80))
    cases += ((0x200f, 0, 0, 0), (0x700f, 0, 0, 0))
    for name, (extension, encoding, mask) in BITMANIP_ENCODINGS.items():
        for amount in ((0, 1, 31, 32, 63) if mask == 0xfc00707f else (0, 1, 31)):
            operand = amount if mask != 0xfff0707f else 0
            word = encoding | (5 << 15) | (6 << 7) | (operand << 20)
            enabled = parameters.get('enable' + extension, False)
            register = word & 127 in (0x33, 0x3b) and mask != 0xfff0707f
            extra[word] = (22 if register else 21) if enabled else 0
            cases += ((word, int(enabled), int(enabled and register), int(enabled)),)
    invalid.update((0x69805013, 0x6200501b, 0x08004033, 0x60801013, 0x2a001033))
    cases += tuple((word, 0, 0, 0) for word in (0x69805013, 0x6200501b, 0x08004033, 0x60801013, 0x2a001033))
    body = '    input_valid = 1; output_ready = 1;\n'
    for word, rs1, rs2, rd in cases:
        if word & 127 in (0x33, 0x3b) and word >> 25 == 1 and not parameters.get('enableM', True):
            rs1 = rs2 = rd = 0
            extra[word] = 0
        if word & 127 == 0x2f and not parameters.get('enableA', True):
            rs1 = rs2 = rd = 0
            extra[word] = 0
        serial = int((word & 127 == 0x73 and (word >> 12) & 7 in (1, 2, 3, 5, 6, 7)) or word in (0x30200073, 0x10500073) or word == 0x10200073 and parameters.get('enableSupervisorMode') or word & 0x707f in (0x0f, 0x100f))
        body += (f"    input_bits_instruction = 32'h{word:08x};\n"
                 f'    check(output_valid && input_ready && output_bits_usesRs1 == {rs1} && output_bits_usesRs2 == {rs2} && output_bits_writesRd == {rd} && output_bits_serializing == {serial}, "Decode dependency metadata {word:08x}");\n')
        if word in extra or word in invalid:
            body += f'    check(output_bits_operation == {extra.get(word, 0)}, "Scalar operation class {word:08x}");\n'
        if word in (0x00000073, 0x00100073):
            body += '    check(output_bits_operation == 12, "Environment exception operation class");\n'
    if parameters.get('virtualAddressBits') == 39:
        precise = any(parameters.get(key) for key in ('tlbEntries', 'iTlbEntries', 'dTlbEntries')) and any(parameters.get(key) for key in ('asidBits', 'iTlbEntries', 'dTlbEntries'))
        for rs1, rs2 in ((0, 0), (1, 0), (0, 31), (31, 31)):
            word = 0x12000073 | (rs1 << 15) | (rs2 << 20)
            body += f'''    input_bits_instruction = 32'h{word:x};
    check(output_bits_operation == 16 && output_bits_serializing && output_bits_usesRs1 == {int(precise)} && output_bits_usesRs2 == output_bits_usesRs1 && !output_bits_writesRd, "SFENCE selector dependencies");
'''
        for word in (0x120000f3, 0x12001073, 0x14000073):
            body += f"    input_bits_instruction = 32'h{word:x}; check(output_bits_operation != 16, \"SFENCE requires its complete standard encoding\");\n"
    return body + (compressed_decode_contract(directory) if parameters.get('enableC') else "    input_bits_length=2; input_bits_instruction='h4485; check(output_bits_operation==0, \"Disabled compressed encoding\"); input_bits_length=4;\n") + '''    input_bits_instruction = 32'h00728333; input_bits_fault = 1;
    check(!output_bits_usesRs1 && !output_bits_usesRs2 && !output_bits_writesRd, "Faulting instruction dependencies");
    input_bits_instruction = 32'h34029373;
    check(!output_bits_usesRs1 && !output_bits_writesRd && !output_bits_serializing, "Faulting CSR serialization");
    input_bits_instruction = 32'h0000100f;
    check(!output_bits_usesRs1 && !output_bits_usesRs2 && !output_bits_writesRd && !output_bits_serializing, "Faulting instruction synchronization");
'''


def execute_contract(parameters):
    config = dict(resetVector='0', physicalAddressBits=56, pmpEntries=0, enableInterrupts=True, enableC=parameters.get('enableC', False), **{key: parameters.get(key, False) for key in ('enableZba', 'enableZbb', 'enableZbs')},
                  memoryRegions=[dict(base='0', size=str(1 << 56), readable=True, writable=True, executable=True, device=False, atomic=True)])
    body = ''

    def check_instruction(word, operation, a, b=0, immediate=None):
        nonlocal body
        model = Model(config, {i: (word >> (8 * i)) & 255 for i in range(4)}, {})
        model.registers[1], model.registers[2], model.csrs[0x340] = a & MASK, b & MASK, 0x55aa5555aa55aa55
        address = word >> 20
        csr_value, legal = model.csrs.get(address, 0), address in model.csrs
        record = model.step()
        opcode, function = word & 127, (word >> 12) & 7
        csr_write = opcode == 0x73 and (function & 3 == 1 or (word >> 15) & 31 != 0)
        checks = [f'output_bits_instruction_fault == {record[7]}', f'output_bits_load == {int(opcode == 3)}',
                  f'output_bits_store == {int(opcode == 0x23)}', 'output_bits_atomic == 0', f'output_bits_csrWrite == {int(csr_write)}']
        if record[7]:
            checks += [f'output_bits_instruction_cause == 64\'h{record[8]:x}', f'output_bits_instruction_tval == 64\'h{record[9]:x}']
        else:
            checks += [f'output_bits_nextPc == 64\'h{record[3]:x}']
            if opcode not in (3, 0x23):
                checks += [f'output_bits_value == 64\'h{record[6]:x}']
            if opcode == 0x73:
                checks += [f'output_bits_csrData == 64\'h{model.csrs[address]:x}']
            if opcode in (3, 0x23):
                checks += [f'output_bits_memorySize == {function & 3}', f'output_bits_unsignedLoad == {int(opcode == 3 and function >= 4)}',
                           f'output_bits_address == 64\'h{a + (signed(word >> 20, 12) if opcode == 3 else immediate):x}']
        value = signed(word >> 20, 12) if immediate is None else immediate
        body += f'''    input_valid = 1; input_bits_decoded_instruction_instruction = 32'h{word:08x}; input_bits_decoded_instruction_length = 4;
    input_bits_decoded_operation = {operation}; input_bits_decoded_rd = {(word >> 7) & 31}; input_bits_decoded_rs1 = {(word >> 15) & 31};
    input_bits_decoded_writesRd = {int(opcode not in (0x23, 0x63))}; input_bits_decoded_immediate = 64'h{value & MASK:x};
    input_bits_operand1 = 64'h{a & MASK:x}; input_bits_operand2 = 64'h{b & MASK:x}; csrValue = 64'h{csr_value:x}; csrLegal = {int(legal)};
'''
        for ready in (0, 1):
            body += f'    output_ready = {ready}; check(output_valid && input_ready == {ready} && ' + ' && '.join(checks) + f', "Scalar execution {word:08x}");\n'

    pairs = ((0, 0), (1, 63), (MASK, 64), (1 << 63, 65), ((1 << 63) - 1, MASK), (0x80000000, 32), (0xffffffff, 31))
    for word in (False, True):
        for a, b in pairs:
            for function, upper in (((f, 0) for f in range(8)) if not word else ((0, 0), (1, 0), (5, 0))):
                check_instruction(alu(6, 1, 2, function, word, upper=upper), 24 if word else 4 if function == 0 else 22, a, b)
            for function in (0, 5):
                check_instruction(alu(6, 1, 2, function, word, upper=32), 24 if word else 22, a, b)
            for function in ((0,) if word else (2, 3, 4, 6, 7)):
                for value in (-2048, -1, 0, 2047):
                    check_instruction(alu(6, 1, value, function, word, True), 23 if word else 21, a)
            for function, upper in ((1, 0), (5, 0), (5, 0x400)):
                for amount in ((0, 1, 31) if word else (0, 1, 32, 63)):
                    check_instruction(alu(6, 1, amount | upper, function, word, True), 23 if word else 21, a)
    random = __import__('random').Random(0x624)
    for name, (extension, encoding, mask) in BITMANIP_ENCODINGS.items():
        if not parameters.get('enable' + extension):
            continue
        operation = 22 if encoding & 127 in (0x33, 0x3b) and mask != 0xfff0707f else 21
        for a, b in (*pairs, *((random.getrandbits(64), random.getrandbits(64)) for _ in range(12))):
            for amount in ((0, 1, 31, 32, 63) if mask == 0xfc00707f else (0, 1, 31) if name == 'roriw' else (0,)):
                rs2 = amount if mask == 0xfc00707f or name == 'roriw' else 0 if mask == 0xfff0707f else 2
                instruction = encoding | (1 << 15) | (6 << 7) | (rs2 << 20)
                check_instruction(instruction, operation, a, b)
    for function in (1, 4, 5, 6, 7):
        for a, b in pairs:
            for offset in (2, 8):
                check_instruction(beq(1, 2, offset) | (function << 12), 25, a, b, offset)
    for function in (3, 5, 6, 7):
        for source in (0, 1, 31):
            for address in (0x340, 0xf14, 0x777):
                check_instruction(csr(6, address, source, function=function), 28, 0)
    for size in (0, 1):
        for unsigned in (False, True):
            check_instruction(load(6, 1, 4, size, unsigned), 26, 0x1000)
        check_instruction(store(2, 1, 4, size), 27, 0x1000, MASK, 4)
    for operation, size in ((op, size) for op in (*ATOMIC_OPERATIONS, 2, 3) for size in (2, 3)):
        for order in range(4):
            body += f'''    input_bits_decoded_operation = {15 if operation == 0 and size == 3 else 30}; input_bits_decoded_immediate = 0;
    input_bits_decoded_instruction_instruction = 32'h{amo(operation, 6, 1, 0 if operation == 2 else 2, order, size):x};
    input_bits_decoded_writesRd = 1; input_bits_operand1 = 'h1000; input_bits_operand2 = 64'h{0 if operation == 2 else MASK:x};
    check(output_valid && output_bits_atomic && output_bits_load == {int(operation != 3)} && output_bits_store == {int(operation != 2)} && output_bits_memorySize == {size} && output_bits_address == 'h1000 && output_bits_storeData == 64'h{0 if operation == 2 else MASK:x}, "Atomic execution metadata");
'''
    body += '''    input_bits_decoded_operation = 12; input_bits_decoded_writesRd = 0;
    input_bits_decoded_instruction_instruction = 32'h00100073; input_bits_decoded_instruction_pc = 'h104;
    input_bits_decoded_instruction_fault = 0;
'''
    for privilege in (3, 1, 0):
        for ready in (0, 1):
            body += f'''    privilege = {privilege}; output_ready = {ready};
    check(output_valid && input_ready == {ready} && output_bits_instruction_fault && output_bits_instruction_cause == 3 &&
      output_bits_instruction_tval == 'h104 && !output_bits_rdWrite && !output_bits_load && !output_bits_store &&
      !output_bits_atomic && !output_bits_csrWrite && !output_bits_mret && !output_bits_sret, "Breakpoint exception and effects");
'''
    body += '''    input_bits_decoded_instruction_fault = 1; input_bits_decoded_instruction_cause = 1;
    input_bits_decoded_instruction_tval = 'habc;
    check(output_bits_instruction_cause == 1 && output_bits_instruction_tval == 'habc, "Prior fetch fault precedes breakpoint");
    input_bits_decoded_instruction_fault = 0; privilege = 3;
'''
    if parameters.get('enableC'):
        body = re.sub(r"(input_bits_decoded_instruction_instruction = [^;]+;)",
                      r"\1 input_bits_decoded_functionCode = {input_bits_decoded_instruction_instruction[30], input_bits_decoded_instruction_instruction[14:12]};", body)
    return body


def memory_contract(parameters):
    base = int(parameters['resetVector'])
    cases = ((0x1000, 0, 1, 0, 1, True), (0x1002, 1, 1, 0, 2, True),
             (0x1004, 2, 0, 0, 0, True), (0x1008, 3, 1, 0, 0xff, True),
             (0x4000, 3, 0, 0, 0, True), (0x4000, 3, 1, 0, 0xff, False),
             (0x5000, 2, 0, 1, 0, False), (0x7000, 3, 0, 0, 0, True),
             (0x1000, 4, 0, 0, 0, False), (0x1001, 3, 0, 0, 0, False),
             (0x1000, 1, 1, 0, 0, False), (0x1000, 1, 1, 0, 4, False),
             (1 << parameters['physicalAddressBits'], 3, 0, 0, 0, False),
             (0x8000, 2, 0, 1, 0, True), (0x8000, 2, 0, 0, 0, False))
    cases = tuple((*case[:-1], 0, case[-1]) for case in cases)
    ram_atomic = parameters.get('enableA', True) and any(r.get('atomic', False) and int(r['base']) <= base + 0x1000 < int(r['base']) + int(r['size'])
                     for r in parameters['memoryRegions'])
    cases += ((0x1000, 3, 1, 0, 255, 1, ram_atomic),
              (0x1000, 3, 0, 0, 255, 1, False), (0x1000, 3, 1, 1, 255, 1, False),
              (0x1000, 2, 1, 0, 15, 1, ram_atomic), (0x1000, 3, 1, 0, 127, 1, False),
              (0x1001, 3, 1, 0, 255, 1, False), (0x4000, 3, 1, 0, 255, 1, False),
              (0x5000, 3, 1, 0, 255, 1, False), (0x7000, 3, 1, 0, 255, 1, False),
              (0x8000, 3, 1, 0, 255, 1, False))
    cases = tuple((*case[:-1], 0, 0, case[-1]) for case in cases)
    cases += tuple((0x1000, 3, int(op != 2), 0, 0 if op == 2 else 255, 1, op, int(op == 3), ram_atomic) for op in (1, 2, 3, 8))
    cases += ((0x1000, 3, 1, 0, 255, 1, 3, 0, ram_atomic),
              (0x1000, 3, 1, 0, 255, 1, 2, 0, False), (0x1000, 3, 0, 0, 0, 1, 3, 1, False))
    cases += tuple((0x1000, 3, 1, 0, 255, 1, op, 0, ram_atomic and op in ATOMIC_OPERATIONS) for op in (4, 5, 12, 16, 20, 24, 28))
    cases += tuple((0x1004, size, int(op != 2), 0, 0 if op == 2 else (1 << (1 << size)) - 1, 1, op, 0, ram_atomic and size == 2) for op in (*ATOMIC_OPERATIONS, 2, 3) for size in (2, 3))
    for fetch in (0, 1):
        enabled = parameters.get('enableBurstRefill') if fetch else parameters.get('dCacheRefillBytes') == 64
        cacheable = any(r.get('dataCacheable') and not r['device'] and r['readable'] and
                        int(r['base']) <= base + 0x1000 and base + 0x1040 <= int(r['base']) + int(r['size'])
                        for r in parameters['memoryRegions'])
        cases += tuple((offset, 6, write, fetch, 0, atomic, 0, 0, bool(enabled and valid and (fetch or cacheable)))
                       for offset, write, atomic, valid in ((0x1000, 0, 0, True), (0x1004, 0, 0, False),
                       (0x1000, 1, 0, False), (0x1000, 0, 1, False), (0x5000, 0, 0, False), (0x3fe0, 0, 0, False)))
    body = ''
    for tag, (offset, size, write, fetch, mask, atomic, operation, eligible, allowed) in enumerate(cases, 1):
        body += f'''    upstream_request_bits_address = 64'h{base + offset:x};
    upstream_request_bits_size = {size}; upstream_request_bits_write = {write};
    upstream_request_bits_fetch = {fetch}; upstream_request_bits_mask = {mask};
    upstream_request_bits_atomic = {atomic};
    upstream_request_bits_atomicOperation = {operation}; upstream_request_bits_scEligible = {eligible};
    upstream_request_bits_tag = {tag}; upstream_request_valid = 1;
    check(downstream_request_valid == {int(allowed)} && upstream_request_ready == {int(not allowed)}, "Memory permission and shape {tag}");
'''
        if allowed:
            body += f'''    repeat (3) begin
      check(downstream_request_valid && downstream_request_bits_tag == {tag} && downstream_request_bits_atomic == {atomic} && downstream_request_bits_atomicOperation == {operation} && downstream_request_bits_scEligible == {eligible} && !upstream_request_ready, "Memory request backpressure {tag}");
      tick();
    end
    downstream_request_ready = 1; tick(); downstream_request_ready = 0;
    downstream_response_valid = 1; downstream_response_bits_tag = {tag};
    downstream_response_bits_data = 64'hfedcba9876543210;
'''
        else:
            body += '    tick();\n'
        body += f'''    upstream_request_valid = 0;
    for (integer chunk = 0; chunk < {8 if allowed and size == 6 else 1}; chunk++) begin
    downstream_response_bits_last = chunk == {7 if allowed and size == 6 else 0};
    repeat (3) begin
      check(upstream_response_valid && upstream_response_bits_fault == {int(not allowed)} && upstream_response_bits_tag == {tag} && upstream_response_bits_last == {"downstream_response_bits_last" if allowed else "1"} && !downstream_request_valid && !upstream_request_ready, "Memory response backpressure {tag}");
      tick();
    end
    upstream_response_ready = 1; tick(); upstream_response_ready = 0;
    end
    downstream_response_valid = 0;
'''
    return body


def axi_cache_attributes(parameters):
    regions = ''
    if parameters.get('l2CacheBytes'):
        for r in parameters['memoryRegions']:
            if r['device']:
                continue
            lower = f"address >= 64'd{int(r['base'])} && " if int(r['base']) else ''
            regions += f'''    if ({lower}address + bytes <= 64'd{int(r['base']) + int(r['size'])})
      expected_cache = !locked && (fetch ? {int(r['executable'])} : {int(r['readable'] and r.get('dataCacheable', False))}) ? (write_access ? 6 : 14) : 2;
'''
    return '''  function automatic logic [3:0] expected_cache(input logic [63:0] address,
      input integer bytes, input bit fetch, write_access, locked);
    expected_cache = 0;
''' + regions + '  endfunction\n'


def axi_contract(width, harts, enable_a=True):
    bus_bytes = width // 8
    read_data = sum((0xa0 + byte) << (8 * byte) for byte in range(bus_bytes))
    write_data = 0x8877665544332211
    body, tag = '', 0
    for size in range(4):
        byte_count = 1 << size
        mask = (1 << byte_count) - (2 if byte_count > 1 else 1)
        for lane in range(0, bus_bytes, byte_count):
            for write in (0, 1):
                tag += 1
                body += f'''    memory_request_bits_address = 64'h{0x1000 + lane:x};
    memory_request_bits_data = 64'h{write_data:x}; memory_request_bits_mask = {mask};
    memory_request_bits_size = {size}; memory_request_bits_write = {write};
    memory_request_bits_tag = {tag}; memory_request_valid = 1;
    tick(); memory_request_valid = 0; memory_request_bits_tag = 0;
'''
                if write:
                    shifted = (write_data << (8 * lane)) & ((1 << width) - 1)
                    body += f'''    repeat (3) begin
      check(axi_aw_valid && axi_w_valid && !axi_ar_valid && axi_aw_bits_addr == 'h{0x1000 + lane:x} && axi_aw_bits_size == {size} && axi_w_bits_strb == 'h{mask << lane:x} && axi_w_bits_data == 'h{shifted:x}, "AXI write lanes {tag}");
      tick();
    end
    axi_aw_ready = 1; axi_w_ready = 1; tick(); axi_aw_ready = 0; axi_w_ready = 0;
    axi_b_valid = 1; tick(); axi_b_valid = 0;
'''
                    expected = 0
                else:
                    body += f'''    check(axi_ar_valid && !axi_aw_valid && !axi_w_valid && axi_ar_bits_addr == 'h{0x1000 + lane:x} && axi_ar_bits_size == {size}, "AXI read lanes {tag}");
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    axi_r_bits_data = 'h{read_data:x}; axi_r_bits_last = 1; axi_r_valid = 1;
    tick(); axi_r_valid = 0;
'''
                    expected = (read_data >> (8 * lane)) & ((1 << (8 * byte_count)) - 1)
                body += f'''    repeat (3) begin
      check(memory_response_valid && !memory_response_bits_fault && memory_response_bits_tag == {tag} && memory_response_bits_data == 64'h{expected:x}, "AXI response tag and zero extension {tag}");
      tick();
    end
    memory_response_ready = 1; tick(); memory_response_ready = 0;
'''
    return body + (axi_atomic_contract(width) + axi_reservation_contract(width, harts) if enable_a else '')


def axi_atomic_contract(width):
    body = ''
    cases = ((1, 0, 1, 0, 0, False), (1, 0, 1, 0, 2, False),
             (0, 0, 1, 0, 0, False), (2, 0, 1, 0, 0, False),
             (3, 0, 1, 0, 0, False), (1, 1, 1, 0, 0, False),
             (1, 0, 2, 0, 0, False), (1, 0, 3, 0, 0, False),
             (1, 0, 1, 1, 0, False), (1, 0, 0, 1, 0, False),
             (1, 0, 1, 0, 0, True))
    cases = tuple((0, *case) for case in cases) + tuple((op, 1, 0, 1, 0, retries, False) for op in (1, 8) for retries in (0, 2))
    cases = tuple((size, *case, -3, 5) for size in (2, 3) for case in cases) + tuple(
        (size, op, 1, 0, 1, 0, 0, False, a, b) for size in (2, 3) for op in ATOMIC_OPERATIONS
        for a, b in ((0, -1), (-1, 0), (0x80000000, 1), (0x7fffffff, 0xffffffff), (1 << 63, 1), ((1 << 63)-1, 1 << 63)))
    for index, (size, operation, read_resp, read_id, write_resp, write_id, retries, malformed, initial, operand) in enumerate(cases):
        lane = width // 8 - (1 << size)
        shift, mask = lane * 8, (1 << (8 << size)) - 1
        operand &= mask
        body += f'''
    memory_request_bits_atomic = 1; memory_request_bits_write = 1; memory_request_bits_atomicOperation = {operation};
    memory_request_bits_address = 'h{0x1000 + lane:x}; memory_request_bits_size = {size};
    memory_request_bits_mask = {(1 << (1 << size)) - 1}; memory_request_bits_data = 64'h{operand:x}; memory_request_bits_tag = 201;
    memory_request_valid = 1; tick(); memory_request_valid = 0;
    memory_request_bits_atomic = 0; memory_request_bits_data = 99; memory_request_bits_address = 0;
'''
        fault = read_resp != 1 or read_id != 0 or write_resp != 1 or write_id != 0 or malformed
        for attempt in range(retries + 1):
            old = (initial + attempt * 11) & mask
            value = atomic_value(operation, old, operand, 1 << size)
            body += f'''
    repeat (3) begin
      check(axi_ar_valid && !axi_aw_valid && !axi_w_valid && !memory_response_valid && !memory_request_ready && axi_ar_bits_lock && axi_ar_bits_addr == 'h{0x1000 + lane:x} && axi_ar_bits_id == 0 && axi_ar_bits_len == 0 && axi_ar_bits_size == {size}, "Exclusive read ownership"); tick();
    end
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    repeat (2) begin check(axi_r_ready && !memory_response_valid && !axi_aw_valid, "Exclusive read response wait"); tick(); end
    axi_r_valid = 1; axi_r_bits_resp = {read_resp}; axi_r_bits_id = {read_id};
    axi_r_bits_data = 'h{old << shift:x}; axi_r_bits_last = {int(not malformed)};
    tick(); axi_r_valid = 0;
'''
            if malformed:
                body += '''
    repeat (3) begin check(axi_r_ready && !axi_aw_valid && !axi_w_valid && !memory_response_valid, "Malformed exclusive read drains"); tick(); end
    axi_r_valid = 1; axi_r_bits_last = 1; tick(); axi_r_valid = 0;
'''
            if read_resp == 1 and read_id == 0 and not malformed:
                body += f'''
    repeat (3) begin
      check(axi_aw_valid && axi_w_valid && !axi_ar_valid && !memory_response_valid && !memory_request_ready && axi_aw_bits_lock && axi_aw_bits_addr == 'h{0x1000 + lane:x} && axi_aw_bits_id == 0 && axi_aw_bits_len == 0 && axi_aw_bits_size == {size} && axi_w_bits_data == 'h{value << shift:x} && axi_w_bits_strb == 'h{((1 << (1 << size)) - 1) << lane:x} && axi_w_bits_last, "Exclusive sum and captured operand"); tick();
    end
'''
                first, second = ('aw', 'w') if (index + attempt) % 2 else ('w', 'aw')
                body += f'''
    axi_{first}_ready = 1; tick(); axi_{first}_ready = 0;
    repeat (3) begin check(!axi_{first}_valid && axi_{second}_valid && !axi_b_ready && !memory_response_valid, "Independent exclusive write handshakes"); tick(); end
    axi_{second}_ready = 1; tick(); axi_{second}_ready = 0;
    repeat (2) begin check(axi_b_ready && !memory_response_valid && !axi_ar_valid, "Exclusive write response wait"); tick(); end
    axi_b_valid = 1; axi_b_bits_resp = {0 if attempt < retries else write_resp}; axi_b_bits_id = {write_id};
    tick(); axi_b_valid = 0;
'''
        body += f'''
    repeat (3) begin
      check(memory_response_valid && memory_response_bits_fault == {int(fault)} && memory_response_bits_tag == 201 && {'1' if fault else f"memory_response_bits_data == 64'h{old:x}"} && !memory_request_ready && !axi_ar_valid && !axi_aw_valid && !axi_w_valid, "Atomic final response ownership"); tick();
    end
    memory_response_ready = 1; tick(); memory_response_ready = 0;
    check(memory_request_ready && !memory_response_valid, "Atomic slot reuse");
    axi_r_bits_id = 0; axi_b_bits_id = 0; axi_r_bits_resp = 0; axi_b_bits_resp = 0;
'''
    return body


def axi_reservation_contract(width, harts):
    lane, body = width // 8 - 8, ''
    for owner in sorted({0, harts - 1}):
        for operation, eligible, response, wrong_id in ((2, 0, 1, 0), (2, 0, 0, 0), (2, 0, 2, 0),
                (2, 0, 3, 0), (2, 0, 1, 1), (3, 0, 0, 0), (3, 1, 1, 0), (3, 1, 0, 0),
                (3, 1, 2, 0), (3, 1, 3, 0), (3, 1, 1, 1)):
            fault = wrong_id or (response != 1 if operation == 2 else response >= 2)
            value = 0xfedcba9876543210 if operation == 2 else int(not eligible or response == 0)
            body += f'''    hartId = {owner}; memory_request_bits_atomic = 1; memory_request_bits_atomicOperation = {operation};
    memory_request_bits_scEligible = {eligible}; memory_request_bits_write = {int(operation == 3)};
    memory_request_bits_address = 'h{0x1000 + lane:x}; memory_request_bits_size = 3;
    memory_request_bits_mask = {255 if operation == 3 else 0}; memory_request_bits_data = 19; memory_request_bits_tag = 199;
    memory_request_valid = 1; tick(); memory_request_valid = 0; hartId = {owner ^ 1};
    memory_request_bits_atomicOperation = 0; memory_request_bits_scEligible = 0;
'''
            if operation == 2:
                body += f'''    repeat (3) begin
      check(axi_ar_valid && axi_ar_bits_addr == 'h{0x1000 + lane:x} && axi_ar_bits_id == {owner} && axi_ar_bits_lock && axi_ar_bits_size == 3 && !axi_aw_valid && !axi_w_valid, "LR captured identity and read-only ownership"); tick();
    end
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    axi_r_valid = 1; axi_r_bits_last = 1; axi_r_bits_id = {owner ^ wrong_id}; axi_r_bits_resp = {response};
    axi_r_bits_data = {width}'h{value << (8 * lane):x}; tick(); axi_r_valid = 0;
'''
            elif eligible:
                body += f'''    repeat (3) begin
      check(axi_aw_valid && axi_w_valid && axi_aw_bits_addr == 'h{0x1000 + lane:x} && axi_aw_bits_id == {owner} && axi_aw_bits_lock && axi_aw_bits_size == 3 && !axi_ar_valid && axi_w_bits_data == {width}'h{19 << (8 * lane):x} && axi_w_bits_strb == 'h{255 << lane:x}, "SC captured single write"); tick();
    end
    axi_w_ready = 1; tick(); axi_w_ready = 0;
    repeat (3) begin check(axi_aw_valid && !axi_w_valid && !axi_ar_valid && !axi_b_ready, "SC independent write handshakes"); tick(); end
    axi_aw_ready = 1; tick(); axi_aw_ready = 0;
    axi_b_valid = 1; axi_b_bits_id = {owner ^ wrong_id}; axi_b_bits_resp = {response}; tick(); axi_b_valid = 0;
'''
            body += f'''    repeat (3) begin
      check(memory_response_valid && memory_response_bits_tag == 199 && memory_response_bits_fault == {int(fault)} && memory_response_bits_data == 64'h{value:x} && !axi_ar_valid && !axi_aw_valid && !axi_w_valid && !memory_request_ready, "LR/SC completion without extra transaction or retry"); tick();
    end
    memory_response_ready = 1; tick(); memory_response_ready = 0;
'''
    return body


def frontend_contract(parameters):
    base = int(parameters['resetVector'])
    return f'''
    check(memory_request_valid && memory_request_bits_address == 64'h{base:x} && memory_request_bits_tag == 0, "Initial frontend request");
    repeat (3) tick();
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_valid = 1; memory_response_bits_tag = 0;
    memory_response_bits_data = 64'h12345037;
    tick(); memory_response_valid = 0;
    repeat (3) begin
      check(output_valid && output_bits_pc == 64'h{base:x} && output_bits_tag == 0 && output_bits_length == 4 && output_bits_instruction == 32'h12345037, "Frontend result hold");
      tick();
    end
    output_ready = 1; tick(); output_ready = 0;
    tick();
    check(memory_request_valid && memory_request_bits_address == 64'h{base+4:x} && memory_request_bits_tag == 1, "Sequential frontend PC");
    redirect = 1; redirectPc = 64'h{base+0x100:x}; tick(); redirect = 0;
    repeat (3) begin
      check(memory_request_valid && memory_request_bits_address == 64'h{base+4:x} && memory_request_bits_tag == 1, "Redirect request stability");
      tick();
    end
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_valid = 1; memory_response_bits_fault = 1; memory_response_bits_tag = 1;
    tick(); memory_response_valid = 0; memory_response_bits_fault = 0;
    check(!output_valid, "Late cancelled fault escaped");
    tick(); tick();
    check(memory_request_valid && memory_request_bits_address == 64'h{base+0x100:x} && memory_request_bits_tag == 2, "Redirect target request");
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_valid = 1; memory_response_bits_tag = 2;
    tick(); memory_response_valid = 0;
    check(output_valid && output_bits_pc == 64'h{base+0x100:x}, "Redirect target delivery");
    output_ready = 1; redirect = 1; redirectPc = 64'h{base+0x200:x};
    tick(); output_ready = 0; redirect = 0;
    tick();
    check(memory_request_valid && memory_request_bits_address == 64'h{base+0x200:x} && memory_request_bits_tag == 3, "Redirect priority over output consumption");
'''


def prediction_contract(parameters):
    entries = parameters.get('branchPredictorEntries', 0)
    if not entries or not parameters.get('iCacheBytes') or not parameters.get('enableBurstRefill') or parameters.get('virtualAddressBits') == 39:
        return ''
    base = int(parameters['resetVector'])
    body = '    begin: prediction_contract\n      logic [7:0] service_tag;\n    privilege = 3;\n'
    if parameters.get('pmpEntries'):
        body += "    pmp_config = '0; pmp_address = '0;\n"
    scenarios = ((True, [1], 0, 1, False), (False, [1, 0], 0, 1, False),
                 (True, [1]*5+[0], 0, 1, False), (False, [0]*5+[1], 0, 1, False),
                 (False, [1], 4*entries, 1, False), (False, [1], 1 << 32, 1, False),
                 (False, [1], 0, 1, True), (False, [1], 0, 0, False),
                 (True, [1], 0, 0, False), (True, [1], 0, 0, False))
    for phase, (taken, history, alias, conditional, clear) in enumerate(scenarios):
        indirect = phase >= len(scenarios)-2
        pc = base + (0x404 if indirect else 4 * (entries - 1))
        denied = phase == len(scenarios)-1
        target = base + (0x6000 if denied else 0x14) if indirect else pc + 12
        line = pc & ~63
        instruction = 0x00008067 if indirect else 0x00000663
        body += f'''    halt = 1; prediction_valid = 0; prediction_clear = 0; redirect = 0; invalidate = 0;
    memory_request_ready = 0; memory_response_valid = 0; memory_response_bits_fault = 0; output_ready = 0;
    reset = 1; tick(); reset = 0; tick();
    prediction_pc = 64'h{pc+alias:x}; prediction_conditional = {conditional};
'''
        for outcome in history:
            body += f'''    prediction_valid = 1; prediction_clear = {int(clear)}; prediction_taken = {outcome};
    prediction_nextPc = 64'h{target if outcome else pc+4:x}; tick();
'''
        body += f'''    prediction_valid = 0; prediction_clear = 0;
    redirect = 1; redirectPc = 64'h{pc:x}; tick(); redirect = 0; halt = 0;
    while (!memory_request_valid) tick();
    check(memory_request_bits_address == 64'h{line:x} && memory_request_bits_size == 6,
          "Prediction still uses the real instruction refill path");
    service_tag = memory_request_bits_tag;
    memory_request_ready = 1; tick(); memory_request_ready = 0;
'''
        for beat in range(8):
            low = instruction if line+8*beat == pc else 0x13
            high = instruction if line+8*beat+4 == pc else 0x13
            body += f'''    memory_response_bits_tag = service_tag; memory_response_bits_data = 64'h{high:08x}{low:08x};
    memory_response_bits_last = {int(beat == 7)}; memory_response_valid = 1;
    while (!memory_response_ready) tick(); tick(); memory_response_valid = 0;
'''
        body += f'''    while (!output_valid) tick();
    check(output_bits_packets_0_pc == 64'h{pc:x} && output_bits_packets_0_instruction == 32'h{instruction:08x} &&
          output_bits_packets_0_predictedTaken == {int(taken)} && output_bits_packets_0_predictedPc == 64'h{target if taken else 0:x},
          "Prediction direction, full tag, target and clear priority");
    prediction_clear = 1; prediction_valid = 1; prediction_taken = 0;
    repeat (3) begin
      check(output_valid && output_bits_packets_0_pc == 64'h{pc:x} &&
            output_bits_packets_0_predictedTaken == {int(taken)} && output_bits_packets_0_predictedPc == 64'h{target if taken else 0:x},
            "Queued prediction metadata survives table updates and backpressure"); tick();
    end
'''
        if denied:
            body += f'''    output_ready = 1; tick(); output_ready = 0;
    while (!output_valid) begin check(!memory_request_valid, "Prediction never authorizes a denied target"); tick(); end
    check(output_bits_packets_0_pc == 64'h{target:x} && output_bits_packets_0_fault &&
          output_bits_packets_0_cause == 1 && output_bits_packets_0_tval == 64'h{target:x} && !memory_request_valid,
          "Predicted target still receives the real instruction access fault");
'''
    return body + '    prediction_clear = 0; prediction_valid = 0;\n    $display("PREDICTION_CONTRACT 10");\n    end\n'


def instruction_cache_contract(parameters):
    base = int(parameters['resetVector'])
    burst = parameters.get('enableBurstRefill')
    banks = 1 if parameters.get('enableC') else 1 << (parameters['issueWidth'] - 1).bit_length()
    body = f'''
    allowed = 1; upstream_request_valid = 1;
    upstream_request_bits_address = 'h{base:x}; upstream_request_bits_tag = 33;
    upstream_request_bits_fetch = 1; upstream_request_bits_size = {banks.bit_length()+1};
    while (!upstream_request_ready) tick(); tick(); upstream_request_valid = 0;
'''
    for beat in range(8 if burst else 16):
        if not burst or beat == 0:
            address = base if burst else base + 4 * beat
            body += f'''
    while (!downstream_request_valid) tick();
    check(downstream_request_bits_address == 'h{address:x} && downstream_request_bits_size == {6 if burst else 2}, "Native refill address");
    downstream_request_ready = 1; tick(); downstream_request_ready = 0;
'''
        data = ((0x10000000 + 2 * beat + 1) << 32 | (0x10000000 + 2 * beat)) if burst else 0x10000000 + beat
        body += f'''
    downstream_response_bits_data = 64'h{data:x}; downstream_response_bits_tag = 33;
    downstream_response_bits_last = {int(not burst or beat == 7)}; downstream_response_valid = 1;
    while (!downstream_response_ready) tick(); tick(); downstream_response_valid = 0;
'''
    body += f'''
    while (!upstream_response_valid) tick();
    {f'check(upstream_response_bits_count == 1, "Miss returns the demanded word only");' if banks > 1 else ''}
    repeat (3) begin
      check(upstream_response_bits_data == 'h10000000 && !upstream_response_bits_fault, "Native refill completion hold"); tick();
    end
    upstream_response_ready = 1; upstream_request_valid = 1;
    upstream_request_bits_address = 'h{base:x}; upstream_request_bits_tag = 64;
    upstream_request_bits_size = 2;
    check(upstream_request_ready, "Completion did not release lookup credit"); tick();
    for (integer beat = 0; beat < 64; beat++) begin
      check(upstream_response_valid && !upstream_response_bits_fault && upstream_response_bits_tag == 64 + beat &&
        upstream_response_bits_data == 'h10000000 + (beat % 16) && !downstream_request_valid, "Native one-cycle hit stream");
      upstream_request_bits_address = 'h{base:x} + 4 * ((beat + 1) % 16);
      upstream_request_bits_tag = 65 + beat;
      upstream_request_valid = beat != 63;
      check(upstream_request_ready, "Hit response blocked the next lookup"); tick();
    end
    upstream_request_valid = 1; upstream_request_bits_address = 'h{base+4:x}; upstream_request_bits_tag = 7;
    tick(); upstream_request_valid = 0; upstream_response_ready = 0;
    repeat (3) begin
      check(upstream_response_valid && upstream_response_bits_data == 'h10000001 && upstream_response_bits_tag == 7 &&
        !upstream_request_ready, "Native hit under backpressure"); tick();
    end
'''
    if banks > 1:
        body += '    upstream_response_ready = 1; tick(); upstream_response_ready = 0;\n'
        for size in (2, banks.bit_length() + 1):
            for offset in range(16):
                count = 1 if size == 2 else banks - offset % banks
                value = sum((0x10000000 + offset + lane) << (32 * lane) for lane in range(count))
                body += f'''    upstream_request_valid = 1; upstream_request_bits_address = 'h{base + 4 * offset:x};
    upstream_request_bits_size = {size}; upstream_request_bits_tag = {offset};
    check(upstream_request_ready, "Bank lookup admission"); tick(); upstream_request_valid = 0;
    repeat (3) begin
      check(upstream_response_valid && !upstream_response_bits_fault && upstream_response_bits_count == {count} &&
        upstream_response_bits_data == 'h{value:x} && upstream_response_bits_tag == {offset} &&
        !downstream_request_valid && !upstream_request_ready, "Bank suffix and stable return"); tick();
    end
    upstream_response_ready = 1; tick(); upstream_response_ready = 0;
'''
        body += f'''    upstream_response_ready = 1; upstream_request_valid = 1;
    upstream_request_bits_address = 'h{base:x}; upstream_request_bits_size = {banks.bit_length()+1};
    upstream_request_bits_tag = 64; tick();
'''
        for beat in range(64):
            offset = banks * (beat % (16 // banks))
            value = sum((0x10000000 + offset + lane) << (32 * lane) for lane in range(banks))
            body += f'''    check(upstream_response_valid && !upstream_response_bits_fault &&
      upstream_response_bits_count == {banks} && upstream_response_bits_data == 'h{value:x} &&
      upstream_response_bits_tag == {64+beat} && !downstream_request_valid, "Native full-bank hit stream");
    upstream_request_bits_address = 'h{base + 4 * banks * ((beat + 1) % (16 // banks)):x};
    upstream_request_bits_tag = {65+beat}; upstream_request_valid = {int(beat != 63)};
    check(upstream_request_ready, "Full-bank response blocked the next lookup"); tick();
'''
    return body + f'''
    upstream_response_ready = 1; upstream_request_valid = 1;
    upstream_request_bits_address = 'h{base+64:x}; upstream_request_bits_tag = 8; upstream_request_bits_size = 2; tick();
    check(!upstream_request_ready && !upstream_response_valid, "Miss admitted a younger lookup");
    upstream_request_valid = 0;
'''


def cached_fetch_contract(parameters, frontend=False):
    base = int(parameters['resetVector'])
    line = base if frontend else base + 0x100

    def request(address, tag):
        return f'''    request_bits_pc = 'h{address:x}; request_bits_tag = {tag}; request_valid = 1;
    #1; while (!request_ready) tick(); tick(); request_valid = 0;
'''

    def respond(address, value, fault=0):
        return f'''    while (!memory_request_valid) begin check(!output_valid, "Incomplete cache refill escaped"); tick(); end
    check(memory_request_bits_address == 'h{address:x} && memory_request_bits_size == 2 && memory_request_bits_fetch && !memory_request_bits_write && !memory_request_bits_atomic, "Cache refill address and attributes");
    memory_response_bits_tag = memory_request_bits_tag;
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_valid = 1; memory_response_bits_data = {value}; memory_response_bits_fault = {fault};
    check(memory_response_ready, "Cache response ownership"); tick(); memory_response_valid = 0; memory_response_bits_fault = 0;
'''

    def refill(address):
        return '    for (integer beat = 0; beat < 16; beat++) begin\n' + respond(
            address, "32'h10000000 + beat").replace(f"memory_request_bits_address == 'h{address:x}", f"memory_request_bits_address == ('h{address:x} + 4 * beat)") + '    end\n'

    def output(address, value, fault=0):
        return f'''    while (!output_valid) tick();
    repeat (3) begin
      check(output_valid && output_bits_pc == 'h{address:x} && output_bits_instruction == {value} && output_bits_fault == {fault} && !memory_request_valid, "Cache output retention"); tick();
    end
    output_ready = 1; tick(); output_ready = 0;
'''

    body = '' if frontend else request(line + 4, 21)
    body += refill(line) + output(line if frontend else line + 4, "32'h10000000" if frontend else "32'h10000001")
    if frontend:
        body += output(line + 4, "32'h10000001")
        body += f'''    while (!output_valid) tick();
    check(output_bits_pc == 'h{line+8:x}, "Oldest unpublished frontend PC");
    invalidate = 1; check(!output_valid, "Invalidate delivered a stale instruction"); tick(); invalidate = 0;
'''
        body += refill(line) + output(line + 8, "32'h10000002")
        body += f'''    redirect = 1; invalidate = 1; redirectPc = 'h{base + 0x100:x}; tick(); redirect = 0; invalidate = 0;
'''
        body += refill(base + 0x100) + output(base + 0x100, "32'h10000000")
        forbidden = (max(int(r['base']) + int(r['size']) for r in parameters['memoryRegions']) + 3) & ~3
        return body + f'''
    redirect = 1; redirectPc = 'h{forbidden:x}; tick(); redirect = 0;
    while (!output_valid) tick();
    check(output_bits_fault && output_bits_pc == 'h{forbidden:x}, "Missing local fetch fault");
    invalidate = 1; tick(); invalidate = 0;
    while (!output_valid) tick();
    check(output_bits_fault && output_bits_pc == 'h{forbidden:x}, "Unpublished fault was not retried");
    output_ready = 1; tick(); output_ready = 0;
    invalidate = 1; tick(); invalidate = 0;
    repeat (3) begin check(!dut.fetch.request_valid, "Delivered fetch fault resumed after invalidate"); tick(); end
'''
    body += request(line + 8, 22) + output(line + 8, "32'h10000002")
    if parameters['pmpEntries']:
        body += f"    pmp_config = 'h90; pmp_address = 'h{(line + 8) >> 2:x};\n"
        body += request(line + 8, 23) + output(line + 8, '0', 1)
        body += '    pmp_config = 0; pmp_address = 0;\n'
    body += '    cancel = 1; invalidate = 1; tick(); cancel = 0; invalidate = 0;\n'
    if parameters['pmpEntries']:
        body += f"    pmp_config = 'h90; pmp_address = 'h{(line + 4) >> 2:x};\n"
        body += request(line + 8, 24) + respond(line, "32'h10000000") + respond(line + 8, "32'habcdef13")
        body += output(line + 8, "32'habcdef13") + '    pmp_config = 0; pmp_address = 0;\n'
    body += request(line + 8, 24) + respond(line, '0', 1) + respond(line + 8, "32'habcdef13")
    body += output(line + 8, "32'habcdef13")
    body += request(line + 8, 25)
    body += f'''    while (!memory_request_valid) tick();
    check(memory_request_bits_address == 'h{line:x}, "Faulting refill allocated a line");
    cancel = 1; invalidate = 1; tick(); cancel = 0; invalidate = 0;
    repeat (3) begin check(memory_request_valid && memory_request_bits_address == 'h{line:x} && !output_valid, "Cancelled cache request stability"); tick(); end
'''
    body += respond(line, "32'h10000000")
    body += '    while (!request_ready) begin check(!output_valid, "Cancelled cache output escaped"); tick(); end\n'
    body += request(line, 26) + respond(line, '0', 1) + output(line, '0', 1)
    for address, cause in ((line + 2, 0), (base + 0x6000, 1)):
        body += request(address, 27) + output(address, '0', 1)
        body += f'    check(output_bits_cause == {cause}, "Local instruction authorization fault");\n'
    return body


def frontend_group_contract(parameters):
    width = parameters['issueWidth']
    base = int(parameters['resetVector'])
    lane_checks = []
    for lane in range(width):
        packet = f'output_bits_packets_{lane}_'
        lane_checks.append(f"""
        if (held_offer && {lane} < held_count && !redirect && !invalidate) begin
          check({packet}pc == held_pc[{lane}] && {packet}instruction == held_word[{lane}] &&
            {packet}tag == held_tag[{lane}] && {packet}fault == held_fault[{lane}], "Stable instruction offer");
        end
        if (output_valid && output_ready && {lane} < output_bits_count) begin
          check({packet}pc == next_pc && {packet}length == 4, "Ordered instruction PC");
          if (phase == 5) begin
            check({packet}fault && {packet}cause == 1 && {packet}tval == next_pc, "Ordered fetch fault");
          end else begin
            check(!{packet}fault && {packet}instruction == (32'h13 | ((((next_pc - 'h{base:x}) >> 2) & 'h7ff) << 20)), "Ordered instruction data");
          end
          next_pc += 4; received += 1;
        end
        held_pc[{lane}] = {packet}pc; held_word[{lane}] = {packet}instruction;
        held_tag[{lane}] = {packet}tag; held_fault[{lane}] = {packet}fault;
""")
    body = f"""
    `undef CHECK
    `define CHECK(ok, message) if ((ok) !== 1'b1) $fatal(1, "%s", message)
    begin: grouped_frontend
      integer phase, cycle, received, target, beat, full_count, partial_count;
      logic bus_pending, bus_line, held_offer, started;
      logic [63:0] bus_address, service_address, next_pc;
      logic [7:0] bus_tag;
      logic [31:0] low_word, high_word;
      logic [63:0] held_pc [{width}]; logic [31:0] held_word [{width}];
      logic [7:0] held_tag [{width}]; logic held_fault [{width}];
      integer held_count;
      bus_pending = 0; held_offer = 0; full_count = 0; partial_count = 0;
      halt = 0; privilege = 3; memory_request_ready = 0; memory_response_valid = 0;
      {'pmp_config = 0; pmp_address = 0;' if parameters['pmpEntries'] else ''}
      reset = 1; tick(); tick(); reset = 0;
      for (phase = 0; phase < 6; phase += 1) begin
        cycle = 0; received = 0; started = 0;
        target = phase == 0 ? 256 : phase == 1 ? {64*width} : phase == 5 ? 1 : 96;
        if (phase == 0 || phase == 1 || phase == 4 || phase == 5)
          next_pc = 'h{base:x} + (phase == 5 ? 'h3000 : phase == 4 ? 'h204 : 'h200);
        while (received < target && cycle < 4000) begin
          redirect = cycle == 0 && (phase == 0 || phase == 1 || phase == 4 || phase == 5);
          redirectPc = next_pc;
          invalidate = phase == 3 && cycle == 0;
          halt = phase == 2 && cycle % 11 < 3;
          output_ready = phase != 2 || cycle % 7 >= 3;
          memory_request_ready = phase != 2 || cycle % 5 != 1;
          memory_response_valid = bus_pending;
          service_address = bus_address + (bus_line ? 8 * beat : 0);
          low_word = 32'h13 | ((((service_address - 'h{base:x}) >> 2) & 'h7ff) << 20);
          high_word = 32'h13 | ((((service_address + 4 - 'h{base:x}) >> 2) & 'h7ff) << 20);
          memory_response_bits_data = {{high_word, low_word}};
          memory_response_bits_tag = bus_tag;
          memory_response_bits_last = !bus_line || beat == 7;
          memory_response_bits_fault = bus_address >= 'h{base+0x3000:x};
          #1;
          if (redirect || invalidate) begin check(!output_valid, "Flush suppresses publication"); end
          if (output_valid) begin check(output_bits_count >= 1 && output_bits_count <= {width}, "Instruction group bounds"); end
          if (held_offer && !redirect && !invalidate) begin
            check(output_valid && output_bits_count == held_count, "Stable group count"); end
          if (phase == 1 && (started || output_valid)) begin
            check(output_valid && output_bits_count == {width}, "Continuous full-width native fetch");
            started = 1;
          end
          {''.join(lane_checks)}
          held_offer = output_valid && !output_ready; held_count = output_bits_count;
          if (output_valid && output_ready) begin
            if (output_bits_count == {width}) full_count += 1; else partial_count += 1;
          end
          if (memory_response_valid && memory_response_ready) begin
            if (memory_response_bits_last) bus_pending = 0; else beat += 1;
          end
          if (memory_request_valid && memory_request_ready) begin
            check(!bus_pending, "Single physical transaction");
            bus_pending = 1; bus_address = memory_request_bits_address; bus_tag = memory_request_bits_tag;
            bus_line = memory_request_bits_size == 6; beat = 0;
          end
          tick(); cycle += 1;
        end
        check(received >= target, "Frontend group progress");
      end
      output_ready = 1; memory_response_valid = 0; redirect = 0; invalidate = 0;
      repeat (8) begin check(!output_valid && !memory_request_valid, "Published fault stops fetching"); tick(); end
      check(full_count >= 64 && ({width} == 1 || partial_count > 0), "Full and partial groups exercised");
    end
"""
    if parameters.get('virtualAddressBits') == 39:
        body = body.replace('integer held_count;', 'integer held_count; logic translation_pending; logic [63:0] translated_address;')
        body = body.replace('bus_pending = 0; held_offer', 'translation_pending = 0; bus_pending = 0; held_offer')
        body = body.replace('          #1;', """          translation_request_ready = 1; translation_response_valid = translation_pending;
          translation_response_bits_address = translated_address; translation_response_bits_fault = 0;
          translation_response_bits_cause = 0;
          #1;
          if (phase == 1 && !translation_pending && translation_request_valid) begin
            translation_response_valid = 1; translation_response_bits_address = translation_request_bits_address;
          end
          #1;""")
        body = body.replace('          tick(); cycle += 1;', """          if (translation_response_valid && translation_response_ready) translation_pending = 0;
          if (translation_request_valid && translation_request_ready && !(translation_response_valid && translation_response_ready)) begin
            check(!translation_pending, "Single instruction translation");
            translation_pending = 1; translated_address = translation_request_bits_address;
          end
          tick(); cycle += 1;""")
    if not parameters.get('iCacheBytes'):
        body = body.replace('invalidate', "1'b0").replace("1'b0 = phase == 3 && cycle == 0;", '').replace("1'b0 = 0;", '')
        body = body.replace('if (phase == 1 && (started || output_valid))', 'if (0)')
        body = body.replace('full_count >= 64 &&', 'full_count >= 0 &&')
    return body


def wide_fetch_contract(parameters):
    banks = 1 if parameters.get('enableC') else 1 << (parameters['issueWidth'] - 1).bit_length()
    line = int(parameters['resetVector']) + 0x200
    translated = parameters.get('virtualAddressBits') == 39
    user_mode = bool(parameters.get('enableUserMode'))

    def offer(pc, tag):
        body = f'''    request_bits_pc = 'h{pc:x}; request_bits_tag = {tag}; request_valid = 1;
    {'translation_request_ready = 1;' if translated else ''}
    #1; while (!request_ready) tick(); tick(); request_valid = 0;
'''
        if translated:
            body += f'''    translation_request_ready = 0;
    translation_response_bits_address = 'h{pc:x}; translation_response_valid = 1;
    tick(); translation_response_valid = 0;
'''
        return body

    def expected(pc, tag, count, fault=False):
        words = [f'output_bits_instruction == {0 if fault else 0x20000000 + (pc-line)//4}']
        words += [f'output_bits_following_{i} == {0x20000000 + (pc-line)//4+i+1}' for i in range(count-1)]
        if fault:
            words += [f'output_bits_cause == 1 && output_bits_tval == \'h{pc:x}']
        return f'output_valid && output_bits_pc == \'h{pc:x} && output_bits_tag == {tag} && output_bits_count == {count} && output_bits_fault == {int(fault)} && ' + ' && '.join(words)

    def finish(pc, tag, count, fault=False):
        return f'''    while (!output_valid) begin check(!memory_request_valid, "Unexpected wide lookup miss"); tick(); end
    repeat (3) begin check({expected(pc, tag, count, fault)}, "Wide output suffix and hold"); tick(); end
    output_ready = 1; tick(); output_ready = 0;
'''

    body = '''    request_valid = 0; cancel = 0; invalidate = 0; output_ready = 0;
    memory_request_ready = 0; memory_response_valid = 0; memory_response_bits_fault = 0; memory_response_bits_last = 1;
    reset = 1; tick(); reset = 0; tick(); privilege = 3;
'''
    if translated:
        body += '    translation_request_ready = 0; translation_response_valid = 0; translation_response_bits_fault = 0; translation_response_bits_cause = 0;\n'
    if parameters['pmpEntries']:
        body += '    pmp_config = 0; pmp_address = 0;\n'
    body += offer(line, 1)
    burst = parameters.get('enableBurstRefill')
    for beat in range(8 if burst else 16):
        if not burst or beat == 0:
            body += f'''    while (!memory_request_valid) tick();
    check(memory_request_bits_address == 'h{line if burst else line+4*beat:x} && memory_request_bits_size == {6 if burst else 2}, "Wide cold refill stays physical");
    memory_response_bits_tag = memory_request_bits_tag;
    memory_request_ready = 1; tick(); memory_request_ready = 0;
'''
        value = ((0x20000000+2*beat+1) << 32 | (0x20000000+2*beat)) if burst else 0x20000000+beat
        body += f'''    memory_response_bits_data = 'h{value:x}; memory_response_bits_last = {int(not burst or beat == 7)};
    memory_response_valid = 1; while (!memory_response_ready) tick(); tick(); memory_response_valid = 0;
'''
    body += f'''    while (!output_valid) tick();
    check({expected(line, 1, 1)}, "Short miss return");
    output_ready = 1; request_valid = 1; request_bits_pc = 'h{line+64:x};
    check(!request_ready, "Short return admitted a younger lookup"); tick();
    request_valid = 0; output_ready = 0;
'''
    for offset in range(16):
        pc, tag = line + 4*offset, offset+2
        body += offer(pc, tag) + finish(pc, tag, banks-offset % banks)
    if not translated:
        body += offer(line, 64) + '    output_ready = 1;\n'
        for beat in range(64):
            pc = line + 4*banks*(beat % (16//banks))
            body += f'''    check({expected(pc, 64+beat, banks)}, "Wide one-cycle hit stream");
    request_valid = {int(beat != 63)}; request_bits_pc = 'h{line+4*banks*((beat+1) % (16//banks)):x}; request_bits_tag = {65+beat};
    check(request_ready, "Wide hit stream credit"); tick();
'''
        body += '    request_valid = 0; output_ready = 0;\n'
    if parameters['pmpEntries']:
        for offset in range(banks):
            pc = line + 4*offset
            body += f"    pmp_config = 'h94; pmp_address = 'h{pc >> 2:x}; privilege = {0 if user_mode else 3};\n"
            body += offer(pc, 200+offset) + '    privilege = 3;\n'
            body += finish(pc, 200+offset, 1)
        body += f"    pmp_config = 'h90; pmp_address = 'h{line >> 2:x};\n"
        body += offer(line, 220) + finish(line, 220, 1, True)
        body += f'    pmp_config = 0; privilege = {0 if user_mode else 3};\n'
        body += offer(line, 221) + '    privilege = 3;\n' + finish(line, 221, 1 if user_mode else banks, user_mode)
        body += f"    pmp_config = 'h94; pmp_address = 'h{line >> 2:x};\n"
        body += offer(line, 222) + '''    cancel = 1; check(!output_valid, "Cancelled scalar recheck escaped"); tick(); cancel = 0;
    repeat (3) begin check(!output_valid && !memory_request_valid, "Cancelled recheck started a lookup"); tick(); end
'''
        body += '    translation_request_ready = 1;\n' if translated else ''
        body += '    check(request_ready, "Cancelled recheck did not release ownership");\n'
        body += '    pmp_config = 0; pmp_address = 0;\n'
    for region in parameters['memoryRegions']:
        if region['executable'] and int(region['size']) == 8 and int(region['base']) % 16 == 8:
            pc = int(region['base'])
            body += offer(pc, 230) + f'''    while (!memory_request_valid) tick();
    check(memory_request_bits_address == 'h{pc:x} && memory_request_bits_size == 2, "PMA scalar fallback");
    memory_response_bits_tag = memory_request_bits_tag; memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_data = 'h{0x20000000 + (pc-line)//4:x}; memory_response_valid = 1;
    while (!memory_response_ready) tick(); tick(); memory_response_valid = 0;
''' + finish(pc, 230, 1)
    return body


def burst_fetch_contract(parameters, frontend=False):
    base = int(parameters['resetVector']) + (0 if frontend else 0x100)

    def request(address, tag):
        return f"    request_bits_pc = 'h{address:x}; request_bits_tag = {tag}; request_valid = 1; #1; while (!request_ready) tick(); tick(); request_valid = 0;\n"

    def line(address, fault=-1, cancel=-1, invalidate=-1, wrong_tag=False):
        body = f"""    while (!memory_request_valid) tick();
    check(memory_request_bits_address == 'h{address:x} && memory_request_bits_size == 6 && memory_request_bits_fetch && !memory_request_bits_write && !memory_request_bits_atomic, "Aligned protected line request");
    memory_response_bits_tag = memory_request_bits_tag ^ {int(wrong_tag)};
    memory_request_ready = 1; tick(); memory_request_ready = 0;
"""
        for chunk in range(8):
            body += f"""    repeat (2) begin check(!output_valid && !memory_request_valid, "Incomplete line cannot escape or relinquish ownership"); tick(); end
    memory_response_bits_data = 64'h{(0x10000001 + 2 * chunk) << 32 | (0x10000000 + 2 * chunk):x};
    memory_response_bits_last = {int(chunk == 7)}; memory_response_bits_fault = {int(chunk == fault)};
    memory_response_valid = 1; while (!memory_response_ready) tick();
    cancel = {int(chunk == cancel)}; invalidate = {int(chunk == invalidate)}; tick();
    memory_response_valid = 0; memory_response_bits_fault = 0; cancel = 0; invalidate = 0;
""".replace('cancel =', 'redirect =' if frontend else 'cancel =')
        return body

    def output(address, word, fault=0):
        return f"""    while (!output_valid) tick();
    repeat (3) begin check(output_bits_pc == 'h{address:x} && output_bits_instruction == 32'h{word:x} && output_bits_fault == {fault} && !memory_request_valid, "Demand word and output retention"); tick(); end
    output_ready = 1; tick(); output_ready = 0;
"""

    def scalar(address, fault=0):
        return f"""    while (!memory_request_valid) tick();
    check(memory_request_bits_address == 'h{address:x} && memory_request_bits_size == 2, "Line failure retries only original demand");
    memory_response_bits_tag = memory_request_bits_tag; memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_data = 'habcdef13; memory_response_bits_fault = {fault}; memory_response_bits_last = 1;
    memory_response_valid = 1; tick(); memory_response_valid = 0; memory_response_bits_fault = 0;
"""

    body = '' if frontend else request(base + 4, 21)
    body += line(base) + output(base if frontend else base + 4, 0x10000000 if frontend else 0x10000001)
    if frontend:
        return body + output(base + 4, 0x10000001)
    for word in range(16):
        body += request(base + 4 * word, 22) + output(base + 4 * word, 0x10000000 + word)
    for index, failure in enumerate((dict(fault=7), dict(fault=0), dict(wrong_tag=True))):
        body += '    invalidate = 1; tick(); invalidate = 0;\n'
        body += request(base + 8, 23 + index) + line(base, **failure) + scalar(base + 8) + output(base + 8, 0xabcdef13)
    for index, event in enumerate((dict(cancel=0), dict(cancel=7), dict(invalidate=7))):
        body += '    invalidate = 1; tick(); invalidate = 0;\n'
        body += request(base + 8, 30 + index) + line(base, **event)
        body += '    while (!request_ready) begin check(!output_valid, "Cancelled line cannot publish"); tick(); end\n'
        body += request(base + 8, 40 + index) + line(base) + output(base + 8, 0x10000002)
    if parameters['pmpEntries']:
        body += f"    invalidate = 1; tick(); invalidate = 0; pmp_config = 'h90; pmp_address = 'h{(base + 4) >> 2:x};\n"
        body += request(base + 8, 50) + scalar(base + 8) + output(base + 8, 0xabcdef13)
        body += request(base + 4, 51) + output(base + 4, 0, 1)
        body += '    pmp_config = 0; pmp_address = 0;\n'
    return body


def burst_axi_contract(parameters, fetch=True):
    width, bus_bytes = parameters['axiDataBits'], parameters['axiDataBits'] // 8
    beats, slices = 64 // bus_bytes, width // 64
    body = ''
    for error in ('none', 'response', 'id', 'early', 'missing'):
        if error == 'early' and beats == 1:
            continue
        body += f"""    hartId = 0; memory_request_bits_address = 'h1000; memory_request_bits_size = 6;
    memory_request_bits_write = 0; memory_request_bits_fetch = {int(fetch)}; memory_request_bits_atomic = 0;
    memory_request_bits_privileged = 0;
    memory_request_bits_tag = 219; memory_request_valid = 1; tick(); memory_request_valid = 0;
    repeat (3) begin check(axi_ar_valid && axi_ar_bits_len == {beats - 1} && axi_ar_bits_size == {bus_bytes.bit_length() - 1} && axi_ar_bits_burst == 1 && axi_ar_bits_prot == {int(fetch) * 4 + int(not parameters.get('enableUserMode'))} && !axi_ar_bits_lock, "Line AXI shape, protection and address retention"); tick(); end
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
"""
        for beat in range(1 if error == 'early' else beats):
            data = sum((byte + beat * bus_bytes + 1) << (8 * byte) for byte in range(bus_bytes))
            terminal = error == 'early' or (beat == beats - 1 and error != 'missing')
            bad = error in ('response', 'id', 'early') or error == 'missing' and beat == beats - 1
            body += f"""    axi_r_bits_data = {width}'h{data:x}; axi_r_bits_id = {int(error == 'id')}; axi_r_bits_resp = {2 if error == 'response' else 0}; axi_r_bits_last = {int(terminal)};
    axi_r_valid = 1; while (!axi_r_ready) tick(); tick(); axi_r_valid = 0;
"""
            for part in range(slices):
                body += f"""    while (!memory_response_valid) tick();
    repeat (3) begin check(memory_response_bits_data == 64'h{(data >> (64 * part)) & MASK:x} && memory_response_bits_tag == 219 && memory_response_bits_fault == {int(bad)} && memory_response_bits_last == {int(terminal and part == slices - 1)} && !memory_request_ready && !axi_ar_valid, "Serialized chunk data, error, last and retained ownership"); tick(); end
    memory_response_ready = 1; tick(); memory_response_ready = 0;
"""
        if error == 'missing':
            body += """    check(axi_r_ready && !memory_request_ready && !memory_response_valid, "Malformed line retains drain ownership");
    axi_r_bits_last = 1; axi_r_valid = 1; tick(); axi_r_valid = 0;
    check(memory_response_valid && memory_response_bits_fault && memory_response_bits_last, "Late terminal beat faults without silent owner reuse");
    memory_response_ready = 1; tick(); memory_response_ready = 0;
"""
        body += '    check(memory_request_ready, "Terminal line releases bridge");\n'
    return body + '    memory_request_bits_fetch = 0; memory_request_bits_privileged = 1;\n'


def lsu_refill_contract(parameters):
    region = next((r for r in parameters['memoryRegions'] if r.get('dataCacheable') and not r['device']), None)
    if not parameters.get('dCacheBytes') or region is None:
        return ''
    base = (int(region['base']) + 71) & ~7
    translated = parameters.get('virtualAddressBits') == 39
    line = parameters.get('dCacheRefillBytes') == 64
    body = ''
    modes = ('line', 'word', 'priority', 'partial', 'denied') if line else ('word', 'partial', 'denied')
    for mode in (modes if parameters['pmpEntries'] else ('line' if line else 'word',)):
        for size in range(4):
            if mode == 'partial' and size == 3:
                continue
            address = base + 8 - (1 << size)
            virtual = address + (0x4000 if translated else 0)
            body += f'''    reset = 1; tick(); reset = 0; tick();
    privilege = {0 if parameters.get('enableUserMode') else 3};
    input_bits_instruction_fault = 0; input_bits_instruction_tag = 37;
    input_bits_memorySize = {size}; input_bits_unsignedLoad = 1;
    input_bits_load = 1; input_bits_store = 0; input_bits_atomic = 0;
    input_bits_address = 64'h{virtual:x}; input_valid = 1;
'''
            if parameters['pmpEntries']:
                config, point = ((0x99, ((base & ~63) >> 2) | 7) if mode == 'line' else
                                 (0x99, base >> 2) if mode == 'word' else
                                 (0x91 if mode == 'partial' else 0x90, (base + 4) >> 2))
                if mode == 'priority':
                    config, point = 0x9990, ((base + 16) >> 2) | ((((base & ~63) >> 2) | 7) << (parameters['physicalAddressBits'] - 2))
                body += f"    pmp_config = 'h{config:x}; pmp_address = 'h{point:x};\n"
            body += '    tick(); input_valid = 0; privilege = 3; input_bits_address = 0;\n'
            if translated:
                body += f'''    check(translation_request_valid && translation_request_bits_address == 64'h{virtual:x}, "Refill original virtual address");
    translation_request_ready = 1; tick(); translation_request_ready = 0;
    translation_response_bits_address = 64'h{address:x}; translation_response_bits_fault = 0;
    translation_response_bits_cause = 0; translation_response_valid = 1;
    check(translation_response_ready, "Refill translation ownership"); tick(); translation_response_valid = 0;
'''
            if mode == 'line':
                body += '    check(memory_request_valid && !output_valid, "Full-range authorization adds no wait state");\n'
            body += '''    for (integer cycles = 0; !memory_request_valid && !output_valid; cycles++) begin
      check(cycles < 2, "Authorization fallback query bound"); tick();
    end
'''
            if mode == 'denied':
                body += f'''    check(output_valid && output_bits_instruction_fault && output_bits_instruction_cause == 5 &&
      output_bits_instruction_tval == 64'h{virtual:x} && !memory_request_valid, "Denied demand cannot obtain refill permission");
'''
            else:
                body += f'''    while (!memory_request_valid) begin check(!output_valid, "Refill check must preserve demand"); tick(); end
    repeat (3) begin
      check(memory_request_valid && memory_request_bits_address == 64'h{address:x} &&
        memory_request_bits_size == {size} && memory_request_bits_tag == 37 &&
        memory_request_bits_refillSize == {6 if mode == 'line' else 3 if mode in ('word', 'priority') and size < 3 else 0} &&
        memory_request_bits_privileged == {int(not parameters.get('enableUserMode'))}, "Captured demand and full-range refill authorization"); tick();
    end
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_data = 41; memory_response_bits_tag = 37;
    memory_response_bits_fault = 0; memory_response_valid = 1; tick(); memory_response_valid = 0;
    check(output_valid && !output_bits_instruction_fault && output_bits_value == 41, "Refill demand result");
'''
            body += '    output_ready = 1; tick(); output_ready = 0;\n'
    if line:
        body += f'''    reset = 1; tick(); reset = 0; tick(); privilege = 3;
    input_bits_memorySize = 1; input_bits_address = 64'h{base + 1:x};
    input_bits_instruction_fault = 0; input_valid = 1; tick(); input_valid = 0;
    check(output_valid && output_bits_instruction_fault && output_bits_instruction_cause == 4 && !memory_request_valid, "Wide permission cannot hide demand misalignment");
    output_ready = 1; tick(); output_ready = 0;
'''
    return body


def data_cache_queue_contract(parameters):
    region = next(r for r in parameters['memoryRegions'] if r.get('dataCacheable'))
    base = int(region['base']) + 0x1000
    addresses, tags = (base + 24, base + 104), (17, 34)
    seed = addresses[0] + parameters['dCacheBytes'] // 2
    seeded = parameters.get('dCacheWays', 1) == 2 and seed + 8 <= int(region['base']) + int(region['size'])
    line = parameters['dCacheRefillBytes'] == 64
    chunks = 8 if line else 1

    def request(index):
        return f'''    @(negedge clock);
    upstream_request_bits_address = 64'h{addresses[index]:x}; upstream_request_bits_tag = {tags[index]};
    upstream_request_bits_size = 3; upstream_request_bits_refillSize = {6 if line else 0}; upstream_request_valid = 1;
    #1; while (!upstream_request_ready) tick(); tick(); upstream_request_valid = 0;
'''

    def offer(index, accept=True):
        address = addresses[index] & ~63 if line else addresses[index]
        return f'''    while (!downstream_request_valid) tick();
    check(downstream_request_bits_address == 64'h{address:x} && downstream_request_bits_tag == {tags[index]} &&
          downstream_request_bits_size == {6 if line else 3} && !downstream_request_bits_write && !downstream_request_bits_cacheOperation,
          "Independent cache miss identity");
''' + ('    downstream_request_ready = 1; tick(); downstream_request_ready = 0;\n' if accept else '')

    def response(index, word):
        return f'''    @(negedge clock); downstream_response_bits_tag = {tags[index]};
    downstream_response_bits_data = {4096 + 256 * index + word}; downstream_response_bits_last = {int(word == chunks - 1)};
    downstream_response_valid = 1; #1; while (!downstream_response_ready) tick(); tick(); downstream_response_valid = 0;
'''

    body = ''
    for held in (False, True):
        body += '''    begin
    integer seen;
    bit holding;
    seen = 0; holding = 0;
    upstream_response_ready = 0; downstream_request_ready = 0;
    reset = 1; tick(); reset = 0; tick(); upstream_response_ready = 1;
'''
        if seeded:
            body += f'''    upstream_response_ready = 0;
    upstream_request_bits_address = 64'h{seed:x}; upstream_request_bits_size = 3;
    upstream_request_bits_refillSize = 0; upstream_request_bits_tag = 119;
    upstream_request_bits_write = 0; upstream_request_valid = 1;
    while (!upstream_request_ready) tick(); tick(); upstream_request_valid = 0;
    while (!downstream_request_valid) tick();
    downstream_request_ready = 1; tick(); downstream_request_ready = 0;
    downstream_response_bits_tag = 119; downstream_response_bits_data = 4660;
    downstream_response_bits_fault = 0; downstream_response_bits_last = 1; downstream_response_valid = 1;
    while (!downstream_response_ready) tick(); tick(); downstream_response_valid = 0;
    while (!upstream_response_valid) tick();
    check(upstream_response_bits_data == 4660 && !upstream_response_bits_fault, "Seed occupies the other way");
    upstream_response_ready = 1; tick(); upstream_response_ready = 0;
'''
            if parameters.get('dCacheWriteback'):
                body += f'''    upstream_request_bits_write = 1; upstream_request_bits_data = 91;
    upstream_request_bits_mask = 255; upstream_request_valid = 1;
    while (!upstream_request_ready) tick(); tick(); upstream_request_valid = 0;
    while (!downstream_request_valid) tick();
    check(downstream_request_bits_cacheOperation == 1 && downstream_request_bits_address == 64'h{seed:x}, "Seed obtains dirty ownership");
    downstream_request_ready = 1; tick(); downstream_request_ready = 0;
    downstream_response_valid = 1; while (!downstream_response_ready) tick(); tick(); downstream_response_valid = 0;
    while (!upstream_response_valid) tick();
    check(!upstream_response_bits_fault, "Seed store completes");
    upstream_response_ready = 1; tick(); upstream_response_ready = 0;
    upstream_request_bits_write = 0; upstream_request_bits_mask = 0;
'''
            body += '    upstream_response_ready = 1;\n'
        body += '''    fork
      forever begin
        @(posedge clock);
        if (upstream_response_valid && upstream_response_ready) begin
'''
        for index, tag in enumerate(tags):
            expected = 4096 + 256 * index + ((addresses[index] >> 3) & 7 if line else 0)
            body += f'''          {'if' if index == 0 else 'else if'} (upstream_response_bits_tag == {tag}) begin
            if ((seen & {1 << index}) || upstream_response_bits_data !== 64'd{expected} || upstream_response_bits_fault || !upstream_response_bits_last)
              $fatal(1, "Concurrent cache response association");
            seen = seen | {1 << index};
          end
'''
        body += '''          else $fatal(1, "Unknown cache completion tag");
        end
'''
        address = addresses[1] & ~63 if line else addresses[1]
        body += f'''        if (holding && (!downstream_request_valid || downstream_request_bits_tag != 34 ||
            downstream_request_bits_address != 64'h{address:x} || downstream_request_bits_size != {6 if line else 3}))
          $fatal(1, "Held cache offer changed while older response progressed");
      end
    join_none
'''
        body += request(0) + offer(0) + request(1) + offer(1, not held)
        if held:
            body += '    holding = 1;\n'
            body += ''.join(response(0, word) for word in range(chunks))
            body += '''    while (!(seen & 1)) tick();
    repeat (3) tick(); holding = 0;
    downstream_request_ready = 1; tick(); downstream_request_ready = 0;
'''
            body += ''.join(response(1, word) for word in range(chunks))
        else:
            body += ''.join(response(index, word) for word in range(chunks) for index in (1, 0))
        body += '''    while (seen != 3) tick();
    repeat (3) tick(); disable fork; upstream_response_ready = 0;
'''
        body += request(0).replace('upstream_request_bits_tag = 17', 'upstream_request_bits_tag = 51')
        expected = 4096 + ((addresses[0] >> 3) & 7 if line else 0)
        body += f'''    while (!upstream_response_valid) begin check(!downstream_request_valid, "Concurrent refill failed to populate cache"); tick(); end
    repeat (3) begin
      check(upstream_response_bits_data == {expected} && upstream_response_bits_tag == 51 && !upstream_response_bits_fault && !downstream_request_valid,
            "Concurrent refill hit and held completion"); tick();
    end
    upstream_response_ready = 1; tick(); upstream_response_ready = 0;
'''
        if seeded:
            body += f'''    upstream_request_bits_address = 64'h{seed:x}; upstream_request_bits_tag = 85;
    upstream_request_bits_refillSize = 0; upstream_request_valid = 1;
    while (!upstream_request_ready) tick(); tick(); upstream_request_valid = 0;
    while (!upstream_response_valid) begin check(!downstream_request_valid, "Restored read overwrote another cache way"); tick(); end
    check(!upstream_response_bits_fault && upstream_response_bits_tag == 85 &&
          upstream_response_bits_data == {91 if parameters.get('dCacheWriteback') else 4660}, "Parked read retains its selected way and peer dirty bytes");
    upstream_response_ready = 1; tick(); upstream_response_ready = 0;
'''
        body += '    end\n'
    return body


def data_cache_contract(parameters):
    region = next(r for r in parameters['memoryRegions'] if r.get('dataCacheable'))
    base, size = int(region['base']), parameters['dCacheBytes']
    fields = dict(cacheOperation=2, address=64, data=64, size=3, mask=8, tag=8, write=1, fetch=1,
                  privileged=1, atomic=1, atomicOperation=5, scEligible=1, refillSize=3)
    current = {}

    def request(address, **options):
        invalidate_accept = options.pop('invalidate_accept', False)
        current.clear()
        current.update(dict.fromkeys(fields, 0), address=address, size=3, tag=37, privileged=1)
        current.update(options)
        body = '    @(negedge clock);\n' + ''.join(
            f"    upstream_request_bits_{key} = {fields[key]}'h{value:x};\n" for key, value in current.items()) + '''    upstream_request_valid = 1;
'''
        if invalidate_accept:
            body += f"    probe_request_bits_address = 64'h{address:x}; probe_request_valid = 1;\n"
        return body + '    #1; while (!upstream_request_ready) tick(); tick(); upstream_request_valid = 0; probe_request_valid = 0;\n'

    def invalidate(address):
        return f'''    probe_request_bits_address = 64'h{address:x}; probe_request_valid = 1;
    check(probe_request_ready, "Invalidation must not wait for local or physical service");
    tick(); probe_request_valid = 0;
'''

    def bus(value, fault=0, wrong_tag=False, invalidation=None, expanded=False, fallback=False,
            operation=0, physical_address=None, before_response=''):
        body = '''    while (!downstream_request_valid) begin check(!upstream_response_valid, "Miss completed before physical service"); tick(); end
    repeat (3) begin
'''
        physical = dict(current, address=current['address'] & ~7, size=3) if expanded else dict(current)
        physical['cacheOperation'] = operation
        if operation == 2:
            physical.update(address=physical_address, size=3, data=0, mask=0, write=0, fetch=0,
                            atomic=0, atomicOperation=0, scEligible=0, refillSize=0)
        if fallback:
            physical['refillSize'] = 0
        body += '      check(' + ' && '.join(f"downstream_request_bits_{key} == {fields[key]}'h{value:x}" for key, value in physical.items())
        body += ', "Captured request payload changed"); tick();\n    end\n'
        if invalidation == 'held':
            body += invalidate(current['address'])
        body += '    downstream_request_ready = 1; tick(); downstream_request_ready = 0;\n'
        if invalidation == 'waiting':
            body += invalidate(current['address'])
        body += before_response
        body += f'''    downstream_response_bits_data = 64'h{value:x}; downstream_response_bits_tag = {current['tag'] ^ int(wrong_tag)};
    downstream_response_bits_fault = {fault}; downstream_response_bits_last = 1; downstream_response_valid = 1;
    check(downstream_response_ready, "Physical response ownership");
'''
        if invalidation == 'response':
            body += invalidate(current['address'])
        else:
            body += '    tick();\n'
        return body + '    downstream_response_valid = 0; downstream_response_bits_fault = 0;\n'

    def reply(value, fault=0, invalidate_hit=False):
        body = '''    while (!upstream_response_valid) begin check(!downstream_request_valid, "Hit generated a physical request"); tick(); end
    repeat (3) begin
'''
        data = '' if fault else f" && upstream_response_bits_data == 64'h{value:x}"
        body += f'''      check(upstream_response_valid && upstream_response_bits_tag == {current['tag']} && upstream_response_bits_fault == {fault}{data} && !downstream_request_valid, "Data completion identity, value and retention"); tick();
    end
'''
        if invalidate_hit:
            body += invalidate(current['address'])
            body += f'''    check(upstream_response_valid && upstream_response_bits_data == 64'h{value:x}, "Sampled hit did not drain after invalidation");
'''
        return body + '    upstream_response_ready = 1; tick(); upstream_response_ready = 0;\n'

    values = tuple(0xfedcba9876543210 ^ (0x0101010101010101 * word) for word in range(8))

    def line(fault=-1, wrong_tag=-1, chunks=8, invalidation=None, payload=None):
        payload = values if payload is None else payload
        physical = dict(current, address=current['address'] & ~63, size=6)
        body = '''    while (!downstream_request_valid) begin check(!upstream_response_valid, "Line miss completed before service"); tick(); end
repeat (3) begin
  check(''' + ' && '.join(f"downstream_request_bits_{key} == {fields[key]}'h{value:x}" for key, value in physical.items())
        body += ', "Line request identity and retention"); tick();\n    end\n'
        if invalidation == 'held':
            body += invalidate(current['address'])
        body += '    downstream_request_ready = 1; tick(); downstream_request_ready = 0;\n'
        if invalidation == 'waiting':
            body += invalidate(current['address'])
        for chunk in range(chunks):
            body += f'''    repeat (2) begin check(!upstream_response_valid && !downstream_request_valid && !upstream_request_ready, "Partial line cannot complete or release ownership"); tick(); end
downstream_response_bits_data = 64'h{payload[chunk % 8]:x}; downstream_response_bits_tag = {current['tag'] ^ int(chunk == wrong_tag)};
downstream_response_bits_fault = {int(chunk == fault)}; downstream_response_bits_last = {int(chunk == chunks - 1)};
downstream_response_valid = 1; check(downstream_response_ready, "Line response ownership");
'''
            body += invalidate(current['address']) if invalidation == chunk else '    tick();\n'
            body += '    downstream_response_valid = 0; downstream_response_bits_fault = 0;\n'
        return body


    geometry = ''
    limit = min(size, int(region['size']))
    for offset in (limit - 16, limit - 8):
        geometry += request(base + offset) + bus(offset ^ 0x71) + reply(offset ^ 0x71)
    for offset in (limit - 16, limit - 8):
        geometry += request(base + offset) + reply(offset ^ 0x71)

    def probe_line(address, invalidate_line, dirty=None):
        dirty = dirty or {}
        body = f'''    probe_request_bits_address = 64'h{address:x}; probe_request_bits_invalidate = {int(invalidate_line)};
probe_request_valid = 1; probe_response_ready = 0;
#1; while (!probe_request_ready) tick(); tick(); probe_request_valid = 0;
'''
        for word in range(8) if dirty else (0,):
            value, mask = dirty.get(word, (0, 0))
            data = f" && probe_response_bits_data == 64'h{value:x}" if mask else ''
            body += f'''    while (!probe_response_valid) tick();
repeat (4) begin
  check(probe_response_valid && probe_response_bits_mask == {mask} && probe_response_bits_word == {word} && probe_response_bits_last == {int(not dirty or word == 7)}{data} && !upstream_request_ready, "Probe frame data, dirty bytes and ownership retained under backpressure"); tick();
end
probe_response_ready = 1; tick(); probe_response_ready = 0;
'''
        return body + '    check(!probe_response_valid, "Probe completes once");\n'

    if parameters.get('dCacheWriteback') and int(region['size']) >= 2 * size:
        high = base + size - 8
        targets = [(high, (size - 8) ^ 0x71)]
        if parameters.get('dCacheWays', 1) == 2:
            other = high - size // 2
            geometry += request(other) + bus(0x1234) + reply(0x1234)
            targets.append((other, 0x1234))
        for address, value in targets:
            updated = (value & ((1 << 56) - 1)) | (0x5a << 56)
            geometry += request(address + 7, write=1, size=0, mask=1, data=0x5a) + bus(0, operation=1) + reply(0)
            geometry += request(address) + reply(updated)
        for address, value in targets:
            updated = (value & ((1 << 56) - 1)) | (0x5a << 56)
            geometry += probe_line(address, True, {7: (updated, 128)})

    if int(region['size']) < 2 * size:
        writeback = parameters.get('dCacheWriteback', False)
        body = '    probe_response_ready = 0;\n' if writeback else '    probe_request_bits_invalidate = 1; probe_response_ready = 1;\n'
        body += request(base) + bus(19) + reply(19)
        body += request(base, write=1, mask=255, data=23) + bus(0, operation=int(writeback)) + reply(0)
        body += request(base) + reply(23)
        body += probe_line(base, True, {0: (23, 255)}) if writeback else invalidate(base)
        body += request(base) + bus(23) + reply(23)
        if parameters.get('dCacheRefillBytes') == 64:
            body += probe_line(base, True) if writeback else invalidate(base)
            body += request(base + 8, refillSize=6) + line() + reply(values[1])
            for word in (0, 7):
                body += request(base + 8 * word) + reply(values[word])
        return geometry + body

    def associative():
        x, y, z = base, base + size // 2, base + size
        body = '    probe_response_ready = 0;\n' if parameters.get('dCacheWriteback') else '    probe_request_bits_invalidate = 1; probe_response_ready = 1;\n'
        for address, value in ((x, 11), (y, 22), (x + 8, 13), (y + 8, 23)):
            body += request(address) + bus(value) + reply(value)
        for address, value in ((x, 11), (y, 22), (x + 8, 13), (y + 8, 23)):
            body += request(address) + reply(value)
        body += request(z) + bus(33) + reply(33) + request(y) + reply(22)
        body += request(z) + reply(33) + request(x) + bus(11) + reply(11)
        body += request(z) + reply(33) + request(y) + bus(22) + reply(22)
        body += request(z) + reply(33)
        body += request(y, write=1, mask=255, data=71) + bus(0, operation=int(parameters.get('dCacheWriteback', False))) + reply(0)
        body += request(y) + reply(71) + request(z) + reply(33)
        if parameters.get('dCacheWriteback'):
            body += probe_line(y, True, {0: (71, 255)}) + request(z) + reply(33)
            body += probe_line(z, True) + probe_line(x, True)
            body += request(x) + bus(11) + reply(11) + request(y) + bus(22) + reply(22)
            for address, value in ((x, 91), (y, 92)):
                body += request(address, write=1, mask=255, data=value) + bus(0, operation=1) + reply(0)
            body += request(z)
            body += bus(0, operation=2, physical_address=x, before_response=probe_line(x, True, {0: (91, 255)}))
            body += bus(33) + reply(33) + request(y) + reply(92)
            body += request(x) + bus(91) + reply(91) + request(x) + reply(91)
            body += request(z)
            body += bus(0, operation=2, physical_address=y, before_response=probe_line(y, True, {0: (92, 255)}))
            body += bus(33) + reply(33) + request(x) + reply(91)
            body += probe_line(x, True) + probe_line(y, True) + probe_line(z, True)
        else:
            body += invalidate(y) + request(z) + bus(33) + reply(33)
            body += request(x) + bus(11) + reply(11)
            body += invalidate(x)
        body += request(x) + bus(11) + reply(11) + request(y) + bus(22) + reply(22)
        body += request(z) + bus(0, fault=1) + reply(0, fault=1)
        body += request(x) + reply(11) + request(y) + reply(22)
        body += request(y + (1 << parameters['physicalAddressBits'])) + bus(0, fault=1) + reply(0, fault=1)
        body += request(y) + reply(22)
        body += probe_line(x, True) + probe_line(y, True) if parameters.get('dCacheWriteback') else invalidate(x)
        if parameters.get('dCacheRefillBytes') == 64:
            first = values
            body += request(x, refillSize=6) + line() + reply(first[0])
            second = tuple(v ^ 0x5a5a5a5a5a5a5a5a for v in first)
            body += request(y, refillSize=6)
            body += line(payload=second) + reply(second[0])
            for word in (0, 3, 7):
                body += request(x + 8 * word) + reply(first[word])
                body += request(y + 8 * word) + reply(second[word])
            for target, retained, value in ((z, y + 56, second[7]), (x, z + 8, 89)):
                body += request(target, refillSize=6) + line(wrong_tag=3) + bus(67, fallback=True) + reply(67)
                body += request(retained) + reply(value)
                body += request(target + 8) + bus(89) + reply(89)
                body += request(target) + bus(67) + reply(67)
        return body

    if parameters.get('dCacheWays', 1) == 2:
        return geometry + associative()

    if parameters.get('dCacheWriteback'):
        initial = 0x123456789abcdef0
        value = initial
        body = request(base) + bus(value) + reply(value)
        for width in range(4):
            for offset in range(0, 8, 1 << width):
                mask = (1 << (1 << width)) - 1
                for selected in sorted({mask, mask & 0x55 or 1}):
                    byte_mask = sum(255 << (8 * byte) for byte in range(8) if selected >> byte & 1) << (8 * offset)
                    value = (value & ~byte_mask) | ((0xfedcba9876543210 << (8 * offset)) & byte_mask)
                    body += request(base + offset, size=width, mask=selected, write=1, data=0xfedcba9876543210)
                    body += bus(0, operation=1) + reply(0)
                    body += request(base) + reply(value)
                    body += probe_line(base, False, {0: (value, selected << offset)})
                    body += request(base) + reply(value)
        value = (value & ~0xff000000000000ff) | 0xa500000000000091
        body += request(base, write=1, size=0, mask=1, data=0x91) + bus(0, operation=1) + reply(0)
        body += request(base + 7, write=1, size=0, mask=1, data=0xa5) + bus(0, operation=1) + reply(0)
        body += request(base) + reply(value) + probe_line(base, False, {0: (value, 0x81)})
        body += request(base, write=1, mask=255, data=initial) + bus(0, operation=1) + reply(0)
        for options in ({'fault': 1}, {'wrong_tag': True}):
            body += request(base, write=1, mask=255, data=29) + bus(0, operation=1, **options) + reply(0, fault=1)
            body += request(base) + reply(initial)
        body += probe_line(base + size, True)
        body += probe_line(base + (1 << parameters['physicalAddressBits']), True)
        body += request(base) + reply(initial)
        body += request(base + 8) + bus(17) + reply(17)
        body += request(base + 9, write=1, size=0, mask=1, data=0x88) + bus(0, operation=1) + reply(0)
        body += probe_line(base, False, {0: (initial, 255), 1: (0x8811, 2)})
        body += request(base) + reply(initial)
        body += request(base + 8) + reply(0x8811)
        body += probe_line(base, False)
        body += request(base, write=1, mask=255, data=31) + bus(0, operation=1) + reply(0)
        body += request(base + size)
        body += bus(0, operation=2, physical_address=base, before_response=probe_line(base, True, {0: (31, 255)}))
        body += bus(23) + reply(23)
        body += request(base) + bus(31) + reply(31)
        body += probe_line(base, True)
        body += request(base, write=1, mask=255, data=41) + bus(0) + reply(0)
        body += request(base) + bus(41) + reply(41)
        if parameters.get('dCacheRefillBytes') == 64:
            body += probe_line(base, True) + request(base + 56, refillSize=6) + line() + reply(values[7])
            for word in range(8):
                body += request(base + 8 * word) + reply(values[word])
            low, high = (values[0] & ~255) | 0x91, (values[7] & ((1 << 56) - 1)) | (0xa5 << 56)
            body += request(base, write=1, size=0, mask=1, data=0x91) + bus(0, operation=1) + reply(0)
            body += request(base + 63, write=1, size=0, mask=1, data=0xa5) + bus(0, operation=1) + reply(0)
            body += request(base + size + 8, refillSize=6)
            body += bus(0, operation=2, physical_address=base, before_response=probe_line(base, True, {0: (low, 1), 7: (high, 128)}))
            body += line() + reply(values[1])
            body += request(base + size) + reply(values[0])
            body += request(base + size + 56) + reply(values[7])
            body += probe_line(base + size, True) + request(base + size) + bus(values[0]) + reply(values[0])
            low = (values[0] & ~0xff00) | 0xab00
            body += request(base + size + 1, write=1, size=0, mask=1, data=0xab) + bus(0, operation=1) + reply(0)
            body += request(base + size + 8, refillSize=6)
            body += bus(0, operation=2, physical_address=base + size, before_response=probe_line(base + size, True, {0: (low, 2)}))
            values = (low, *values[1:])
            body += line() + reply(values[1]) + request(base + size) + reply(low)
            body += probe_line(base + size, True) + request(base + size, refillSize=6) + line(wrong_tag=3)
            body += bus(low, fallback=True) + reply(low)
            body += request(base + size + 8) + bus(values[1]) + reply(values[1])
        return geometry + body

    body = '    probe_request_bits_invalidate = 1; probe_response_ready = 1;\n'
    body += request(base) + bus(0x123456789abcdef0) + reply(0x123456789abcdef0)
    body += request(base, tag=38, privileged=0) + reply(0x123456789abcdef0)
    body += request(base + 8) + bus(0x9988776655443322) + reply(0x9988776655443322)
    body += request(base) + reply(0x123456789abcdef0, invalidate_hit=True)
    body += request(base) + bus(3) + reply(3)
    body += request(base + 8) + bus(4) + reply(4)
    body += request(base + size) + bus(5) + reply(5)
    body += request(base) + bus(6) + reply(6)
    for phase in ('held', 'waiting', 'response'):
        body += invalidate(base) + request(base) + bus(7, invalidation=phase) + reply(7)
        body += request(base) + bus(8) + reply(8)
        body += request(base) + reply(8)
    body += request(base, invalidate_accept=True) + bus(10) + reply(10)
    body += request(base) + bus(11) + reply(11)
    for options in ({'fault': 1}, {'wrong_tag': True}):
        body += invalidate(base) + request(base) + bus(0, **options) + reply(0, fault=1)
        body += request(base) + bus(9) + reply(9)
    for options in ({'size': 2}, {'write': 1, 'data': 11, 'mask': 1, 'size': 0},
                    {'atomic': 1, 'atomicOperation': 2},
                    {'atomic': 1, 'atomicOperation': 3, 'write': 1, 'mask': 255, 'data': 12, 'scEligible': 1}):
        for _ in range(2):
            body += invalidate(base) + request(base, **options) + bus(13, invalidation='waiting') + reply(13)
    value = 0xfedcba9876543210
    for width in range(3):
        offset = 8 - (1 << width)
        expected = (value >> (offset * 8)) & ((1 << (8 << width)) - 1)
        body += invalidate(base) + request(base + offset, size=width, refillSize=3)
        body += bus(value, expanded=True) + reply(expected)
        for offset in range(0, 8, 1 << width):
            expected = (value >> (offset * 8)) & ((1 << (8 << width)) - 1)
            body += request(base + offset, size=width) + reply(expected)
    for failure in ({'fault': 1}, {'wrong_tag': True}):
        body += invalidate(base) + request(base + 3, size=0, refillSize=3)
        body += bus(0, expanded=True, **failure) + bus(0x76, fallback=True) + reply(0x76)
        body += request(base + 3, size=0, refillSize=3) + bus(value, expanded=True) + reply(0x76)
        body += request(base + 3, size=0) + reply(0x76)
    for phase in ('held', 'waiting', 'response'):
        body += invalidate(base) + request(base + 4, size=2, refillSize=3)
        body += bus(value, expanded=True, invalidation=phase) + reply(value >> 32)
        body += request(base + 4, size=2, refillSize=3) + bus(value, expanded=True) + reply(value >> 32)
    body += request(base, size=0) + reply(0x10)
    body += f'''    @(negedge clock);
    upstream_request_bits_address = 64'h{base:x}; upstream_request_bits_size = 0;
    upstream_request_bits_tag = 64; upstream_request_valid = 1; upstream_response_ready = 1;
    tick();
'''
    for offset in range(8):
        body += f'''    check(upstream_response_valid && upstream_request_ready && !downstream_request_valid &&
      upstream_response_bits_data == {((value >> (offset * 8)) & 255)} &&
      upstream_response_bits_tag == {64 + offset}, "Consecutive cache hit service");
    upstream_request_bits_address = 64'h{base + offset + 1:x};
    upstream_request_bits_tag = {65 + offset}; upstream_request_valid = {int(offset < 7)}; tick();
'''
    body += '    upstream_response_ready = 0;\n'
    for address in (base + 1, 1 << parameters['physicalAddressBits']):
        body += request(address) + bus(0, fault=1) + reply(0, fault=1)
    for grant in (1, 2, 4, 5, 7):
        body += invalidate(base) + request(base + 1, size=0, refillSize=grant) + bus(29) + reply(29)
    if parameters.get('dCacheRefillBytes') == 64:
        for word in range(8):
            for width in range(4):
                offset = 8 * word + 8 - (1 << width)
                expected = (values[word] >> (8 * (offset % 8))) & ((1 << (8 << width)) - 1)
                body += invalidate(base) + request(base + offset, size=width, refillSize=6)
                body += line() + reply(expected)
                for hit in (0, 7, word):
                    body += request(base + 8 * hit) + reply(values[hit])
        body += invalidate(base) + request(base, refillSize=6) + line()
        body += f'''    while (!upstream_response_valid) tick();
    check(upstream_response_bits_data == 64'h{values[0]:x}, "Line demand before immediate next read");
    upstream_response_ready = 1; upstream_request_valid = 1;
    upstream_request_bits_address = 64'h{base + 56:x}; upstream_request_bits_tag = 38;
    check(upstream_request_ready, "Next request accepts with line completion"); tick();
    upstream_response_ready = 0; upstream_request_valid = 0;
    check(upstream_response_valid && upstream_response_bits_data == 64'h{values[7]:x} && upstream_response_bits_tag == 38 && !downstream_request_valid, "Final array write precedes earliest next hit");
    upstream_response_ready = 1; tick(); upstream_response_ready = 0;
'''
        failures = [dict(fault=i) for i in (0, 3, 7)] + [dict(wrong_tag=i) for i in (0, 7)]
        failures += [dict(chunks=n) for n in (1, 3, 7, 10)]
        failures += [dict(invalidation=p) for p in ('held', 'waiting', 0, 3, 7)]
        for index, failure in enumerate(failures):
            address = base + (size if index % 2 else 0)
            body += invalidate(base) + request(base) + bus(17) + reply(17)
            body += request(address + 12, size=2, refillSize=6) + line(**failure)
            body += bus(29, fallback=True) + reply(29)
            for word in (0, 1, 7):
                body += request(address + 8 * word) + bus(41 + word) + reply(41 + word)
        body += invalidate(base) + request(base + 7, size=0, refillSize=6)
        body += line(fault=0) + bus(0, fault=1, fallback=True) + reply(0, fault=1)
        body += request(base, refillSize=6) + line() + reply(values[0])
        for options in (dict(fetch=1), dict(write=1, mask=255, data=17), dict(atomic=1, atomicOperation=2)):
            body += request(base, refillSize=6, **options) + bus(17) + reply(17)
    value = 0x123456789abcdef0
    for width in range(4):
        for offset in range(0, 8, 1 << width):
            mask = (1 << (1 << width)) - 1
            for selected in sorted({mask, mask & 0x55 or 1}):
                byte_mask = sum(255 << (8 * byte) for byte in range(8) if selected >> byte & 1) << (8 * offset)
                expected = (value & ~byte_mask) | ((0xfedcba9876543210 << (8 * offset)) & byte_mask)
                body += invalidate(base) + request(base) + bus(value) + reply(value)
                body += request(base + 8) + bus(19) + reply(19)
                body += request(base + offset, size=width, mask=selected, write=1, data=0xfedcba9876543210)
                body += bus(0) + reply(0)
                body += request(base) + reply(expected)
                body += request(base + 8) + reply(19)
    body += invalidate(base) + request(base, write=1, mask=255, data=23) + bus(0) + reply(0)
    body += request(base) + bus(23) + reply(23)
    for options in ({'fault': 1}, {'wrong_tag': True}):
        body += request(base, write=1, mask=255, data=29) + bus(0, **options) + reply(0, fault=1)
        body += request(base) + bus(23) + reply(23)
    for phase in ('held', 'waiting', 'response'):
        body += request(base, write=1, mask=255, data=29) + bus(0, invalidation=phase) + reply(0)
        body += request(base) + bus(29) + reply(29)
    body += request(base, write=1, mask=255, data=31, invalidate_accept=True) + bus(0) + reply(0)
    body += request(base) + bus(31) + reply(31)
    for region in parameters['memoryRegions']:
        if region['device']:
            options = {} if region['readable'] else dict(write=1, mask=255, data=14)
            for _ in range(2):
                body += request(int(region['base']), refillSize=6, **options) + bus(14) + reply(14)
            break
    return geometry + body


def coherence_contract(parameters):
    count = parameters['hartCount']
    base = int(next(r for r in parameters['memoryRegions'] if r.get('dataCacheable'))['base'])
    writeback = parameters.get('dCacheWriteback', False)
    body = ''
    cases = ((0, 0, 0, 1), (0, 1, 0, 1), (0, 1, 1, 1)) + (((1, 1, 0, 1), (2, 0, 0, 1), (0, 0, 0, 0)) if writeback else ())
    for operation, write, atomic, privileged in cases:
        writer = count - 1
        targets = ([writer] if operation == 2 else [h for h in range(count) if operation != 1 or h != writer]) if writeback else (
            [h for h in range(count) if atomic or h != writer] if write else [])
        for dirty in (False, True) if targets and writeback else (False,):
            body += f'''    @(negedge clock);
    hartId = {writer}; upstream_request_bits_address = 64'h{base & ~63 if operation == 2 else base:x}; upstream_request_bits_tag = 37;
    upstream_request_bits_size = 3; upstream_request_bits_mask = {255 if write else 0};
    upstream_request_bits_cacheOperation = {operation}; upstream_request_bits_write = {write};
    upstream_request_bits_atomic = {atomic}; upstream_request_bits_atomicOperation = 0;
    upstream_request_bits_data = 19; upstream_request_bits_privileged = {privileged};
    upstream_request_valid = 1; downstream_request_ready = 0; tick();
'''
            for hart in targets:
                for peer in range(count):
                    body += f'''    check(probe_{peer}_request_valid == {int(peer in targets and peer >= hart)}, "Exactly the required probes remain offered");
'''
                body += f'''    check(probe_{hart}_request_bits_address == 64'h{base & ~63:x} && probe_{hart}_request_bits_invalidate == {int(bool(write or operation == 2 or atomic))}, "Probe address and operation");
    probe_{hart}_request_ready = 1; tick(); probe_{hart}_request_ready = 0;
'''
            if targets:
                body += '''    repeat (3) begin
      check(!upstream_request_ready && !upstream_response_valid && !downstream_request_valid, "Probe acceptance is not completion"); tick();
    end
'''
            for hart in targets:
                if dirty and hart == targets[0]:
                    value, mask, word = 0x1122334455667788, 0x55, 3
                    body += f'''    probe_{hart}_response_valid = 1; probe_{hart}_response_bits_mask = {mask};
    probe_{hart}_response_bits_word = {word}; probe_{hart}_response_bits_last = 0;
    probe_{hart}_response_bits_data = 64'h{value:x};
'''
                    for failure in ('fault', 'tag', 'terminal', None):
                        body += f'''    while (!downstream_request_valid) begin
      check(!upstream_request_ready && !upstream_response_valid && !probe_{hart}_response_ready, "Dirty ownership retained before writeback"); tick();
    end
    repeat (3) begin
      check(downstream_request_valid && downstream_request_bits_address == 64'h{(base & ~63) + 8 * word:x} && downstream_request_bits_data == 64'h{value:x} && downstream_request_bits_mask == {mask} && downstream_request_bits_tag == 37 && downstream_request_bits_size == 3 && downstream_request_bits_write && downstream_request_bits_privileged && !downstream_request_bits_atomic && !downstream_request_bits_fetch && downstream_request_bits_cacheOperation == 0 && !probe_{hart}_response_ready, "Held masked writeback payload and trusted maintenance context"); tick();
    end
    downstream_request_ready = 1; tick(); downstream_request_ready = 0;
    repeat (3) begin check(!probe_{hart}_response_ready && !upstream_request_ready && !upstream_response_valid, "Writeback request acceptance is not completion"); tick(); end
'''
                        if failure == 'terminal':
                            body += f'''    downstream_response_bits_fault = 0; downstream_response_bits_tag = 37;
    downstream_response_bits_last = 0; downstream_response_valid = 1;
    check(downstream_response_ready && !probe_{hart}_response_ready, "Malformed writeback cannot release dirty data");
    tick(); downstream_response_valid = 0;
    repeat (3) begin check(!downstream_request_valid && downstream_response_ready && !probe_{hart}_response_ready, "Malformed stream retains physical ownership until last"); tick(); end
'''
                        body += f'''
    downstream_response_bits_data = 0; downstream_response_bits_tag = {36 if failure == 'tag' else 37};
    downstream_response_bits_fault = {int(failure == 'fault')}; downstream_response_bits_last = 1;
    downstream_response_valid = 1;
    check(downstream_response_ready && probe_{hart}_response_ready == {int(failure is None)} && !upstream_request_ready && !upstream_response_valid, "Only successful writeback releases dirty data");
    tick(); downstream_response_valid = 0; downstream_response_bits_fault = 0;
'''
                    body += f'    probe_{hart}_response_valid = 0; tick();\n'
                body += f'''    probe_{hart}_response_bits_mask = 0; probe_{hart}_response_bits_word = 7;
    probe_{hart}_response_bits_last = 1; probe_{hart}_response_valid = 1;
    #1; while (!probe_{hart}_response_ready) tick(); tick(); probe_{hart}_response_valid = 0;
'''
            body += '''    while (!upstream_request_ready && !downstream_request_valid) tick();
'''
            if operation:
                body += '''    check(upstream_request_ready && !downstream_request_valid && !upstream_response_valid, "Ownership grant needs request acceptance");
    tick(); upstream_request_valid = 0; upstream_request_bits_tag = 99;
    repeat (3) begin
      check(upstream_response_valid && upstream_response_bits_tag == 37 && !upstream_response_bits_fault && upstream_response_bits_data == 0 && upstream_response_bits_last && !downstream_request_valid, "Retained ownership grant"); tick();
    end
'''
            else:
                body += f'''    repeat (3) begin
      check(downstream_request_valid && downstream_request_bits_address == 64'h{base:x} && downstream_request_bits_tag == 37 && downstream_request_bits_write == {write} && downstream_request_bits_atomic == {atomic} && downstream_request_bits_privileged == {privileged} && !upstream_request_ready, "Original request follows probe completion"); tick();
    end
    downstream_request_ready = 1; tick(); downstream_request_ready = 0; upstream_request_valid = 0;
    downstream_response_bits_tag = 37; downstream_response_bits_data = 23; downstream_response_bits_fault = 0;
    downstream_response_bits_last = 1; downstream_response_valid = 1;
    repeat (3) begin
      check(upstream_response_valid && upstream_response_bits_tag == 37 && upstream_response_bits_data == 23 && !downstream_response_ready, "Shared response retention"); tick();
    end
'''
            body += '    upstream_response_ready = 1; tick(); upstream_response_ready = 0; downstream_response_valid = 0;\n'
    address = int(next(r['base'] for r in parameters['memoryRegions'] if r['readable'] and not r.get('dataCacheable')))
    for operation in (1, 2, 3):
        body += f'''    upstream_request_bits_address = 64'h{address:x}; upstream_request_bits_size = 3;
    upstream_request_bits_cacheOperation = {operation}; upstream_request_bits_write = {int(operation == 1)};
    upstream_request_bits_mask = 255; upstream_request_bits_atomic = 0; upstream_request_bits_fetch = 0;
    upstream_request_bits_tag = 37; upstream_request_valid = 1;
    check(upstream_request_ready && !downstream_request_valid, "Invalid ownership request rejected before physical effects");
    tick(); upstream_request_valid = 0;
    check(upstream_response_valid && upstream_response_bits_fault && upstream_response_bits_tag == 37 && upstream_response_bits_last, "Invalid ownership request attribution");
    upstream_response_ready = 1; tick(); upstream_response_ready = 0;
'''
    return body


def line_read_window(parameters, expected_peak=None, fault_beat=-1, terminal='normal', stalls=False):
    data = parameters.get('dCacheRefillBytes') == 64
    if not data and not parameters.get('enableBurstRefill'):
        return ''
    width, harts = parameters['axiDataBits'], parameters['hartCount']
    base = int(next(r['base'] for r in parameters['memoryRegions'] if not r['device'] and
                   (r['readable'] and r.get('dataCacheable') if data else r['executable'])))
    count = min(harts * (2 if data and parameters.get('enableBurstRefill') else 1), 4)
    ports = (*range(count - 1), 2 * harts - 1) if data and parameters.get('enableBurstRefill') else tuple(
        2 * hart + int(data) for hart in (*range(count - 1), harts - 1))
    if expected_peak is None:
        expected_peak = min(count, parameters.get('fabricReadSlots') or 2)
    target, beats, slices = expected_peak - 1, 512 // width, width // 64
    lengths = [slices if n == target and terminal == 'early' else 9 if n == target and terminal == 'late' else 8 for n in range(count)]
    body = f'''    reset = 1; tick(); reset = 0; tick();
    begin
      integer cycles, peak, selected, id, expected, bus_id[{count}], delay[{count}], sent[{count}], received[{count}];
      bit [{count-1}:0] accepted, issued, live, done;
      bit holding;
      cycles = 0; peak = 0; selected = 0; accepted = 0; issued = 0; live = 0; done = 0; holding = 0;
      if (!$value$plusargs("EXPECTED_PEAK=%d", expected)) expected = {expected_peak};
      for (integer n = 0; n < {count}; n++) begin delay[n] = 0; sent[n] = 0; received[n] = 0; end
      while (done != {count}'d{(1 << count) - 1} && cycles < 500) begin
        @(negedge clock);
        ar_ready = {'cycles % 3 != 0' if stalls else '1'};
'''
    for n, port in enumerate(ports):
        body += f'''        ports_{port}_request_valid = !accepted[{n}];
        ports_{port}_request_bits_address = 64'h{base + 0x100 + 64 * n:x};
        ports_{port}_request_bits_size = 6; ports_{port}_request_bits_fetch = {int(port % 2 == 0)};
        ports_{port}_request_bits_write = 0; ports_{port}_request_bits_atomic = 0;
        ports_{port}_request_bits_tag = {71 + n}; ports_{port}_response_ready = {'cycles % 5 != 0' if stalls else '1'};
'''
    body += f'''        if (!holding) begin
          r_valid = 0;
          for (integer n = {count-1}; n >= 0; n--) if (live[n] && delay[n] == 0) begin
            selected = n; r_valid = 1;
          end
          if (r_valid) begin
            r_bits_id = bus_id[selected]; r_bits_resp = selected == {target} && sent[selected] == {fault_beat} ? 2 : 0;
            r_bits_last = sent[selected] == (selected == {target} ? {0 if terminal == 'early' else beats if terminal == 'late' else beats - 1} : {beats - 1});
            for (integer chunk = 0; chunk < {width // 64}; chunk++)
              r_bits_data[64 * chunk +: 64] = 64'h1000000000000000 + 256 * selected + sent[selected] * {width // 64} + chunk;
          end
        end
        #1;
'''
    for n, port in enumerate(ports):
        fault_from = fault_beat * slices if fault_beat >= 0 else 9
        if terminal == 'early' and beats > 1: fault_from = 0
        if terminal == 'late': fault_from = min(fault_from, 8 - slices)
        value = f"64'h1000000000000000 + 256 * {n} + received[{n}]"
        if n == target and terminal == 'late': value = f"(received[{n}] == 8 ? 64'b0 : {value})"
        body += f'''        if (ports_{port}_request_valid && ports_{port}_request_ready) accepted[{n}] = 1;
        if (ports_{port}_response_valid && ports_{port}_response_ready) begin
          if (done[{n}] || ports_{port}_response_bits_fault != ({int(n == target)} && received[{n}] >= {fault_from}) || ports_{port}_response_bits_tag != {71 + n} ||
              ports_{port}_response_bits_data != {value} ||
              ports_{port}_response_bits_last != (received[{n}] == {lengths[n]-1})) $fatal(1, "Line window payload or completion");
          received[{n}]++;
          if (received[{n}] == {lengths[n]}) done[{n}] = 1;
        end
'''
    body += f'''        if (ar_valid && ar_ready) begin
          id = integer'((ar_bits_addr - 64'h{base + 0x100:x}) / 64);
          if (id < 0 || id >= {count} || !accepted[id] || issued[id] ||
              ar_bits_addr != 64'h{base + 0x100:x} + 64 * id || ar_bits_len != {512 // width - 1} ||
              ar_bits_size != {int(width // 8).bit_length() - 1}) $fatal(1, "Line window address identity");
          for (integer n = 0; n < {count}; n++) if (live[n] && bus_id[n] == ar_bits_id) $fatal(1, "Live read ID reused");
          bus_id[id] = ar_bits_id;
          issued[id] = 1; live[id] = 1; delay[id] = 24;
          if ($countones(live) > peak) peak = $countones(live);
        end
        holding = r_valid && !r_ready;
        if (r_valid && r_ready) begin sent[selected]++; if (r_bits_last) live[selected] = 0; end
        for (integer n = 0; n < {count}; n++) if (delay[n] > 0) delay[n]--;
        tick(); cycles++;
      end
      check(done == {count}'d{(1 << count) - 1} && peak == expected, "Line window completion and physical overlap");
      $display("LINE_READ_WINDOW cycles=%0d peak=%0d fault={fault_beat} terminal={terminal}", cycles, peak);
      ar_ready = 0; r_valid = 0;
'''
    for port in ports:
        body += f'      ports_{port}_request_valid = 0; ports_{port}_response_ready = 0;\n'
    return body + '    end\n'


def line_read_contract(parameters):
    width, harts = parameters['axiDataBits'], parameters['hartCount']
    beats, slices = 512 // width, width // 64
    kinds = ([True] if parameters.get('enableBurstRefill') else []) + ([False] if parameters.get('dCacheRefillBytes') == 64 else [])
    if not kinds:
        return ''
    base = int(next(r['base'] for r in parameters['memoryRegions'] if not r['device'] and r['executable'] and r['readable'] and
                   (r.get('dataCacheable') or kinds == [True])))
    body = ''
    scenarios = [(a, b, 6, -1, 'normal') for a in kinds for b in kinds]
    scenarios += [(a, False, 2, -1, 'normal') for a in kinds]
    scenarios += [(kinds[0], kinds[0], 6, error, 'normal') for error in sorted({0, beats // 2, beats - 1})]
    scenarios += [(kinds[0], kinds[0], 6, -1, mode) for mode in ('early', 'late') if mode != 'early' or beats > 1]
    for first, second, second_size, error, mode in scenarios:
        ports = (int(not first), 2 * (harts - 1) + int(not second))
        if ports[0] == ports[1]:
            continue
        body += '    begin\n      integer bus_id[2];\n'
        for n, port in enumerate(ports):
            size, fetch = (6, first) if n == 0 else (second_size, second)
            body += f'''    ports_{port}_request_bits_address = 64'h{base + 0x100 + 64 * n:x};
    ports_{port}_request_bits_size = {size}; ports_{port}_request_bits_fetch = {int(fetch)};
    ports_{port}_request_bits_write = 0; ports_{port}_request_bits_atomic = 0;
    ports_{port}_request_bits_tag = {91 + n}; ports_{port}_request_valid = 1; #1;
    while (!ports_{port}_request_ready) tick(); tick(); ports_{port}_request_valid = 0;
'''
        for n in range(2):
            size = 6 if n == 0 else second_size
            body += f'''    while (!ar_valid) tick();
    repeat (3) begin
      check(ar_bits_addr == 64'h{base + 0x100 + 64 * n:x} && ar_bits_len == {beats - 1 if size == 6 else 0} && ar_bits_size == {int(width // 8).bit_length() - 1 if size == 6 else size}, "Concurrent line AR stable before any R"); tick();
    end
    bus_id[{n}] = ar_bits_id;
    {'check(bus_id[0] != bus_id[1], "Concurrent lines have distinct IDs");' if n == 1 else ''}
    ar_ready = 1; tick(); ar_ready = 0;
'''
        for beat in range(beats):
            for n in (1, 0):
                size = 6 if n == 0 else second_size
                if size != 6 and beat != 0 or n == 0 and mode == 'early' and beat > 0:
                    continue
                port = ports[n]
                last = size != 6 or (beat == 0 if n == 0 and mode == 'early' else beat == beats - 1 and not (n == 0 and mode == 'late'))
                bad = n == 0 and (0 <= error <= beat or mode == 'early' or mode == 'late' and beat == beats - 1)
                parts = slices if size == 6 else 1
                words = [(0x2000000000000000 + 256 * n + beat * slices + part) if size == 6 else 0x76543210 for part in range(parts)]
                value = sum(word << (64 * part) for part, word in enumerate(words))
                body += f'''    r_bits_id = bus_id[{n}]; r_bits_data = {width}'h{value:x};
    r_bits_resp = {2 if n == 0 and error == beat else 0}; r_bits_last = {int(last)}; r_valid = 1; #1;
    while (!r_ready) tick(); tick(); r_valid = 0;
'''
                for part, word in enumerate(words):
                    body += f'''    while (!ports_{port}_response_valid) tick();
    repeat (2) begin
      check(ports_{port}_response_bits_data == 64'h{word:x} && ports_{port}_response_bits_tag == {91 + n} && ports_{port}_response_bits_fault == {int(bad)} && ports_{port}_response_bits_last == {int(last and part == parts - 1)} && !empty, "Interleaved line chunk retains data, fault and owner"); tick();
    end
    ports_{port}_response_ready = 1; tick(); ports_{port}_response_ready = 0;
'''
        if mode == 'late':
            port = ports[0]
            body += f'''    r_bits_id = bus_id[0]; r_bits_resp = 0; r_bits_last = 0; r_valid = 1; #1;
    while (!r_ready) tick(); tick(); r_valid = 0;
    check(!ports_{port}_response_valid && !empty, "Overlong line drains without extra chunks");
    r_bits_last = 1; r_valid = 1; tick(); r_valid = 0;
    while (!ports_{port}_response_valid) tick();
    check(ports_{port}_response_bits_fault && ports_{port}_response_bits_last && ports_{port}_response_bits_tag == 91, "Overlong line terminates with owned error");
    ports_{port}_response_ready = 1; tick(); ports_{port}_response_ready = 0;
'''
        body += '    check(empty, "Both interleaved transactions consumed");\n    end\n'
    if beats > 1:
        port = int(not kinds[0])
        body += f'''    ports_{port}_request_bits_address = 64'h{base + 0x100:x};
    ports_{port}_request_bits_size = 6; ports_{port}_request_bits_fetch = {int(kinds[0])};
    ports_{port}_request_valid = 1; #1;
    while (!ports_{port}_request_ready) tick(); tick(); ports_{port}_request_valid = 0;
    while (!ar_valid) tick(); ar_ready = 1; tick(); ar_ready = 0;
    r_bits_id = 0; r_bits_resp = 0; r_bits_last = 0; r_bits_data = 0; r_valid = 1;
    while (!r_ready) tick(); tick(); r_valid = 0;
'''
        for beat in range(1, beats):
            body += f'''    r_bits_data = {beat}; r_bits_last = {int(beat == beats - 1)}; r_valid = 1;
    repeat (3) begin
      check(!r_ready && ports_{port}_response_valid && !ports_{port}_response_bits_fault, "Known RID waits for prior fragments without poisoning"); tick();
    end
    ports_{port}_response_ready = 1; repeat ({slices}) tick(); ports_{port}_response_ready = 0;
    while (!r_ready) tick(); tick(); r_valid = 0;
'''
        body += f'''    ports_{port}_response_ready = 1;
    repeat ({slices}) begin check(ports_{port}_response_valid && !ports_{port}_response_bits_fault, "Backpressured line completes"); tick(); end
    ports_{port}_response_ready = 0; check(empty, "Backpressured line releases owner");
'''
    return body + line_read_window(parameters)


def read_queue_serial_contract(parameters):
    base = int(next(r['base'] for r in parameters['memoryRegions'] if r['readable'] and not r['device']))
    body = ''
    for hart in (0, parameters['hartCount'] - 1):
        port = 2 * hart + 1
        for mode in ('short', 'late', 'denied', 'write', 'atomic', 'size', 'unknown'):
            denied = mode in ('denied', 'write', 'atomic', 'size')
            address = 1 << parameters['physicalAddressBits'] if mode == 'denied' else base + 0x100
            body += f'''    reset = 1; tick(); reset = 0; tick();
    r_bits_resp = 0; r_bits_last = 1; r_valid = 0; ar_ready = 0;
    ports_{port}_request_bits_address = 64'h{address:x}; ports_{port}_request_bits_size = {4 if mode == 'size' else 3};
    ports_{port}_request_bits_write = {int(mode == 'write')}; ports_{port}_request_bits_atomic = {int(mode == 'atomic')};
    ports_{port}_request_bits_tag = 59; ports_{port}_request_valid = 1; #1;
    while (!ports_{port}_request_ready) tick(); tick(); ports_{port}_request_valid = 0;
'''
            if denied:
                body += f'''    while (!ports_{port}_response_valid) begin check(!ar_valid, "Rejected read cannot issue AR"); tick(); end
'''
            else:
                body += f'''    while (!ar_valid) tick();
    repeat (3) begin check(ar_bits_id == 0 && ar_bits_addr == 64'h{address:x} && ar_bits_len == 0 && !ports_{port}_request_ready, "Serial AR stability and client exclusion"); tick(); end
    ar_ready = 1; tick(); ar_ready = 0;
'''
                if mode == 'unknown':
                    body += f'''    r_bits_id = 1; r_valid = 1; tick(); r_valid = 0;
    check(!ports_{port}_response_valid && !empty, "Unknown RID cannot complete a real owner");
'''
                body += f'''    r_bits_id = 0; r_bits_data = 64'h123456789abcdef0; r_valid = 1;
'''
                if mode == 'late':
                    body += f'''    r_bits_last = 0; tick(); r_valid = 0;
    check(!ports_{port}_response_valid, "Unterminated short read retains ownership");
    r_bits_last = 1; r_valid = 1;
'''
                body += '    tick(); r_valid = 0;\n'
            body += f'''    repeat (3) begin
      check(ports_{port}_response_valid && ports_{port}_response_bits_tag == 59 && ports_{port}_response_bits_last &&
        ports_{port}_response_bits_fault == {int(mode != 'short')} && !ports_{port}_request_ready &&
        (ports_{port}_response_bits_fault || ports_{port}_response_bits_data == 64'h123456789abcdef0), "Serial completion identity, data and retention"); tick();
    end
    ports_{port}_response_ready = 1; tick(); ports_{port}_response_ready = 0;
    check(empty == {int(mode != 'unknown')}, "Serial release or sticky protocol containment");
    ports_{port}_request_bits_write = 0; ports_{port}_request_bits_atomic = 0;
'''
    return body + '    reset = 1; tick(); reset = 0; tick();\n'


def read_queue_data_contract(parameters):
    if parameters.get('loadQueueEntries', 1) != 2 or (parameters.get('fabricReadSlots') or 2) < 2:
        return ''
    width = parameters['axiDataBits']
    base = int(parameters['memoryRegions'][0]['base'])
    body = '''    begin
    integer ids[2];
    reset = 1; tick(); reset = 0; tick(); ports_1_response_ready = 0;
'''
    for index, address in enumerate((base + 0x100, base + 0x140)):
        body += f'''    ports_1_request_bits_address = 'h{address:x}; ports_1_request_bits_size = 3; ports_1_request_bits_fetch = 0;
    ports_1_request_bits_tag = {17 + 17 * index}; ports_1_request_valid = 1;
    #1; while (!ports_1_request_ready) tick(); tick(); ports_1_request_valid = 0;
    while (!ar_valid) tick(); ids[{index}] = ar_bits_id;
    check(ar_bits_addr == 'h{address:x} && ar_bits_len == 0, "Two same-client AXI addresses before either reply");
    ar_ready = 1; tick(); ar_ready = 0;
'''
    body += '''    check(ids[0] != ids[1], "Same-client reads require distinct live IDs");
    ports_1_request_bits_tag = 51; ports_1_request_valid = 1;
    repeat (3) begin check(!ports_1_request_ready && !empty, "Data client capacity is two"); tick(); end
    ports_1_request_valid = 0;
'''
    for index in (1, 0):
        body += f'''    r_bits_id = ids[{index}]; r_bits_data = {width}'d{11 + 11 * index}; r_bits_last = 1; r_bits_resp = 0; r_valid = 1;
    #1; while (!r_ready) tick(); tick(); r_valid = 0;
    repeat (3) begin
      check(ports_1_response_valid && ports_1_response_bits_tag == 34 && ports_1_response_bits_data == 22,
            "Held response survives another completed context"); tick();
    end
'''
    body += '''    ports_1_response_ready = 1; tick(); ports_1_response_ready = 0;
    check(!empty && ports_1_response_valid && ports_1_response_bits_tag == 17 && ports_1_response_bits_data == 11,
          "One response handshake releases exactly one context");
    repeat (3) tick(); ports_1_response_ready = 1; tick(); ports_1_response_ready = 0;
    check(empty && !ports_1_response_valid, "Both data contexts drain once");
    end
'''
    return body


def read_queue_contract(parameters):
    stress = ''.join(line_read_window(parameters, fault_beat=beat, stalls=True) for beat in range(512 // parameters['axiDataBits']))
    stress += line_read_window(parameters, terminal='late', stalls=True)
    if parameters['axiDataBits'] < 512:
        stress += line_read_window(parameters, terminal='early', stalls=True)
    if parameters.get('fabricReadSlots') == 1:
        return read_queue_serial_contract(parameters) + line_read_window(parameters) + stress
    base = int(parameters['memoryRegions'][0]['base'])
    last = 0
    width = parameters['axiDataBits']
    first_address, second_address = base+0x138, base+0x124
    first_data, second_data = 0x1122334455667788, 0x98765432
    body = f'''    begin
        integer first_id, second_id, held_id;
        ports_1_request_bits_address = 64'h{first_address:x}; ports_1_request_bits_size = 3;
        ports_1_request_bits_tag = 17; ports_1_request_valid = 1;
        check(ports_1_request_ready, "First read acceptance"); tick(); ports_1_request_valid = 0;
        ports_{last}_request_bits_address = 64'h{second_address:x}; ports_{last}_request_bits_size = 2;
        ports_{last}_request_bits_tag = 17; ports_{last}_request_bits_fetch = 1; ports_{last}_request_valid = 1;
        check(ports_{last}_request_ready, "Same hart instruction and data overlap"); tick(); ports_{last}_request_valid = 0;
        ports_1_request_bits_address = 64'h{base+0x180:x}; ports_1_request_bits_size = 2;
        ports_1_request_valid = 1;
        while (!ar_valid) tick();
        first_id = ar_bits_id;
        repeat (3) begin
          check(ar_bits_id == first_id && ar_bits_addr == 64'h{first_address:x} && ar_bits_len == 0 && !ports_1_request_ready, "First AR hold and client ownership"); tick();
        end
        ar_ready = 1; tick(); ar_ready = 0;
        while (!ar_valid) tick();
        second_id = ar_bits_id;
        check(first_id != second_id && ar_bits_addr == 64'h{second_address:x}, "Second AR before first response");
        ar_ready = 1; tick(); ar_ready = 0;
        r_bits_id = second_id; r_bits_data = {width}'h{second_data << (8*(second_address%(width//8))):x}; r_bits_last = 1; r_valid = 1;
        check(r_ready, "Reordered return accepted"); tick(); r_valid = 0;
        repeat (3) begin
          check(ports_{last}_response_valid && ports_{last}_response_bits_data == 64'h{second_data:x} && ports_{last}_response_bits_tag == 17 && !ports_{last}_response_bits_fault && !ports_1_response_valid && !ports_1_request_ready && !empty, "Same tag reordered response retained by client"); tick();
        end
        ports_{last}_response_ready = 1; tick(); ports_{last}_response_ready = 0;
        r_bits_id = first_id; r_bits_data = {width}'h{first_data << (8*(first_address%(width//8))):x}; r_valid = 1;
        tick(); r_valid = 0;
        check(ports_1_response_valid && ports_1_response_bits_data == 64'h{first_data:x} && ports_1_response_bits_tag == 17 && !ports_1_response_bits_fault && !ports_1_request_ready, "First response identity");
        ports_1_response_ready = 1; tick(); ports_1_response_ready = 0;
        check(ports_1_request_ready && empty, "Client released only after response consumption"); ports_1_request_valid = 0;
        ports_1_request_bits_address = 64'h{1<<parameters['physicalAddressBits']:x}; ports_1_request_bits_tag = 51; ports_1_request_valid = 1;
        tick(); ports_1_request_valid = 0;
        while (!ports_1_response_valid) begin check(!ar_valid, "PMA denial reached AXI"); tick(); end
        check(ports_1_response_bits_fault && ports_1_response_bits_tag == 51, "Local denial ownership");
        ports_1_response_ready = 1; tick(); ports_1_response_ready = 0;
        ports_{last}_request_bits_size = 3; ports_{last}_request_bits_address = 64'h{base+0x130:x}; ports_{last}_request_valid = 1;
        tick(); ports_{last}_request_valid = 0;
        while (!ar_valid) tick(); first_id = ar_bits_id; ar_ready = 1; tick(); ar_ready = 0;
        r_bits_id = first_id; r_bits_last = 0; r_valid = 1; tick(); r_valid = 0;
        check(!ports_{last}_response_valid && r_ready, "Malformed response drains");
        r_bits_last = 1; r_valid = 1; tick(); r_valid = 0;
        check(ports_{last}_response_valid && ports_{last}_response_bits_fault, "Malformed response reports fault");
        ports_{last}_response_ready = 1; tick();
        check(empty, "Final ownership release");
    '''
    body += f'''    ports_{last}_response_ready = 0; r_bits_last = 1;
    ports_{last}_request_valid = 1; tick(); ports_{last}_request_valid = 0;
    while (!ar_valid) tick(); first_id = ar_bits_id; ar_ready = 1; tick(); ar_ready = 0;
    ports_1_request_bits_address = 64'h{first_address:x}; ports_1_request_valid = 1;
    tick(); ports_1_request_valid = 0; while (!ar_valid) tick();
    held_id = ar_bits_id; r_bits_id = held_id; r_valid = 1; tick(); r_valid = 0;
    ports_1_request_valid = 1;
    repeat (3) begin check(!ports_1_request_ready && ar_valid && ar_bits_id == held_id && ar_bits_addr == 64'h{first_address:x} && !empty && !ports_{last}_response_valid, "Unknown RID preserves held AR and real owners"); tick(); end
    ar_ready = 1; tick(); ar_ready = 0;
    r_bits_id = first_id; r_valid = 1; tick(); r_valid = 0;
    check(ports_{last}_response_valid && ports_{last}_response_bits_fault, "Known response drains after protocol fault");
    ports_{last}_response_ready = 1; tick(); ports_{last}_response_ready = 0;
    r_bits_id = held_id; r_valid = 1; tick(); r_valid = 0;
    check(ports_1_response_valid && ports_1_response_bits_fault, "Previously held AR drains with owned fault");
    ports_1_response_ready = 1; tick(); ports_1_response_ready = 0;
    check(!empty && !ports_1_request_ready && !ar_valid, "Protocol fault blocks exclusive handover and ID reuse");
    ports_1_request_valid = 0; reset = 1; tick(); reset = 0; tick();
    check(empty, "Reset clears protocol containment");
    end
'''
    return read_queue_serial_contract(parameters) + body + line_read_contract(parameters) + stress + read_queue_data_contract(parameters)


def coherent_fabric_contract(parameters):
    count = parameters['hartCount']
    base = int(next(r['base'] for r in parameters['memoryRegions'] if r.get('dataCacheable') and r['writable']))
    uncached = int(next(r['base'] for r in parameters['memoryRegions'] if r['readable'] and not r.get('dataCacheable') and not r['device']))
    body = ''
    for operation, address, write, physical in ((1, base, 1, False), (2, base & ~63, 0, False),
                                                 (3, base, 0, False), (0, base, 0, True), (0, uncached, 0, True)):
        targets = (1 if operation == 2 else ((1 << count) - 2) if operation == 1 else
                   (1 << count) - 1 if address == base and operation == 0 else 0)
        body += f'''    begin
      reg [{count-1}:0] seen, pending;
      seen = 0; pending = 0;
      reset = 1; tick(); reset = 0; tick();
      data_0_request_bits_cacheOperation = {operation}; data_0_request_bits_address = 64'h{address:x};
      data_0_request_bits_size = 3; data_0_request_bits_write = {write};
      data_0_request_bits_mask = {255 if write else 0}; data_0_request_bits_tag = 77;
      data_0_request_valid = 1;
      #1; while (!data_0_request_ready) tick(); tick(); data_0_request_valid = 0;
'''
        while_condition = '!axi_ar_valid && !data_0_response_valid' if physical else '!data_0_response_valid'
        body += f'      while ({while_condition}) begin\n'
        if not physical:
            body += '        check(!axi_ar_valid && !axi_aw_valid && !axi_w_valid, "Internal cache operation escaped to AXI");\n'
        if operation:
            body += f'        check({"dut.readers.empty" if count > 1 else "1"}, "Internal cache operation entered ordinary read slots");\n'
        for hart in range(count):
            body += f'''        probe_{hart}_request_ready = 1; probe_{hart}_response_valid = pending[{hart}];
        probe_{hart}_response_bits_data = 0; probe_{hart}_response_bits_mask = 0;
        probe_{hart}_response_bits_word = 0; probe_{hart}_response_bits_last = 1;
'''
        body += '        #1;\n'
        for hart in range(count):
            body += f'''        if (probe_{hart}_response_valid && probe_{hart}_response_ready) pending[{hart}] = 0;
        if (probe_{hart}_request_valid && probe_{hart}_request_ready) begin
          if (seen[{hart}] || probe_{hart}_request_bits_address != 64'h{address & ~63:x} || probe_{hart}_request_bits_invalidate != {int(bool(operation in (1,2)))}) $fatal(1, "Actual fabric probe owner and identity");
          seen[{hart}] = 1; pending[{hart}] = 1;
        end
'''
        body += '        tick();\n      end\n'
        body += f'      check(seen == {count}\'h{targets:x} && pending == 0, "Complete actual-fabric probe set");\n'
        if physical:
            value = 42 << ((address % (parameters['axiDataBits'] // 8)) * 8)
            body += f'''      check(axi_ar_valid && axi_ar_bits_addr == 64'h{address:x} && axi_ar_bits_id == 0 && !data_0_response_valid, "Read follows required coherence service");
      axi_ar_ready = 1; tick(); axi_ar_ready = 0;
      axi_r_bits_data = {parameters['axiDataBits']}'h{value:x}; axi_r_bits_id = 0;
      axi_r_bits_resp = 0; axi_r_bits_last = 1; axi_r_valid = 1;
      while (!axi_r_ready) tick(); tick(); axi_r_valid = 0;
      while (!data_0_response_valid) tick();
'''
        body += f'''      repeat (3) begin
        check(data_0_response_valid && data_0_response_bits_tag == 77 && data_0_response_bits_last && data_0_response_bits_fault == {int(operation == 3)} && data_0_response_bits_data == {42 if physical else 0}, "Coherent fabric completion attribution"); tick();
      end
      data_0_response_ready = 1; tick(); data_0_response_ready = 0;
'''
        body += ''.join(f'      probe_{h}_response_valid = 0; probe_{h}_request_ready = 0;\n' for h in range(count))
        body += '    end\n'
    return body


def fabric_contract(parameters):
    if parameters.get('dCacheWriteback'):
        return coherent_fabric_contract(parameters)
    base = int(next(r['base'] for r in parameters['memoryRegions'] if r['writable'] and r['executable'] and not r['device']))
    width = parameters['axiDataBits']
    data_address, instruction_address = base + 0x238, base + 0x104
    data_value, instruction_value = 0x8877665544332211, 0x12345037
    data_shift = data_address % (width // 8) * 8
    instruction_shift = instruction_address % (width // 8) * 8
    body = f'''
    instruction_request_bits_address = 64'h{instruction_address:x};
    instruction_request_bits_size = 2; instruction_request_bits_fetch = 1;
    instruction_request_bits_tag = 17; instruction_request_valid = 0;
    data_request_bits_address = 64'h{data_address:x}; data_request_bits_size = 3;
    data_request_bits_tag = 34; data_request_valid = 1;
    check(data_request_ready && !instruction_request_ready, "Initial data request ownership");
    tick(); data_request_valid = 0; instruction_request_valid = 0;
    while (!axi_ar_valid) tick();
    repeat (3) begin
      check(axi_ar_bits_addr == 'h{data_address:x} && axi_ar_bits_prot == 1 && axi_ar_bits_id == 0 && !instruction_response_valid, "Data ownership under AXI backpressure"); tick();
    end
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    axi_r_bits_data = 'h{data_value << data_shift:x}; axi_r_bits_last = 1; axi_r_valid = 1;
    tick(); axi_r_valid = 0;
    repeat (3) begin
      check(data_response_valid && data_response_bits_tag == 34 && data_response_bits_data == 64'h{data_value:x} && !data_response_bits_fault && !instruction_response_valid && !axi_ar_valid, "Held data completion retains owner"); tick();
    end
    data_response_ready = 1; tick(); data_response_ready = 0;
    instruction_request_valid = 1;
    check(instruction_request_ready, "Instruction client did not recover");
    tick(); instruction_request_valid = 0;
    while (!axi_ar_valid) tick();
    check(axi_ar_bits_addr == 'h{instruction_address:x} && axi_ar_bits_prot == 5 && axi_ar_bits_id == {parameters['hartCount'] - 1 if not (parameters.get('fabricReadSlots') or parameters['hartCount'] > 1) else 0}, "Instruction ownership");
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    axi_r_bits_data = 'h{instruction_value << instruction_shift:x}; axi_r_bits_id = {parameters['hartCount'] - 1 if not (parameters.get('fabricReadSlots') or parameters['hartCount'] > 1) else 0}; axi_r_valid = 1;
    tick(); axi_r_valid = 0;
    repeat (3) begin
      check(instruction_response_valid && instruction_response_bits_tag == 17 && instruction_response_bits_data == 64'h{instruction_value:x} && !instruction_response_bits_fault && !data_response_valid, "Held instruction completion retains owner"); tick();
    end
    instruction_response_ready = 1; tick(); instruction_response_ready = 0;
    data_request_bits_address = 64'h{1 << parameters['physicalAddressBits']:x}; data_request_bits_tag = 51; data_request_valid = 1;
    tick(); data_request_valid = 0;
    while (!data_response_valid) begin
      check(!axi_ar_valid && !axi_aw_valid && !axi_w_valid, "Denied request reached AXI"); tick();
    end
    repeat (3) begin
      check(data_response_valid && data_response_bits_fault && data_response_bits_tag == 51 && !axi_ar_valid && !axi_aw_valid && !axi_w_valid, "Denied completion ownership"); tick();
    end
    data_response_ready = 1; tick(); data_response_ready = 0;
    data_request_bits_address = 64'h{data_address:x}; data_request_bits_tag = 68; data_request_valid = 1;
    tick(); data_request_valid = 0;
    while (!axi_ar_valid) tick();
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    axi_r_bits_id = 0; axi_r_bits_resp = 2; axi_r_valid = 1; tick(); axi_r_valid = 0;
    repeat (3) begin
      check(data_response_valid && data_response_bits_fault && data_response_bits_tag == 68 && !instruction_response_valid, "Bus fault completion ownership"); tick();
    end
    data_response_ready = 1; tick(); data_response_ready = 0;
'''
    if parameters.get('localInterruptBase') is not None:
        local_base, hart = int(parameters['localInterruptBase']), parameters['hartCount'] - 1
        for address, write, expected, fault in ((local_base + 4 * hart, 1, 0, 0),
                                                (local_base + 4 * hart, 0, 1, 0),
                                                (local_base + 4 * parameters['hartCount'], 0, 0, 1)):
            body += f'''    timeTick = 0; axi_r_bits_resp = 0;
    data_request_bits_address = 64'h{address:x}; data_request_bits_size = 2;
    data_request_bits_write = {write}; data_request_bits_mask = {15 if write else 0};
    data_request_bits_data = 1; data_request_bits_tag = 85; data_request_valid = 1;
    check(data_request_ready, "Local route slot unavailable"); tick(); data_request_valid = 0;
    data_request_bits_address = 'h{data_address:x}; data_request_bits_write = 0; data_request_bits_size = 3;
    while (!data_response_valid) begin
      check(!axi_ar_valid && !axi_aw_valid && !axi_w_valid, "Local route escaped to AXI"); tick();
    end
    repeat (3) begin
      check(data_response_valid && data_response_bits_tag == 85 && data_response_bits_data == {expected} && data_response_bits_fault == {fault} && localInterrupts_{hart}_software && !instruction_response_valid && !axi_ar_valid && !axi_aw_valid && !axi_w_valid, "Local route response ownership"); tick();
    end
    data_response_ready = 1; tick(); data_response_ready = 0;
'''
    body = body.replace('instruction_', f"instruction_{parameters['hartCount']-1}_").replace('data_request_', 'data_0_request_').replace('data_response_', 'data_0_response_')
    if parameters.get('fabricReadSlots') or parameters['hartCount'] > 1:
        overlap = read_queue_contract(parameters)
        overlap = re.sub(r'\bports_(\d+)_', lambda m: f'{"instruction" if int(m[1]) % 2 == 0 else "data"}_{int(m[1]) // 2}_', overlap)
        overlap = re.sub(r'\b(ar|r)_', r'axi_\1_', overlap).replace('empty', 'dut.readers.empty')
        body += '    axi_r_bits_resp = 0;\n' + overlap
        body += fabric_exclusive_contract(parameters)
    return body


def fabric_exclusive_contract(parameters):
    hart = parameters['hartCount'] - 1
    base = int(next(r['base'] for r in parameters['memoryRegions'] if r['writable'] and not r['device']))
    def probes(writer, address):
        if not parameters.get('dCacheBytes'):
            return ''
        body = f'    check(!probe_{writer}_request_valid, "Ordinary writer retains its copy");\n'
        for peer in range(parameters['hartCount']):
            if peer == writer:
                continue
            body += f'''    while (!probe_{peer}_request_valid) begin check(!axi_aw_valid && !axi_w_valid, "Write waits for peer probes"); tick(); end
    check(probe_{peer}_request_bits_address == 64'h{address & ~63:x} && probe_{peer}_request_bits_invalidate, "Peer probe line and action");
    probe_{peer}_request_ready = 1; tick(); probe_{peer}_request_ready = 0;
    probe_{peer}_response_bits_data = 0; probe_{peer}_response_bits_mask = 0; probe_{peer}_response_bits_word = 0; probe_{peer}_response_bits_last = 1;
    probe_{peer}_response_valid = 1; while (!probe_{peer}_response_ready) tick(); tick(); probe_{peer}_response_valid = 0;
'''
        return body
    depth = parameters.get('fabricReadSlots') or 2
    identities = (*range(depth - 1), 2 * parameters['hartCount'] - 1)
    body = f'    begin\n      integer bus_id[{depth}], post_id, index;\n      axi_r_bits_resp = 0; axi_r_bits_last = 1;\n'
    for index, source in enumerate(identities):
        reader = f'{"instruction" if source % 2 == 0 else "data"}_{source // 2}'
        body += f'''    {reader}_request_bits_write = 0; {reader}_request_bits_atomic = 0; {reader}_request_bits_fetch = {int(source % 2 == 0)};
    {reader}_request_bits_address = 'h{base+0x100+8*index:x}; {reader}_request_bits_size = {2 if source % 2 == 0 else 3};
    {reader}_request_bits_tag = {51 + index};
    {reader}_response_ready = 0; {reader}_request_valid = 1; #1;
    while (!{reader}_request_ready) tick(); tick(); {reader}_request_valid = 0;
'''
    body += f'''    repeat ({depth}) begin
      while (!axi_ar_valid) tick();
      index = integer'((axi_ar_bits_addr - 'h{base+0x100:x}) / 8);
      check(index >= 0 && index < {depth}, "Read address belongs to accepted owner");
      bus_id[index] = axi_ar_bits_id; axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    end
    data_0_request_bits_address = 'h{base+0x200:x}; data_0_request_bits_size = 3;
    data_0_request_bits_write = 1; data_0_request_bits_atomic = 0; data_0_request_bits_fetch = 0; data_0_request_bits_mask = 255;
    data_0_request_bits_data = 17; data_0_request_bits_tag = 85; data_0_request_valid = 1;
    instruction_{hart}_request_bits_address = 'h{base+0x180:x};
    instruction_{hart}_request_bits_size = 2; instruction_{hart}_request_valid = 1;
    repeat (3) begin
      check(!data_0_request_ready && !instruction_{hart}_request_ready && !axi_aw_valid && !axi_w_valid, "Exclusive request waits for all accepted reads"); tick();
    end
'''
    for index, source in enumerate(identities[:-1]):
        reader = f'{"instruction" if source % 2 == 0 else "data"}_{source // 2}'
        body += f'''    axi_r_bits_id = bus_id[{index}]; axi_r_valid = 1; tick(); axi_r_valid = 0;
    {reader}_response_ready = 1; tick(); {reader}_response_ready = 0;
    check(!data_0_request_ready && !axi_aw_valid && !axi_w_valid, "Partial drain cannot release exclusive traffic");
'''
    body += f'''    axi_r_bits_id = bus_id[{depth - 1}]; axi_r_valid = 1; tick(); axi_r_valid = 0;
    repeat (3) begin
      check(data_{hart}_response_valid && !data_0_request_ready && !axi_aw_valid && !axi_w_valid, "Exclusive request waits for held read response"); tick();
    end
    data_{hart}_response_ready = 1; tick(); data_{hart}_response_ready = 0;
    check(data_0_request_ready && !instruction_{hart}_request_ready, "Waiting writer precedes another read");
    tick(); data_0_request_valid = 0;
'''
    body += probes(0, base + 0x200)
    body += f'''
    while (!axi_aw_valid || !axi_w_valid) begin check(!axi_ar_valid, "Read bypassed exclusive writer"); tick(); end
    axi_aw_ready = 1; tick(); axi_aw_ready = 0;
    repeat (3) begin check(axi_w_valid && !axi_ar_valid, "Split write retains exclusive ownership"); tick(); end
    axi_w_ready = 1; tick(); axi_w_ready = 0;
    axi_b_bits_id = 0; axi_b_bits_resp = 0; axi_b_valid = 1;
    while (!axi_b_ready) tick(); tick(); axi_b_valid = 0;
    while (!data_0_response_valid) tick();
    repeat (3) begin
      check(data_0_response_bits_tag == 85 && !data_0_response_bits_fault && !instruction_{hart}_request_ready && !axi_ar_valid, "Exclusive ownership lasts through response consumption"); tick();
    end
    data_0_response_ready = 1; tick(); data_0_response_ready = 0;
    check(instruction_{hart}_request_ready, "Read resumes after exclusive response");
    tick(); instruction_{hart}_request_valid = 0;
    while (!axi_ar_valid) tick();
    post_id = axi_ar_bits_id;
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    axi_r_bits_id = post_id; axi_r_valid = 1; tick(); axi_r_valid = 0;
    instruction_{hart}_response_ready = 1; tick(); instruction_{hart}_response_ready = 0;
'''
    if parameters.get('dCacheRefillBytes') == 64:
        bus_bytes = parameters['axiDataBits'] // 8
        body += f'''    data_0_request_bits_address = 'h{base + 0x100:x}; data_0_request_bits_size = 6;
    data_0_request_bits_write = 0; data_0_request_bits_atomic = 0; data_0_request_bits_fetch = 0;
    data_0_request_bits_tag = 93; data_0_request_valid = 1; #1;
    while (!data_0_request_ready) tick(); tick(); data_0_request_valid = 0;
    while (!axi_ar_valid) tick();
    check(axi_ar_bits_len == {64 // bus_bytes - 1} && axi_ar_bits_size == {bus_bytes.bit_length() - 1} && axi_ar_bits_id == 0 && !axi_ar_bits_prot[2], "Fabric sends data line through exclusive bridge");
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    data_{hart}_request_bits_address = 'h{base + 0x180:x}; data_{hart}_request_bits_size = 3;
    data_{hart}_request_bits_write = 1; data_{hart}_request_bits_mask = 255;
    data_{hart}_request_bits_data = 17; data_{hart}_request_bits_tag = 94; data_{hart}_request_valid = 1;
'''
        for beat in range(64 // bus_bytes):
            body += f'''    axi_r_bits_id = 0; axi_r_bits_data = '1; axi_r_bits_last = {int(beat == 64 // bus_bytes - 1)};
    axi_r_valid = 1; while (!axi_r_ready) tick(); tick(); axi_r_valid = 0;
'''
            for part in range(bus_bytes // 8):
                body += f'''    while (!data_0_response_valid) tick();
    repeat (3) begin
      check(data_0_response_bits_tag == 93 && !data_0_response_bits_fault && data_0_response_bits_last == {int(beat * bus_bytes // 8 + part == 7)} && !data_{hart}_request_ready && !axi_aw_valid && !axi_w_valid, "Line ownership excludes writes until final response consumption"); tick();
    end
    data_0_response_ready = 1; tick(); data_0_response_ready = 0;
'''
        body += f'''    while (!data_{hart}_request_ready) tick(); tick(); data_{hart}_request_valid = 0;
''' + probes(hart, base + 0x180) + f'''    while (!axi_aw_valid || !axi_w_valid) tick();
    axi_aw_ready = 1; axi_w_ready = 1; tick(); axi_aw_ready = 0; axi_w_ready = 0;
    axi_b_bits_id = {hart}; axi_b_bits_resp = 0; axi_b_valid = 1;
    while (!axi_b_ready) tick(); tick(); axi_b_valid = 0;
    while (!data_{hart}_response_valid) tick();
    check(data_{hart}_response_bits_tag == 94 && !data_{hart}_response_bits_fault, "Waiting write completes after line release");
    data_{hart}_response_ready = 1; tick(); data_{hart}_response_ready = 0;
'''
    return body + '    end\n'


def muldiv_contract():
    edges = (0, 1, 2, (1 << 64) - 1, 1 << 63, (1 << 63) - 1, 1 << 32, 0x80000000, 0x80000001, 0xaaaaaaaa55555555)
    rng = random.Random(2026)
    pairs = [(a, b) for a in edges for b in edges]
    pairs += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(32)]
    body = ''
    for instruction, a, b in ((muldiv(6, 1, 2, function, word), a, b) for word in (False, True)
                              for function in ((0, 4, 5, 6, 7) if word else range(8)) for a, b in pairs):
        body += f'''
    input_bits_decoded_instruction_instruction = 32'h{instruction:x};
    input_bits_operand1 = 64'h{a:x}; input_bits_operand2 = 64'h{b:x}; input_valid = 1;
    check(input_ready && !output_valid, "MulDiv resource reuse"); tick();
    input_bits_operand1 = ~input_bits_operand1; input_bits_operand2 = ~input_bits_operand2;
    input_bits_decoded_instruction_instruction = '1;
    for (integer cycles = 0; !output_valid; cycles++) begin
      check(!input_ready && cycles < {32 if instruction & 127 == 0x3b else 64}, "MulDiv acceptance or completion bound"); tick();
    end
    input_valid = 0;
    repeat (3) begin
      check(!input_ready && output_valid && output_bits == 64'h{muldiv_value(instruction, a, b) & MASK:x}, "MulDiv value and held completion"); tick();
    end
    output_ready = 1; tick(); output_ready = 0;
'''
    return body


def backend_muldiv_contract():
    def send(words, pc, tag):
        return ''.join(f'''
    instruction_bits_pc = 'h{pc + 4 * index:x}; instruction_bits_instruction = 'h{word:x};
    instruction_bits_tag = {tag + index}; instruction_valid = 1;
    while (!instruction_ready) tick(); tick(); instruction_valid = 0;
''' for index, word in enumerate(words))

    reset = '''
    reset = 1; tick(); reset = 0; tick();
    data_request_ready = 0; data_response_valid = 0; data_response_bits_fault = 0;
'''
    setup = send((addi(2, 0, -1), addi(3, 0, -1)), 0x100, 1) + '    repeat (8) tick();\n'
    complete = '''
    data_request_ready = 1; tick(); data_request_ready = 0;
    data_response_bits_tag = data_request_bits_tag; data_response_valid = 1;
    tick(); data_response_valid = 0; repeat (8) tick();
'''
    body = reset + setup + send((sd(3, 0), addi(6, 0, 0), mul(4, 2, 3), addi(5, 4, 1)), 0x180, 10)
    body += '''
    while (!data_request_valid) tick();
    while (!dut.mulDiv.output_valid) tick();
    repeat (3) begin
      check(data_request_valid && data_request_bits_write && data_request_bits_tag == 10 &&
        dut.executePending && dut.issuedValid && !dut.mulDiv.input_valid &&
        dut.mulDiv.output_valid && dut.mulDiv.output_bits == 1, "Blocked mulDiv retains owner and destination"); tick();
    end
''' + complete + send((sd(5, 0),), 0x200, 20) + '''
    while (!data_request_valid) tick();
    check(data_request_bits_write && data_request_bits_data == 2, "Dependent instruction used a stale mulDiv result");
''' + complete
    for held in (False, True):
        body += reset + setup
        words = (0x00003303 if held else 0x73, mul(4, 2, 3), sd(2, 0))
        body += send(words, 0x180, 10)
        if held:
            body += '''
    while (!data_request_valid || dut.mulDiv.remaining != 7) tick();
    check(dut.executePending && !dut.mulDiv.output_valid, "Fault response did not precede mulDiv completion");
    data_request_ready = 1; tick(); data_request_ready = 0;
    data_response_bits_tag = 10; data_response_bits_fault = 1; data_response_valid = 1;
    tick(); data_response_valid = 0; data_response_bits_fault = 0;
'''
        body += f'''
    while (!redirect) begin check(!data_request_valid, "Younger store escaped before redirect"); tick(); end
    check(dut.executePending && dut.mulDiv.{'valid' if held else 'busy'}, "Redirect did not overlap the mulDiv operation");
    tick();
    check(!dut.issuedValid && !data_request_valid, "Redirect retained a younger effect");
'''
        body += send((addi(5, 4, 7), sd(5, 0)), 0x200, 20) + '''
    while (!data_request_valid) tick();
    check(data_request_bits_write && data_request_bits_data == 7 && data_request_bits_tag == 21,
      "Cancelled mulDiv wrote its destination or polluted slot reuse");
''' + complete
    return body


def backend_queue_contract(parameters):
    def send(words, pc=0x100):
        return ''.join(f'''    @(negedge clock); instruction_bits_pc = 'h{pc + 4 * index:x};
    instruction_bits_instruction = 'h{word:x}; instruction_bits_tag = 73; instruction_bits_length = 4;
    instruction_valid = 1; #1; while (!instruction_ready) tick(); tick(); instruction_valid = 0;
''' for index, word in enumerate(words))

    def response(tag, value, fault=False):
        return f'''    @(negedge clock); data_response_bits_tag = {tag}; data_response_bits_data = {value};
    data_response_bits_fault = {int(fault)}; data_response_valid = 1;
    #1; while (!data_response_ready) tick(); tick(); data_response_valid = 0; data_response_bits_fault = 0;
'''

    body = ''
    for mode in ('reverse', 'waw', 'old_fault', 'young_fault', *(('interrupt',) if parameters['enableInterrupts'] else ())):
        second = 3 if mode == 'waw' else 4
        result = 23 if mode == 'waw' else 33
        words = (ld(3, 0, 0x200), ld(second, 0, 0x240),
                 addi(5, 3, 1) if mode == 'waw' else alu(5, 3, 4, 0), sd(5, 0, 0x280))
        if mode == 'interrupt':
            words = (*words[:2], mul(5, 1, 1), addi(6, 0, 7), sd(6, 0, 0x280))
        body += '''    begin
    integer writes;
    logic [7:0] saved_tag;
    writes = 0; instruction_valid = 0; instruction_bits_fault = 0;
    data_request_ready = 0; data_response_valid = 0; data_response_bits_fault = 0;
    reset = 1; tick(); reset = 0; tick();
'''
        if mode == 'interrupt':
            body += '    interrupts_external = 0;\n' + send((addi(1, 0, 0x400), csr(0, 0x305, 1), addi(2, 0, -1),
                csr(0, 0x304, 2), addi(3, 0, 8), csr(0, 0x300, 3)), 0xe8) + '    while (!dut.csr.status[3]) tick();\n'
        body += '''    fork
      forever begin
        @(posedge clock);
        if (dut.gpr.we_0) begin
'''
        expected = ((3, 11),) if mode == 'young_fault' else () if mode == 'old_fault' else ((3, 11), (4, 22)) if mode == 'interrupt' else ((3, 11), (second, 22), (5, result))
        checks = ' || '.join(f'(writes == {index} && dut.gpr.waddr_0 == {rd} && dut.gpr.wdata_0 == {value})'
                            for index, (rd, value) in enumerate(expected)) or "1'b0"
        body += f'''          if (!({checks})) $fatal(1, "Dual-load retirement order and dependencies: write=%0d rd=%0d value=%h pc=%h", writes, dut.gpr.waddr_0, dut.gpr.wdata_0, dut.commitPackets_0_instruction_pc);
          writes++;
        end
      end
    join_none
'''
        body += send(words)
        for index, address in enumerate((0x200, 0x240)):
            body += f'''    while (!data_request_valid) tick();
    check(data_request_bits_address == 'h{address:x} && !data_request_bits_write && data_request_bits_tag == {index},
          "Two real backend reads precede either response");
    data_request_ready = 1; tick(); data_request_ready = 0;
'''
        body += '    repeat (4) begin check(!redirect && writes == 0 && !data_request_valid, "Pending reads retain architectural ownership"); tick(); end\n'
        if mode == 'interrupt':
            body += '    interrupts_external = 1;\n'
        if mode == 'old_fault':
            body += response(0, 11, True)
            body += '    repeat (5) begin check(!redirect && writes == 0 && !data_request_valid, "Old fault waits for younger accepted read to drain"); tick(); end\n'
            body += response(1, 22)
        else:
            body += response(1, 22, mode == 'young_fault')
            body += '    repeat (4) begin check(!redirect && writes == 0 && !data_request_valid, "Younger completion cannot retire before older load"); tick(); end\n'
            body += response(0, 11)
        if 'fault' in mode:
            body += f'''    while (!redirect) begin check(!data_request_valid, "Younger store escaped a load fault"); tick(); end
    check(status_trap && dut.commitPackets_0_instruction_pc == 'h{0x100 if mode == 'old_fault' else 0x104:x} &&
          dut.commitPackets_0_instruction_tval == 'h{0x200 if mode == 'old_fault' else 0x240:x} && writes == {len(expected)},
          "Precise oldest fault context"); tick();
    repeat (8) begin check(!data_request_valid && !dut.gpr.we_0 && !redirect, "Cancelled dual-load effects do not escape"); tick(); end
'''
        elif mode == 'interrupt':
            body += '''    for (integer waited = 0; !redirect; waited++) begin
      check(waited < 8 && !data_request_valid, "Interrupt waits only for accepted loads"); tick(); end
    check(status_trap && writes == 2, "Both accepted loads retire before interrupt"); tick();
    check(dut.csr.returnPc == 'h108, "Interrupt cancels younger arithmetic");
    interrupts_external = 0;
'''
        else:
            body += f'''    while (!data_request_valid) tick();
    check(data_request_bits_write && data_request_bits_address == 'h280 && data_request_bits_data == {result} && writes == 3,
          "Dependent store follows both load retirements");
    saved_tag = data_request_bits_tag;
    data_request_ready = 1; tick(); data_request_ready = 0;
    data_response_bits_tag = saved_tag; data_response_valid = 1;
    #1; while (!data_response_ready) tick(); tick(); data_response_valid = 0;
    repeat (8) begin check(!data_request_valid && !redirect, "Dual-load window releases once"); tick(); end
'''
        body += '    disable fork; end\n'
    return body


def backend_contract(parameters):
    words = [(2 << 12) | (1 << 7) | 0x37, addi(2, 0, 42), sd(2, 1), 0x73, sd(2, 1, 8)]
    body = f'''    instruction_bits_length = 4;
    instruction_bits_instruction = 'h{addi(2, 0, 7):x}; instruction_valid = 1;
    while (!instruction_ready) tick(); tick(); instruction_valid = 0;
    for (integer stage = 0; stage < 6; stage++) begin
      check({{dut.commitValid, dut.memoryValid, dut.resultValid, dut.issuedValid, dut.decodedValid, dut.instructionValid}} == (1 << stage), "Backend register boundaries"); tick();
    end
'''
    for index, word in enumerate(words):
        body += f'''
    instruction_bits_pc = 'h{0x100 + 4 * index:x}; instruction_bits_instruction = 'h{word:x};
    instruction_bits_tag = {index}; instruction_valid = 1;
    while (!instruction_ready) tick();
    tick(); instruction_valid = 0;
'''
    body += f'''
    while (!data_request_valid) tick();
    instruction_bits_pc = 'h114; instruction_bits_instruction = 'h{addi(0, 0, 0):x};
    instruction_bits_tag = 5; instruction_valid = 1;
    repeat (8) begin
      check(data_request_valid && data_request_bits_write && data_request_bits_address == 'h2000 && data_request_bits_data == 42 && data_request_bits_mask == 255 && data_request_bits_tag == 2, "Backend RAW dependencies and blocked store");
      if (instruction_ready) begin tick(); instruction_bits_pc += 4; instruction_bits_tag += 1; end else tick();
    end
    check(!instruction_ready, "Blocked backend exceeded its capacity");
    data_request_ready = 1; tick(); data_request_ready = 0;
    data_response_bits_tag = 2; data_response_valid = 1; tick(); data_response_valid = 0;
    while (!redirect) begin
      check(!data_request_valid, "Younger store escaped before trap");
      if (instruction_valid && instruction_ready) begin tick(); instruction_valid = 0; end
      else tick();
    end
    check(redirectPc == 0 && status_trap && !instruction_ready && !data_request_valid, "Precise trap redirect");
    instruction_valid = 0; tick();
    repeat (3) begin check(!data_request_valid, "Younger store survived redirect"); tick(); end
    instruction_bits_pc = 'h200; instruction_bits_instruction = 'h{sd(2, 1):x};
    instruction_bits_tag = 6; instruction_bits_fault = 1;
    instruction_bits_cause = 1; instruction_bits_tval = 'h200; instruction_valid = 1;
    while (!instruction_ready) tick();
    tick(); instruction_valid = 0;
    while (!redirect) begin check(!data_request_valid, "Fault packet caused a data access"); tick(); end
    check(redirectPc == 0 && status_trap, "Injected instruction fault");
    tick(); instruction_bits_fault = 0; instruction_bits_cause = 0; instruction_bits_tval = 0;
'''
    for index, word in enumerate((csr(3, 0x342, 0, True), sd(3, 1))):
        body += f'''
    instruction_bits_pc = 'h{0x300 + 4 * index:x}; instruction_bits_instruction = 'h{word:x};
    instruction_bits_tag = {7 + index}; instruction_valid = 1;
    while (!instruction_ready) tick();
    tick(); instruction_valid = 0;
'''
    return body + '''
    while (!data_request_valid) tick();
    check(data_request_bits_write && data_request_bits_address == 'h2000 && data_request_bits_data == 1 && data_request_bits_tag == 8, "Fault context survived retirement");
    data_request_ready = 1; tick(); data_request_ready = 0;
    data_response_bits_tag = 8; data_response_valid = 1; tick(); data_response_valid = 0;
    repeat (6) begin check(!data_request_valid && !redirect, "Unexpected backend effect"); tick(); end
''' + (backend_muldiv_contract() if parameters.get('enableM', True) else '')


def backend_group_contract(parameters):
    if parameters['issueWidth'] == 1:
        return ''
    sequences = (
        ((addi(1, 2, 1), addi(3, 2, 2)), (2,), ((1, 6), (3, 7))),
        ((addi(1, 2, 1), addi(3, 1, 2)), (1, 1), ((1, 6), (3, 8))),
        ((addi(1, 2, 1), addi(1, 2, 2)), (1, 1), ((1, 6), (1, 7))),
        ((addi(1, 2, 1), addi(2, 0, 9)), (2,), ((1, 6), (2, 9))),
        ((addi(0, 2, 1), addi(3, 0, 2)), (2,), ((0, 0), (3, 2))),
        ((addi(1, 2, 1), 0), (1, 1), ((1, 6), (0, 0))))
    if parameters['issueWidth'] == 3:
        sequences += (
            ((addi(1, 2, 1), addi(3, 2, 2), addi(4, 2, 3)), (3,), ((1, 6), (3, 7), (4, 8))),
            ((addi(1, 2, 1), addi(3, 2, 2), addi(4, 1, 3)), (2, 1), ((1, 6), (3, 7), (4, 9))),
            ((addi(1, 2, 1), addi(3, 2, 2), addi(4, 3, 3)), (2, 1), ((1, 6), (3, 7), (4, 10))),
            ((addi(1, 2, 1), addi(3, 1, 2), addi(4, 2, 3)), (1, 2), ((1, 6), (3, 8), (4, 8))),
            ((addi(1, 2, 1), addi(3, 2, 2), addi(1, 2, 3)), (2, 1), ((1, 6), (3, 7), (1, 8))),
            ((addi(1, 2, 1), addi(3, 2, 2), addi(2, 0, 9)), (3,), ((1, 6), (3, 7), (2, 9))),
            ((addi(0, 2, 1), addi(3, 0, 2), addi(4, 2, 3)), (3,), ((0, 0), (3, 2), (4, 8))),
            ((addi(1, 2, 1), addi(3, 2, 2), 0), (2, 1), ((1, 6), (3, 7), (0, 0))))
    body = ''
    for words, groups, writes in sequences:
        body += f'''
    instruction_valid = 0; data_response_valid = 0;
    reset = 1; tick(); reset = 0; tick();
    instruction_valid = 1; instruction_bits_count = 1;
    instruction_bits_packets_0_pc = 'h100; instruction_bits_packets_0_fault = 0;
    instruction_bits_packets_0_length = 4; instruction_bits_packets_0_instruction = 'h{addi(2, 0, 5):x};
    while (!instruction_ready) tick(); tick(); instruction_valid = 0; repeat (8) tick();
    instruction_bits_count = {len(words)};
'''
        for lane, word in enumerate(words):
            body += f'''    instruction_bits_packets_{lane}_pc = 'h{0x200 + lane * 4:x};
    instruction_bits_packets_{lane}_instruction = 'h{word:x};
    instruction_bits_packets_{lane}_length = 4; instruction_bits_packets_{lane}_fault = 0;
'''
        body += '    instruction_valid = 1; while (!instruction_ready) tick(); tick(); instruction_valid = 0;\n'
        for stage in ('issued', 'commit'):
            consumed = 0
            for count in groups:
                conditions = [f'dut.{stage}Count == {count}']
                if stage == 'issued':
                    conditions += [f"dut.issuedPackets_{lane}_decoded_instruction_pc == 'h{0x200+4*(consumed+lane):x}" for lane in range(count)]
                else:
                    for lane, (rd, value) in enumerate(writes[consumed:consumed+count]):
                        conditions.append(f'dut.gpr.we_{lane} == {int(rd != 0)}')
                        if rd:
                            conditions.append(f'dut.gpr.waddr_{lane} == {rd} && dut.gpr.wdata_{lane} == {value}')
                body += f'    while (dut.{stage}Count == 0) tick();\n    check(' + ' && '.join(conditions) + f', "Ordered {stage} prefix, retained tail and operands"); tick();\n'
                if stage == 'commit' and parameters.get('enableInterrupts') and all(words[consumed:consumed+count]):
                    body += f'    check(dut.resumePc == \'h{0x200+4*(consumed+count):x}, "Resume after youngest retired instruction");\n'
                consumed += count
        body += '    repeat (8) tick();\n'
    if parameters.get('enableInterrupts'):
        body += '''
    instruction_valid = 0; interrupts_software = 0; interrupts_timer = 0; interrupts_external = 0;
    reset = 1; tick(); reset = 0; tick();
    instruction_bits_count = 1; instruction_bits_packets_0_pc = 'h100;
    instruction_bits_packets_0_length = 4; instruction_bits_packets_0_fault = 0;
'''
        for word in (addi(1, 0, 8), csr(0, 0x304, 1)):
            body += f'''    instruction_bits_packets_0_instruction = 'h{word:x}; instruction_valid = 1;
    while (!instruction_ready) tick(); tick(); instruction_valid = 0; repeat (8) tick();
'''
        body += f'''
    instruction_bits_count = 2; instruction_bits_packets_0_pc = 'h200;
    instruction_bits_packets_0_instruction = 'h10500073;
    instruction_bits_packets_1_pc = 'h204; instruction_bits_packets_1_instruction = 'h{mul(3, 1, 1) if parameters.get('enableM', True) else addi(3, 1, 1):x};
    instruction_bits_packets_1_length = 4; instruction_bits_packets_1_fault = 0;
    instruction_valid = 1; while (!instruction_ready) tick(); tick(); instruction_valid = 0;
    while (dut.commitCount == 0 || !dut.commitPackets_0_wfi) tick();
    tick(); check(status_sleep && {"dut.executePending && " if parameters.get("enableM", True) else ""}dut.resumePc == 'h204, "WFI cancels younger mulDiv and retains resume PC");
    repeat (8) begin check(status_sleep && !instruction_ready && !data_request_valid, "Sleep drains owned execution"); tick(); end
    check({"!dut.executePending" if parameters.get("enableM", True) else "!data_request_valid"}, "Cancelled execution drained");
    interrupts_software = 1; tick();
    check(!status_sleep && instruction_ready && !status_trap, "Locally enabled wake without global trap");
    interrupts_software = 0;
'''
    return body


def backend_branch_contract():
    def send(word, pc, tag):
        return f'''    instruction_bits_packets_0_instruction = 'h{word:x}; instruction_bits_packets_0_pc = 'h{pc:x};
    instruction_bits_packets_0_tag = {tag}; instruction_valid = 1; #1;
    while (!instruction_ready) tick(); tick(); instruction_valid = 0;
'''
    body = ''
    for fault in (False, True):
        body += '''    instruction_valid = 0; data_request_ready = 0; data_response_valid = 0;
    reset = 1; tick(); reset = 0; tick();
    instruction_bits_count = 1; instruction_bits_packets_0_length = 4;
    instruction_bits_packets_0_fault = 0; instruction_bits_packets_0_predictedTaken = 0;
'''
        body += send(ld(3, 0, 0x100), 0x100, 1)
        body += '''    while (!data_request_valid) tick();
    check(data_request_bits_address == 'h100 && !data_request_bits_write, "Older load owns data request");
'''
        body += send((0x40 << 20) | (4 << 7) | 0x6f, 0x200, 2)
        body += send(sd(0, 0, 0x108), 0x204, 3)
        body += send(addi(5, 0, 99), 0x208, 4)
        body += '''    while (!redirect) begin check(!data_request_bits_write, "Younger memory cannot pass older load"); tick(); end
    check(!status_trap && redirectPc == 'h240 && dut.issuedCount == 1 && dut.memoryPending,
      "Branch recovery occurs at execution with older memory retained");
    check(!instruction_ready && data_request_valid && !data_request_bits_write, "Recovery holds older request and stops younger work");
    tick();
    check(dut.resultCount == 1 && dut.resultPackets_0_instruction_pc == 'h200 && dut.instructionCount == 0 && dut.decodedCount == 0,
      "Recovery preserves branch and removes younger instructions");
'''
        body += send(addi(6, 0, 7), 0x240, 5)
        body += '''    repeat (4) begin check(!redirect && data_request_valid && !data_request_bits_write, "Recovery is one-shot under older stall"); tick(); end
    data_request_ready = 1; tick(); data_request_ready = 0;
    data_response_bits_tag = 1; data_response_bits_data = 42;
'''
        body += f'    data_response_bits_fault = {int(fault)}; data_response_valid = 1; tick(); data_response_valid = 0; data_response_bits_fault = 0;\n'
        if fault:
            body += '''    while (!redirect) begin check(!dut.gpr.we_0, "Older fault suppresses speculative register writes"); tick(); end
    check(status_trap && redirectPc == 0 && dut.commitPackets_0_instruction_pc == 'h100, "Older load fault overrides resolved branch");
    tick(); repeat (10) begin check(!dut.gpr.we_0 && !data_request_valid && !redirect, "Fault discards branch and target work"); tick(); end
'''
        else:
            body += '''    begin
      integer writes;
      writes = 0;
      repeat (16) begin
        check(!redirect && !data_request_valid, "Resolved branch never redirects twice or publishes wrong-path store");
        if (dut.gpr.we_0) begin
          check((writes == 0 && dut.gpr.waddr_0 == 3 && dut.gpr.wdata_0 == 42) ||
                (writes == 1 && dut.gpr.waddr_0 == 4 && dut.gpr.wdata_0 == 'h204) ||
                (writes == 2 && dut.gpr.waddr_0 == 6 && dut.gpr.wdata_0 == 7), "Ordered older load, link and target retirement");
          writes = writes + 1;
        end
        tick();
      end
      check(writes == 3, "All retained instructions retire exactly once");
    end
'''
    return body


def backend_memory_group_contract(parameters):
    width = parameters['issueWidth']
    if width == 1:
        return ''
    body = ''
    for operation in ('load', 'byte', 'store'):
        for fault in (0, 1):
            words = [sd(0,0,0x200) if operation=='store' else load(3,0,0x200,size=0) if operation=='byte' else ld(3,0,0x200)]
            words += [addi(10 + lane, 0, 20 + lane) for lane in range(1,width)]
            body += f'''    instruction_valid = 0; data_request_ready = 0; data_response_valid = 0;
    reset = 1; tick(); reset = 0; tick(); instruction_bits_count = {width};
'''
            for lane, word in enumerate(words):
                body += f'''    instruction_bits_packets_{lane}_pc = 'h{0x100+4*lane:x}; instruction_bits_packets_{lane}_instruction = 'h{word:x};
    instruction_bits_packets_{lane}_length = 4; instruction_bits_packets_{lane}_fault = 0; instruction_bits_packets_{lane}_tag = {lane};
    instruction_bits_packets_{lane}_predictedTaken = 0;
'''
            body += f'''    instruction_valid = 1; #1; while (!instruction_ready) tick(); tick(); instruction_valid = 0;
    while (dut.issuedCount == 0) tick();
    check(dut.issuedCount == {width}, "Ordinary memory groups with independent ALU followers");
    while (!data_request_valid) tick();
    check(data_request_bits_address == 'h200 && data_request_bits_write == {int(operation=='store')}, "Group has one head memory request");
    repeat (4) begin check(dut.memoryCount == {width} && dut.memoryPending && dut.commitCount == 0 && data_request_valid,
      "Mixed group retains all followers while request stalls"); tick(); end
    data_request_ready = 1; tick(); data_request_ready = 0;
    repeat (4) begin check(dut.memoryCount == {width} && dut.memoryPending && dut.commitCount == 0, "Mixed group waits for response"); tick(); end
    data_response_bits_data = 42; data_response_bits_tag = 0; data_response_bits_fault = {fault}; data_response_valid = 1;
    tick(); data_response_valid = 0; data_response_bits_fault = 0;
    while (dut.commitCount == 0) tick();
    check(dut.commitCount == {width}, "Completed group remains intact until retirement");
'''
            for lane in range(width):
                writes = not fault and (lane!=0 or operation!='store')
                condition = f'dut.gpr.we_{lane} == {int(writes)}'
                if writes: condition += f' && dut.gpr.waddr_{lane} == {3 if lane==0 else 10+lane} && dut.gpr.wdata_{lane} == {42 if lane==0 else 20+lane}'
                body += f'    check({condition}, "Precise mixed-group register writes");\n'
            body += f'    check(status_trap == {fault}, "Memory fault traps once"); tick();\n'
            body += '    repeat (8) begin check(!data_request_valid && dut.commitCount == 0 && !redirect, "No duplicate mixed-group effects"); tick(); end\n'
    return body


def backend_interrupt_contract():
    body = ''
    for mode in range(4):
        memory = mode != 0
        body += '''
    reset = 1; tick(); reset = 0; tick();
    interrupts_software = 0; interrupts_timer = 0; interrupts_external = 0;
    instruction_valid = 0; instruction_bits_fault = 0; instruction_bits_length = 4;
    data_request_ready = 0; data_response_valid = 0; data_response_bits_fault = 0;
'''
        for index, word in enumerate((addi(1, 0, 0x400), csr(0, 0x305, 1), addi(2, 0, -1),
                                      csr(0, 0x304, 2), addi(3, 0, 8), csr(0, 0x300, 3))):
            body += f"    instruction_bits_pc = 'h{0x100 + index * 4:x}; instruction_bits_instruction = 'h{word:x}; instruction_valid = 1;\n    while (!instruction_ready) tick(); tick(); instruction_valid = 0; repeat (8) tick();\n"
        if memory:
            body += f"    instruction_bits_pc = 'h200; instruction_bits_instruction = 'h{sd(2, 1):x}; instruction_bits_tag = 22; instruction_valid = 1;\n    while (!instruction_ready) tick(); tick(); instruction_valid = 0;\n"
            body += '''
    while (!data_request_valid) tick();
''' + ('    interrupts_external = 1;\n' if mode == 1 else '') + '''
    repeat (4) begin check(data_request_valid && !redirect, "Interrupt withdrew a presented store"); tick(); end
    data_request_ready = 1; tick(); data_request_ready = 0;
    repeat (4) begin check(!redirect, "Interrupt abandoned a store response"); tick(); end
''' + ('    interrupts_external = 1;\n' if mode == 2 else '') + '''
    data_response_valid = 1; data_response_bits_tag = 22; tick(); data_response_valid = 0;
'''
            if mode == 3:
                body += '''
    while (!dut.commitValid) tick(); interrupts_external = 1;
    check(!redirect, "Completed memory owner must retire before interrupt"); tick();
'''
        else:
            body += '    interrupts_external = 1; #1;\n'
        body += f'''
    for (integer waited = 0; !redirect; waited++) begin
      check(waited < 4, "Interrupt delivery after owner completion"); tick();
    end
    check(status_trap && redirectPc == 'h400 && !instruction_ready && !data_request_valid, "Interrupt entry side effects");
    tick(); interrupts_external = 0;
    check(dut.csr.returnPc == 'h{0x204 if memory else 0x118:x}, "Interrupt architectural resume PC");
    repeat (4) begin check(!redirect, "Repeated entry while globally masked"); tick(); end
'''
    return body


def backend_fence_contract():
    def send(word, pc, tag):
        return f'''    instruction_bits_pc = 'h{pc:x}; instruction_bits_instruction = 'h{word:x};
    instruction_bits_tag = {tag}; instruction_valid = 1;
    while (!instruction_ready) tick(); tick(); instruction_valid = 0;
'''

    body = ''
    for instruction in (False, True):
        body += '''    reset = 1; tick(); reset = 0; tick();
    instruction_bits_length = 4; instruction_bits_fault = 0; instruction_valid = 0;
    data_request_ready = 0; data_response_valid = 0; data_response_bits_fault = 0;
'''
        body += send(addi(1, 0, 0x400), 0x100, 1) + '    repeat (8) tick();\n'
        body += send(addi(2, 0, 19), 0x104, 2) + '    repeat (8) tick();\n'
        body += send(sd(2, 1), 0x108, 3) + send(fence(instruction), 0x10c, 4)
        body += '''    while (!data_request_valid) begin check(!redirect, "Synchronization preceded older store"); tick(); end
    repeat (4) begin check(data_request_valid && !redirect, "Synchronization withdrew blocked store"); tick(); end
    data_request_ready = 1; tick(); data_request_ready = 0;
    repeat (4) begin check(!redirect, "Synchronization preceded store response"); tick(); end
    data_response_bits_tag = 3; data_response_valid = 1; tick(); data_response_valid = 0;
'''
        if instruction:
            body += '''    while (!redirect) tick();
    check(!status_trap && redirectPc == 'h110 && !data_request_valid, "Instruction synchronization restart"); tick();
'''
        body += '    repeat (12) begin check(!redirect && !data_request_valid, "Repeated synchronization effect"); tick(); end\n'
    body += '''    reset = 1; tick(); reset = 0; tick();
    instruction_bits_fault = 1; instruction_bits_cause = 1; instruction_bits_tval = 'h200;
''' + send(fence(True), 0x200, 5) + '''    while (!redirect) tick();
    check(status_trap && redirectPc == 0 && !data_request_valid, "Fault overrides instruction synchronization"); tick();
    instruction_bits_fault = 0; instruction_bits_cause = 0; instruction_bits_tval = 0;
    repeat (8) begin check(!redirect && !data_request_valid, "Faulting synchronization side effects"); tick(); end
'''
    return body


def module_ports(module):
    header = module.read_text().split(');', 1)[0].split('(', 1)[1]
    ports = []
    direction, width = None, ''
    for item in header.split(','):
        match = re.fullmatch(r'\s*(?:(input|output)\s+)?(\[\d+:\d+\])?\s*(\w+)\s*', item)
        assert match, item
        new_direction, new_width, name = match.groups()
        if new_direction:
            direction, width = new_direction, new_width or ''
        ports.append((direction, width, name))
    return ports


def verify_cache_coherence(cache_rtl, fabric_rtl, directory, mutations=False):
    directory.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((cache_rtl / 'ditdah_a1_config.json').read_text())
    parameters = manifest['parameters']
    assert parameters['hartCount'] == 2 and parameters['dCacheWriteback'] and parameters['dCacheRefillBytes'] == 8
    assert manifest['sourceHashes'] == json.loads((fabric_rtl / 'ditdah_a1_config.json').read_text())['sourceHashes']
    modules = dict(DitDahA1DataCache=cache_rtl / 'DitDahA1DataCache.sv', **{
        name: fabric_rtl / (name + '.sv') for name in ('DitDahA1MemoryArbiter', 'DitDahA1Coherence', 'DitDahA1Memory')})
    ports = [('input', '', 'clock'), ('input', '', 'reset')]
    for hart in range(2):
        ports += [(d, w, n.replace('upstream_', f'upstream_{hart}_', 1))
                  for d, w, n in module_ports(modules['DitDahA1DataCache']) if n.startswith('upstream_')]
    ports += [(d, w, n.replace('downstream_', 'physical_', 1))
              for d, w, n in module_ports(modules['DitDahA1Memory']) if n.startswith('downstream_')]
    wires, instances = {}, []

    def instantiate(module, instance, select):
        pins = []
        for direction, width, pin in module_ports(modules[module]):
            signal = pin if pin in ('clock', 'reset') else select(pin, direction)
            if signal and signal not in ('clock', 'reset') and not signal.startswith(('upstream_', 'physical_', "'")):
                assert signal not in wires or wires[signal] == width
                wires[signal] = width
            pins.append(f'.{pin}({signal or ""})')
        instances.append(f'  {module} {instance}(' + ', '.join(pins) + ');')

    for hart in range(2):
        instantiate('DitDahA1DataCache', f'cache_{hart}', lambda pin, direction, h=hart:
                    pin.replace('upstream_', f'upstream_{h}_', 1) if pin.startswith('upstream_') else f'cache_{h}_' + pin)

    def arbiter_pin(pin, direction):
        if pin.startswith('ports_'):
            _, port, channel = pin.split('_', 2)
            if int(port) % 2 == 0:
                return "'0" if direction == 'input' else None
            return f'cache_{int(port)//2}_downstream_' + channel
        return 'arbiter_' + pin

    instantiate('DitDahA1MemoryArbiter', 'arbiter', arbiter_pin)
    instantiate('DitDahA1Coherence', 'coherence', lambda pin, direction:
                'arbiter_hartId' if pin == 'hartId' else pin.replace('upstream_', 'arbiter_downstream_', 1)
                if pin.startswith('upstream_') else 'cache_' + pin[6:].split('_', 1)[0] + '_probe_' + pin[6:].split('_', 1)[1]
                if pin.startswith('probe_') else 'coherence_' + pin)
    instantiate('DitDahA1Memory', 'memory', lambda pin, direction:
                pin.replace('upstream_', 'coherence_downstream_', 1) if pin.startswith('upstream_') else
                pin.replace('downstream_', 'physical_', 1))
    license = '\n'.join(line.replace('#', '//', 1) for line in Path(__file__).read_text().splitlines()[:2]) + '\n'
    wrapper = directory / 'CacheCoherence.sv'
    wrapper.write_text(license + 'module CacheCoherence(\n' + ',\n'.join(f'  {d} {w} {n}' for d, w, n in ports) + '\n);\n' +
                       '\n'.join(f'  wire {w} {n};' for n, w in wires.items()) + '\n' + '\n'.join(instances) + '\nendmodule\n')
    region = next(r for r in parameters['memoryRegions'] if r.get('dataCacheable'))
    base, limit = int(region['base']), int(region['base']) + int(region['size'])
    assert base % 8 == 0 and int(region['size']) >= 2 * parameters['dCacheBytes']
    initial = {base: 0x1122334455667788, base + 8: 0x9988776655443322, base + parameters['dCacheBytes']: 29}
    oracle = {address + b: value >> (8 * b) & 255 for address, value in initial.items() for b in range(8)}
    body = f'''    begin
      reg [7:0] memory [0:{limit-1}];
      integer cycles, reads, writes, failures, failure_budget, delay;
      reg owned, response_fault;
      reg [7:0] response_tag;
      reg [63:0] response_data;
      cycles = 0; reads = 0; writes = 0; failures = 0; failure_budget = 2; delay = 0; owned = 0;
      for (integer b = 0; b < {limit}; b++) memory[b] = 0;
'''
    body += ''.join(f"      memory[{address}] = 8'h{value:x};\n" for address, value in oracle.items())
    body += f'''      fork
        begin
          forever begin
            @(negedge clock);
            physical_request_ready = !owned && cycles % 3 != 0;
            physical_response_valid = owned && delay == 0;
            physical_response_bits_data = response_data; physical_response_bits_fault = response_fault;
            physical_response_bits_tag = response_tag; physical_response_bits_last = 1;
            @(posedge clock); cycles = cycles + 1;
            if (physical_request_valid && physical_request_ready) begin
              if (physical_request_bits_cacheOperation != 0 || physical_request_bits_size > 3 || physical_request_bits_address < {base} ||
                  physical_request_bits_address + (1 << physical_request_bits_size) > {limit}) $fatal(1, "Invalid physical transaction");
              owned = 1; delay = 3; response_data = 0; response_fault = 0; response_tag = physical_request_bits_tag;
              if (physical_request_bits_write) begin
                writes = writes + 1;
                if (failure_budget > 0) begin
                  response_fault = failures % 2 == 0; response_tag = physical_request_bits_tag ^ (failures % 2 == 1);
                  failures = failures + 1; failure_budget = failure_budget - 1;
                end
                for (integer b = 0; b < (1 << physical_request_bits_size); b++)
                  if (physical_request_bits_mask[b] && (!response_fault || b % 2 == 0))
                    memory[physical_request_bits_address + b] = physical_request_bits_data[8*b +: 8];
              end else begin
                reads = reads + 1;
                for (integer b = 0; b < (1 << physical_request_bits_size); b++)
                  response_data[8*b +: 8] = memory[physical_request_bits_address + b];
              end
            end else if (owned && delay > 0) delay = delay - 1;
            if (physical_response_valid && physical_response_ready) owned = 0;
          end
        end
      join_none
'''

    def transfer(hart, address, value=None, size=3):
        write = value is not None
        mask = (1 << (1 << size)) - 1 if write else 0
        expected = 0 if write else sum(oracle.get(address + b, 0) << (8 * b) for b in range(1 << size))
        if write:
            oracle.update((address + b, value >> (8 * b) & 255) for b in range(1 << size))
        return f'''      @(negedge clock);
      upstream_{hart}_request_bits_address = 64'h{address:x}; upstream_{hart}_request_bits_size = {size};
      upstream_{hart}_request_bits_write = {int(write)}; upstream_{hart}_request_bits_data = 64'h{(value or 0):x};
      upstream_{hart}_request_bits_mask = {mask}; upstream_{hart}_request_bits_tag = 37;
      upstream_{hart}_request_valid = 1;
      #1; while (!upstream_{hart}_request_ready) tick(); tick(); upstream_{hart}_request_valid = 0;
      while (!upstream_{hart}_response_valid) tick();
      repeat (3) begin
        check(upstream_{hart}_response_valid && !upstream_{hart}_response_bits_fault && upstream_{hart}_response_bits_tag == 37 && upstream_{hart}_response_bits_last && upstream_{hart}_response_bits_data == 64'h{expected:x}, "Architectural value from actual coherent arrays"); tick();
      end
      upstream_{hart}_response_ready = 1; tick(); upstream_{hart}_response_ready = 0;
'''

    body += transfer(0, base) + transfer(0, base) + transfer(1, base)
    body += transfer(0, base + 2, 0x5678, 1) + transfer(0, base + 7, 0xa5, 0) + transfer(0, base)
    body += '      check(reads == 2 && writes == 0, "Dirty store stays in its owning cache");\n'
    body += transfer(1, base)
    body += '      check(reads == 3 && writes == 3 && failures == 2, "Fault and bad identity retain and retry dirty bytes");\n'
    body += transfer(0, base) + transfer(1, base + 3, 0x12, 0) + transfer(0, base)
    body += transfer(0, base, 0xfedcba9876543210) + transfer(0, base + parameters['dCacheBytes'])
    body += transfer(1, base) + transfer(0, base + parameters['dCacheBytes'])
    body += transfer(1, base + 8) + transfer(1, base, 3, 0) + transfer(1, base + 9, 0x77, 0)
    body += transfer(0, base) + transfer(0, base + 8)
    body += '      check(failures == 2 && writes == 7, "Masked recalls and dirty replacement reach physical memory");\n'
    body += transfer(0, base, 0x1020304050607080)
    body += transfer(1, base + parameters['dCacheBytes']) + transfer(1, base + parameters['dCacheBytes'], 0x8877665544332211)
    body += f'''      begin
        integer accepted, completed;
        accepted = 0; completed = 0; failure_budget = 2;
        @(negedge clock);
        upstream_0_request_bits_address = 64'h{base+parameters['dCacheBytes']:x}; upstream_0_request_bits_tag = 51;
        upstream_1_request_bits_address = 64'h{base:x}; upstream_1_request_bits_tag = 52;
        upstream_0_request_bits_write = 0; upstream_1_request_bits_write = 0;
        upstream_0_request_bits_size = 3; upstream_1_request_bits_size = 3;
        upstream_0_request_valid = 1; upstream_1_request_valid = 1;
        upstream_0_response_ready = 1; upstream_1_response_ready = 1;
        while (completed != 3) begin
          #1;
          if (upstream_0_request_valid && upstream_0_request_ready) accepted = accepted | 1;
          if (upstream_1_request_valid && upstream_1_request_ready) accepted = accepted | 2;
          if (upstream_0_response_valid) begin
            check(!upstream_0_response_bits_fault && upstream_0_response_bits_tag == 51 && upstream_0_response_bits_data == 64'h8877665544332211, "First simultaneous dirty replacement reads latest peer data");
            completed = completed | 1;
          end
          if (upstream_1_response_valid) begin
            check(!upstream_1_response_bits_fault && upstream_1_response_bits_tag == 52 && upstream_1_response_bits_data == 64'h1020304050607080, "Second simultaneous dirty replacement reads latest peer data");
            completed = completed | 2;
          end
          tick(); upstream_0_request_valid = !(accepted & 1); upstream_1_request_valid = !(accepted & 2);
          @(negedge clock);
        end
        upstream_0_response_ready = 0; upstream_1_response_ready = 0;
      end
      check(failures == 4 && writes == 11, "Concurrent release retains dirty data across injected errors");
      $display("COHERENCE reads=%0d writes=%0d failures=%0d", reads, writes, failures);
    end
'''
    test = directory / 'CacheCoherence_tb.sv'
    test.write_text(bench(wrapper, body))
    files = [*modules.values(), *(cache_rtl / f for f in (cache_rtl / 'filelist.f').read_text().splitlines()
                                  if f.startswith(('data_', 'dataTags_', 'dataDirty_', 'mem_'))), wrapper, test]
    binary = directory / 'CacheCoherence'
    subprocess.run(['iverilog', '-g2012', '-s', 'contract_tb', '-o', str(binary), *map(str, files)], check=True)
    result = subprocess.run(['vvp', str(binary)], capture_output=True, text=True, timeout=30)
    (directory / 'CacheCoherence.log').write_text(result.stdout + result.stderr)
    assert result.returncode == 0 and 'PASS' in result.stdout, result.stdout + result.stderr
    negative = []
    if mutations:
        original = modules['DitDahA1DataCache'].read_text()
        mask = re.search(r'assign probe_response_bits_mask\s*=[^;]+;', original).group()
        word = re.search(r'assign probe_response_bits_word\s*=[^;]+;', original).group()
        for name, before, after in (
                ('mask-accumulation', 'storedDirty | accessMask[7:0]', 'accessMask[7:0]'),
                ('probe-mask', mask, 'assign probe_response_bits_mask = 0;'),
                ('probe-word', word, 'assign probe_response_bits_word = 0;')):
            assert original.count(before) == (parameters.get('dCacheWays', 1) if name == 'mask-accumulation' else 1)
            work = directory / ('mutation-' + name)
            work.mkdir(exist_ok=True)
            changed = work / 'DitDahA1DataCache.sv'
            changed.write_text(original.replace(before, after))
            binary = work / 'CacheCoherence'
            subprocess.run(['iverilog', '-g2012', '-s', 'contract_tb', '-o', str(binary),
                            *map(str, [changed, *files[1:]])], check=True)
            result = subprocess.run(['vvp', str(binary)], capture_output=True, text=True, timeout=30)
            (work / 'simulation.log').write_text(result.stdout + result.stderr)
            assert result.returncode != 0 and 'Architectural value from actual coherent arrays' in result.stdout, result.stdout + result.stderr
            negative.append(dict(name=name, status='FAIL_FUNCTIONAL_VALUE', log=str(work / 'simulation.log')))
    (directory / 'summary.json').write_text(json.dumps(dict(scope='two real caches, shared arbiter, coherence and physical protection',
        checkerHash=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        inputHashes={str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        physicalFailures=4, physicalWrites=11, negativeControls=negative), indent=2) + '\n')
    print('  Two-cache dirty ownership, masked recall, failed writeback and replacement passed', flush=True)


def bench(module, body, cycle_limit=10000):
    declarations, connections, names = [], [], []
    for direction, width, name in module_ports(module):
        initial = (" = 3" if name == 'privilege' else " = 1" if name == 'wfiLegal' or name.endswith(('_privileged', '_response_bits_last')) else " = '0") if direction == 'input' else ''
        declarations.append(f'  logic {width} {name}{initial};')
        connections.append(f'.{name}({name})')
        names.append(name)
    header = '\n'.join(line.replace('#', '//', 1) for line in Path(__file__).read_text().splitlines()[:2])
    return (header + '\n`timescale 1ns/1ps\nmodule contract_tb;\n'
            + '`define CHECK(ok, message) #1; if ((ok) !== 1\'b1) $fatal(1, \"%s\", message)\n'
            + '\n'.join(declarations) + '\n  ' + module.stem + ' dut(' + ', '.join(connections) + ');\n'
            + ('''  always #5 clock = ~clock;
  task tick;
    @(posedge clock); #1;
  endtask
''' if 'clock' in names else '')
            + '''
  initial begin
''' + ('    reset = 1; tick(); tick(); reset = 0; tick();\n' if 'reset' in names else '')
            + body.replace('check(', '`CHECK(') + '''
    $display("PASS"); $finish;
  end
  initial begin #''' + str(cycle_limit * 10) + '''; $fatal(1, "Timeout"); end
endmodule
''')


def pmp_contract(parameters):
    pa = parameters['physicalAddressBits']
    width = pa - 2
    rng = random.Random(2026)
    tests = []
    for index in (0, 7, 8, 15):
        for config in (0, 8, 16, 24, 128, 136, 144, 152, 153, 154, 156, 159):
            for address in (0xffc, 0x1000, 0x1004, 0x1008, (1 << pa) - 4, (1 << 64) - 4):
                configs, addresses = [0] * 16, [0] * 16
                configs[index], addresses[index] = config, 0x401
                if index:
                    addresses[index - 1] = 0x400
                tests.append((configs, addresses, address, 3, 'read'))
                tests.append((configs, addresses, address, 3, 'atomic'))
    if parameters.get('enableBurstRefill'):
        for address in (0xfc0, 0xffc, 0x1000, 0x103c, (1 << pa) - 64, (1 << pa) - 32, (1 << 64) - 32):
            for config in (0, 0x9c, 0x98, 0x94, 0x8c):
                tests.append(([config] + [0x9f] + [0] * 14, [0x407, (1 << width) - 1] + [0] * 14, address, 6, 'fetch'))
    for address in (0xfc0, 0xffc, 0x1000, 0x103c, (1 << pa) - 64, (1 << pa) - 32):
        for config in (0, 0x99, 0x98, 0x94, 0x89):
            for kind in ('read', 'write', 'atomic'):
                tests.append(([config, 0x9f] + [0] * 14, [0x407, (1 << width) - 1] + [0] * 14, address, 6, kind))
    block = bool(parameters.get('iCacheBytes')) and parameters['issueWidth'] == 3
    for address in (0xff4, 0xffc, 0x1000, 0x1004, 0x100c, (1 << pa) - 16, (1 << pa) - 4, (1 << 64) - 4):
        for config in (0, 0x9f, 0x9c, 0x98, 0x94, 0x8c):
            for kind in ('fetch', 'read', 'write', 'atomic'):
                tests.append(([config, 0x9f] + [0] * 14, [0x401, (1 << width) - 1] + [0] * 14, address, 4, kind))
    for _ in range(320):
        configs = [rng.randrange(256) & 0x9f for _ in range(16)]
        addresses = [rng.choice((0, 0x400 + rng.randrange(16), (1 << width) - 1)) for _ in range(16)]
        tests.append((configs, addresses, rng.choice((0, 0x1000 + rng.randrange(64), (1 << pa) - 8)),
                      rng.randrange(8), rng.choice(('fetch', 'read', 'write', 'atomic'))))
    body = ''
    for configs, addresses, address, size, kind in tests:
        config = sum(v << (i * 8) for i, v in enumerate(configs))
        points = sum(v << (i * width) for i, v in enumerate(addresses))
        kinds = ('read', 'write') if kind == 'atomic' else (kind,)
        for privilege in ((0, 1, 3) if parameters.get('enableSupervisorMode') else (0, 3) if parameters.get('enableUserMode') else (3,)):
            supported = (size <= 3 or kind == 'fetch' and (size == 4 and block or size == 6 and parameters.get('enableBurstRefill')) or
                         size == 6 and kind == 'read' and parameters.get('dCacheRefillBytes') == 64)
            expected = int(bool(supported) and all(pmp_allowed(configs, addresses, address, 1 << size, access, pa, privilege) for access in kinds))
            body += f'''    state_config = 128'h{config:x}; state_address = {16 * width}'h{points:x}; privilege = {privilege};
    address = 64'h{address:x}; size = {size}; fetch = {int(kind == 'fetch')}; write = {int(kind in ('write', 'atomic'))}; atomic = {int(kind == 'atomic')};
    check(allowed == {expected}, "PMP priority, range and permissions");
'''
    return body


def csr_contract(parameters):
    model = Model(parameters, {}, {})
    body = ''

    def access(address, value=0, write=False):
        nonlocal body
        legal = int(address in model.csrs)
        body += f'''    readAddress = 12'h{address:x}; writeAddress = 12'h{address:x}; writeData = 64'h{value:x}; write = 0;
    check(legal == {legal} && readData == 64'h{model.csrs.get(address, 0):x}, "CSR read and legality");
'''
        if write:
            assert legal
            model.write_csr(address, value)
            body += f'''    write = 1; tick(); write = 0;
    check(readData == 64'h{model.csrs[address]:x}, "PMP CSR WARL and locking");
'''
        configs = sum(model.pmp_config(i) << (i * 8) for i in range(16))
        addresses = sum(model.csrs[0x3b0 + i] << (i * (parameters['physicalAddressBits'] - 2)) for i in range(16))
        body += f'    check(pmp_config == 128\'h{configs:x} && pmp_address == {16 * (parameters["physicalAddressBits"] - 2)}\'h{addresses:x}, "PMP state distribution");\n'

    for index in range(16):
        access(0x3b0 + index, ((1 << 64) - 1) ^ (index * 8), True)
    for address in (0x3a0, 0x3a2):
        access(address, 0x6262626262626262, True)
    for address in (*range(0x3a1, 0x3b0, 2), 0x3a4, 0x3ef):
        access(address)
    access(0x3a4, (1 << 64) - 1, True)
    access(0x3ef, (1 << 64) - 1, True)
    access(0x3a0, 0x8900, True)
    access(0x3b0, 0, True)
    access(0x3b1, 0, True)
    access(0x3a0, 0x80, True)
    access(0x3b0, 0, True)
    access(0x3a0, 0, True)
    access(0x3a2, 0x8900000000000000, True)
    access(0x3be, 0, True)
    access(0x3bf, 0, True)
    body += '    reset = 1; tick(); reset = 0; tick();\n'
    model = Model(parameters, {}, {})
    access(0x3a0)
    access(0x3b0, 0x401, True)
    return body


def interrupt_csr_contract(parameters):
    body = '    reset = 1; tick(); reset = 0; tick();\n'
    model = Model(parameters, {}, {})
    for enabled in range(8):
        mask = sum(((enabled >> i) & 1) << bit for i, bit in enumerate((3, 7, 11)))
        body += f"    write = 1; writeAddress = 'h304; writeData = 64'h{mask | 0xfffffffffffff777:x}; tick(); write = 0; readAddress = 'h304;\n    check(readData == 'h{mask:x}, \"Interrupt enable WARL\");\n"
        model.write_csr(0x304, mask)
        for global_enable in (0, 8):
            model.write_csr(0x300, global_enable)
            body += f"    write = 1; writeAddress = 'h300; writeData = {global_enable}; tick(); write = 0;\n"
            for levels in range(8):
                model.set_interrupts(levels)
                cause = model.interrupt_cause()
                body += f"    interrupts_software = {levels & 1}; interrupts_timer = {(levels >> 1) & 1}; interrupts_external = {levels >> 2}; readAddress = 'h344;\n"
                body += f"    check(readData == 'h{model.csrs[0x344]:x} && interruptPending == {int(bool(cause))}, \"Interrupt levels and eligibility\");\n"
                if cause:
                    body += f"    check(interruptCause == 64'h{cause:x}, \"Interrupt priority\");\n"
                body += f"    write = 1; writeAddress = 'h344; writeData = 0; tick(); write = 0;\n    check(readData == 'h{model.csrs[0x344]:x}, \"Read-only pending levels\");\n"
    return body + f'''
    trap = 1; trapPc = 'h123; trapCause = 64'h800000000000000b; trapValue = 0; tick(); trap = 0;
    readAddress = 'h300; check(readData == 'h{(2 << 32 if parameters.get('enableUserMode') else 0) | 0x1880:x} && !interruptPending, "Entry masks interrupts");
    readAddress = 'h341; check(readData == 'h{0x122 if parameters.get('enableC') else 0x120:x}, "Trap PC alignment");
    readAddress = 'h342; check(readData == 64'h800000000000000b, "Interrupt cause flag");
    readAddress = 'h343; check(readData == 0, "Interrupt trap value");
    mret = 1; tick(); mret = 0; readAddress = 'h300;
    check(readData == 'h{(2 << 32 if parameters.get('enableUserMode') else 0x1800) | 0x88:x} && interruptPending, "Return reevaluates held sources");
    interrupts_software = 0; interrupts_timer = 0; interrupts_external = 0;
    check(!interruptPending, "Source deassertion");
'''


def user_csr_contract(parameters):
    base = int(parameters['resetVector'])
    model = Model(parameters, {base + i: (0x30200073 >> (8 * i)) & 255 for i in range(4)}, {})
    body = '    reset = 1; tick(); reset = 0; tick();\n'

    def state():
        nonlocal body
        body += f'''    readAddress = 'h300;
    check(privilege == {model.privilege} && dataPrivilege == {model.data_privilege()} && wfiLegal == {int(model.privilege == 3 or not model.csrs[0x300] & (1 << 21))}, "Effective execution privilege");
    check(legal == {int(model.privilege == 3)}, "Machine CSR privilege");
'''
        if model.privilege == 3:
            body += f'    check(readData == 64\'h{model.csrs[0x300]:x}, "Privilege status WARL and trap stack");\n'
        if parameters['enableInterrupts']:
            body += f'    check(interruptPending == {int(bool(model.interrupt_cause()))}, "Higher privilege interrupt eligibility");\n'

    state()
    for address in (0x306, 0x30a):
        body += f"    @(negedge clock); readAddress = 'h{address:x}; writeAddress = 'h{address:x}; writeData = '1; write = 1; tick(); write = 0; check(legal && readData == 0, \"Environment CSR WARL zero\");\n"
    for previous in range(4):
        value = (previous << 11) | (1 << 17) | (1 << 21) | 0x88
        model.write_csr(0x300, value)
        body += f"    @(negedge clock); write = 1; writeAddress = 'h300; writeData = 'h{value:x}; tick(); write = 0;\n"
        state()
        model.pc = base
        model.step()
        body += '    @(negedge clock); mret = 1; tick(); mret = 0;\n'
        state()
        for address in (0x300, 0x306, 0x30a, 0x340, 0xf14, 0xf15, 0x180):
            body += f"    readAddress = 'h{address:x}; check(legal == {int(model.privilege == 3 and address in model.csrs)}, \"CSR minimum privilege\");\n"
        model.trap(0x123, 8, 0)
        body += "    @(negedge clock); trap = 1; trapPc = 'h123; trapCause = 8; trapValue = 0; tick(); trap = 0;\n"
        state()
    if parameters['enableInterrupts']:
        for index, bit in enumerate((3, 7, 11)):
            model.write_csr(0x304, 1 << bit)
            model.write_csr(0x300, 0)
            model.set_interrupts(1 << index)
            body += f"    @(negedge clock); write = 1; writeAddress = 'h304; writeData = 'h{1 << bit:x}; tick(); writeAddress = 'h300; writeData = 0; tick(); write = 0;\n"
            body += f'    interrupts_software = {int(index == 0)}; interrupts_timer = {int(index == 1)}; interrupts_external = {int(index == 2)};\n'
            state()
            model.pc = base
            model.step()
            body += '    @(negedge clock); mret = 1; tick(); mret = 0;\n'
            state()
            model.trap(0x123, (1 << 63) | bit, 0)
            body += f"    @(negedge clock); trap = 1; trapPc = 'h123; trapCause = 64'h{(1 << 63) | bit:x}; tick(); trap = 0;\n"
            state()
    return body


def supervisor_csr_contract(parameters):
    model = Model(parameters, {}, {})
    body = '    reset = 1; tick(); reset = 0; tick();\n'

    def state():
        nonlocal body
        status = model.csrs[0x300]
        body += f'''    check(privilege == {model.privilege} && dataPrivilege == {model.data_privilege()}, "Execution and effective data mode");
    check(wfiLegal == {int(model.privilege == 3 or model.privilege == 1 and not status & (1 << 21))} && sretLegal == {int(model.privilege == 3 or model.privilege == 1 and not status & (1 << 22))}, "Privileged instruction controls");
    check(interruptPending == {int(bool(model.interrupt_cause()))} && wakeup == {int(bool(model.csrs[0x304] & model.csrs[0x344]))}, "Delegated interrupt eligibility");
'''
        if model.interrupt_cause():
            body += f'    check(interruptCause == 64\'h{model.interrupt_cause():x}, "Target privilege precedes interrupt source priority");\n'
        body += f'    check(sfenceLegal == {int(parameters.get("virtualAddressBits") == 39 and (model.privilege == 3 or model.privilege == 1 and not status & (1 << 20)))}, "SFENCE minimum privilege and TVM");\n'
        for address in (0x100, 0x104, 0x105, 0x106, 0x10a, 0x140, 0x141, 0x142, 0x143, 0x144,
                        0x180, 0x300, 0x302, 0x303, 0x304, 0x305, 0x340, 0x341, 0x342, 0x343, 0x344):
            legal = model.csr_legal(address)
            body += f"    readAddress = 'h{address:x}; check(legal == {int(legal)}"
            body += (f" && readData == 64'h{model.read_csr(address):x}" if legal else '') + ', "CSR privilege, aliases and trap bank");\n'

    def write(address, value):
        nonlocal body
        model.write_csr(address, value)
        body += f"    @(negedge clock); write = 1; writeAddress = 'h{address:x}; writeData = 64'h{value:x}; tick(); write = 0;\n"

    def trap(cause, pc=0x123, value=0x456):
        nonlocal body
        target = model.trap(pc, cause, value)
        body += f"    @(negedge clock); trap = 1; trapPc = 'h{pc:x}; trapCause = 64'h{cause:x}; trapValue = 'h{value:x};\n"
        body += f"    check(trapVector == 'h{target:x}, \"Execution mode selects trap target\"); tick(); trap = 0;\n"
        state()

    def ret(supervisor=False):
        nonlocal body
        pc = model.return_from_trap(supervisor)
        signal = 'sret' if supervisor else 'mret'
        body += f"    @(negedge clock); {signal} = 1; check(returnPc == 'h{pc:x}, \"Return selects its own trap bank\"); tick(); {signal} = 0;\n"
        state()

    state()
    for address, value in ((0x302, MASK), (0x303, MASK), (0x300, MASK), (0x100, MASK),
                           (0x105, 0x203), (0x305, 0x803), (0x141, 0x347), (0x341, 0x567),
                           (0x106, MASK), (0x10a, MASK), (0x180, MASK), (0x140, 0x1234),
                           (0x304, MASK), (0x104, 0), (0x344, MASK), (0x144, 0)):
        write(address, value)
        state()
    write(0x304, 0)
    write(0x344, 0)
    for previous in (0, 1, 2, 3):
        write(0x300, (previous << 11) | 0x2201aa)
        ret()
        trap(8)
        if model.privilege == 1:
            ret(True)
        trap(11)
    for mode in (0, 1, 3):
        for delegated in (0, 0x222):
            for global_enable in (0, 2):
                write(0x303, delegated)
                write(0x304, 0xaaa)
                write(0x344, 0x222)
                write(0x300, (mode << 11) | global_enable)
                ret()
                for levels in (0, 1, 2, 4, 7):
                    model.set_interrupts(levels)
                    body += f'    interrupts_software = {levels & 1}; interrupts_timer = {(levels >> 1) & 1}; interrupts_external = {levels >> 2};\n'
                    state()
                if model.interrupt_cause():
                    trap(model.interrupt_cause(), value=0)
                trap(11)
                model.set_interrupts(0)
                body += '    interrupts_software = 0; interrupts_timer = 0; interrupts_external = 0;\n'
    write(0x304, 0)
    write(0x344, 0)
    for control in (1 << 20, 1 << 21, 1 << 22):
        write(0x300, 0x800 | control)
        ret()
        trap(11)
    write(0x300, 0x20800)
    trap(5)
    if parameters.get('virtualAddressBits') == 39:
        root = int(parameters['resetVector']) + 0x1000
        for value in ((8 << 60) | root >> 12, (9 << 60) | root >> 12,
                      (8 << 60) | (0xffff << 44) | root >> 12, 0):
            write(0x180, value)
            state()
        write(0x300, 0xc0000)
        state()
        write(0x100, 0)
        state()
    return body


def translation_contract(parameters):
    base, pa = int(parameters['resetVector']), parameters['physicalAddressBits']
    root, middle, bottom = base + 0x1000, base + 0x2000, base + 0x3000
    body = '    reset = 1; tick(); reset = 0; tick();\n'
    cached = [bool(parameters.get('tlbEntries') or parameters.get(key)) for key in ('iTlbEntries', 'dTlbEntries')]
    flush = '    invalidate = 1; tick(); invalidate = 0; tick();\n' if any(cached) else ''
    if parameters['pmpEntries']:
        body += f"    pmp_config = 'h1f; pmp_address = 'h{(1 << (pa - 2)) - 1:x};\n"
    vectors = []
    for level in (0, 1, 2):
        for kind in ('fetch', 'read', 'write'):
            for privilege in (0, 1, 3):
                for flags, status in ((0xcf, 0), (0xdf, 0), (0xdf, 1 << 18), (0xc9, 0), (0xc9, 1 << 19), (0x4f, 0), (0x8f, 0)):
                    vectors.append((level, kind, privilege, flags, status, 0x12345100, None))
    for bad in (0, 1, 0xc5, 0xce, (1 << 54) | 0xcf, (1 << 63) | 0xcf, 0x100000000000cf):
        vectors.append((0, 'read', 1, bad, 0, 0x12345100, None))
    for level in (1, 2):
        vectors.append((level, 'read', 1, 0x4cf, 0, 0x12345100, None))
    for address in (1 << 39, (1 << 38) - 8, MASK - 7):
        vectors.append((0, 'read', 1, 0xcf, 0, address, None))
    for nonleaf in (0x11, 0x41, 0x81):
        vectors.append((0, 'read', 1, 0xcf, 0, 0x12345100, nonleaf))
    for index, (level, kind, privilege, flags, status, address, nonleaf) in enumerate(vectors):
        vpn = [(address >> (12 + 9 * i)) & 511 for i in range(3)]
        entries = {root + vpn[2] * 8: ((middle >> 12) << 10) | (nonleaf or 1),
                   middle + vpn[1] * 8: ((bottom >> 12) << 10) | 1,
                   bottom + vpn[0] * 8: ((base >> 12) << 10) | flags}
        entries[(root, middle, bottom)[2 - level] + vpn[level] * 8] = ((base >> 12) << 10) | flags
        reads = []
        def read_pte(physical):
            reads.append((physical, entries.get(physical, 0)))
            return entries.get(physical, 0)
        fault, cause, physical = False, 0, address
        try:
            physical = sv39_walk(address, kind, privilege, (8 << 60) | root >> 12, status, read_pte)
        except Fault as error:
            fault, cause = True, error.cause
        port = index % 2
        body += flush
        body += f'''    state_satp = 64'h{(8 << 60) | root >> 12:x}; state_sum = {int(bool(status & (1 << 18)))}; state_mxr = {int(bool(status & (1 << 19)))};
    ports_{port}_request_bits_address = 64'h{address:x}; ports_{port}_request_bits_privilege = {privilege};
    ports_{port}_request_bits_fetch = {int(kind == 'fetch')}; ports_{port}_request_bits_write = {int(kind == 'write')};
    ports_{port}_request_valid = 1; #1; while (!ports_{port}_request_ready) tick(); tick(); ports_{port}_request_valid = 0;
    state_satp = 0; state_sum = !state_sum; state_mxr = !state_mxr; ports_{port}_request_bits_address = '1;
'''
        for pte_address, pte in reads:
            body += f'''    while (!memory_request_valid) tick();
    repeat (2) begin
      check(memory_request_bits_address == 64'h{pte_address:x} && memory_request_bits_size == 3 && memory_request_bits_data == 0 && memory_request_bits_mask == 0 && memory_request_bits_tag == 0 && memory_request_bits_privileged && !memory_request_bits_fetch && !memory_request_bits_write && !memory_request_bits_atomic, "PTE identity and ordinary S read"); tick();
    end
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_data = 64'h{pte:x}; memory_response_bits_tag = 0; memory_response_valid = 1;
    check(memory_response_ready, "PTE response owner"); tick(); memory_response_valid = 0;
'''
        body += f'''    while (!ports_{port}_response_valid) tick();
    repeat (2) begin
      check(!ports_{1-port}_response_valid && ports_{port}_response_bits_fault == {int(fault)} && ports_{port}_response_bits_cause == {cause} && ports_{port}_response_bits_address == 64'h{physical:x} && !memory_request_valid, "Independent page walk and retained response"); tick();
    end
    ports_{port}_response_ready = 1; tick(); ports_{port}_response_ready = 0;
'''
        if cached[port] and reads and not fault:
            hit_address = address + (8 if address <= MASK - 15 and address % 4096 < 4088 else 0)
            for hit_kind, hit_privilege, hit_status in ((kind, privilege, status), ('write', privilege, status),
                    ('read', privilege, status ^ (1 << 19)), (kind, 1 - privilege, status ^ (1 << 18))):
                hit_fault, hit_cause, hit_physical = False, 0, hit_address
                try:
                    hit_physical = sv39_walk(hit_address, hit_kind, hit_privilege, (8 << 60) | root >> 12, hit_status, lambda physical: entries.get(physical, 0))
                except Fault as error:
                    hit_fault, hit_cause = True, error.cause
                body += f'''    state_satp = 64'h{(8 << 60) | root >> 12:x}; state_sum = {int(bool(hit_status & (1 << 18)))}; state_mxr = {int(bool(hit_status & (1 << 19)))};
    ports_{port}_request_bits_address = 64'h{hit_address:x}; ports_{port}_request_bits_privilege = {hit_privilege};
    ports_{port}_request_bits_fetch = {int(hit_kind == 'fetch')}; ports_{port}_request_bits_write = {int(hit_kind == 'write')};
    ports_{port}_request_valid = 1; #1; while (!ports_{port}_request_ready) tick(); tick(); ports_{port}_request_valid = 0;
    while (!ports_{port}_response_valid) begin check(!memory_request_valid, "Warm translation repeated page-table service"); tick(); end
    repeat (2) begin
      check(!memory_request_valid && ports_{port}_response_bits_fault == {int(hit_fault)} && ports_{port}_response_bits_cause == {hit_cause} && ports_{port}_response_bits_address == 64'h{hit_physical:x}, "Cached page size, offset and current permissions"); tick();
    end
    ports_{port}_response_ready = 1; tick(); ports_{port}_response_ready = 0;
'''
    body += f'''    state_satp = 64'h{(8 << 60) | root >> 12:x}; ports_0_request_bits_address = 0; ports_0_request_bits_privilege = 1; ports_0_request_bits_fetch = 1; ports_0_request_valid = 1;
    #1; while (!ports_0_request_ready) tick(); tick(); ports_0_request_valid = 0;
    while (!memory_request_valid) tick(); cancelInstruction = 1; tick(); cancelInstruction = 0;
    check(memory_request_valid, "Cancellation withdrew PTE request"); memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_data = 64'h{((middle >> 12) << 10) | 1:x}; memory_response_valid = 1; tick(); memory_response_valid = 0;
    while (!ports_0_response_valid) tick();
    check(!memory_request_valid && !ports_0_response_bits_fault, "Cancelled walk continued or published a fault");
    ports_0_response_ready = 1; tick(); ports_0_response_ready = 0;
'''
    for fault, tag in ((1, 0), (0, 1)):
        body += f'''    ports_1_request_bits_address = 'h100; ports_1_request_bits_privilege = 1; ports_1_request_bits_fetch = 0; ports_1_request_bits_write = 1;
    ports_1_request_valid = 1; #1; while (!ports_1_request_ready) tick(); tick(); ports_1_request_valid = 0;
    while (!memory_request_valid) tick(); memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_data = '1; memory_response_bits_fault = {fault}; memory_response_bits_tag = {tag}; memory_response_valid = 1;
    tick(); memory_response_valid = 0; memory_response_bits_fault = 0; memory_response_bits_tag = 0;
    while (!ports_1_response_valid) tick();
    check(ports_1_response_bits_fault && ports_1_response_bits_cause == 7 && ports_1_response_bits_address == 'h100 && !memory_request_valid, "PTE transport errors retain original store attribution");
    ports_1_response_ready = 1; tick(); ports_1_response_ready = 0;
'''
    denied = [int(r['base']) for r in parameters['memoryRegions'] if r['device']]
    if pa < 56:
        denied.append(1 << pa)
    if parameters['pmpEntries']:
        denied.append(root)
    for physical in denied:
        if physical == root:
            body += '    pmp_config = 0; pmp_address = 0;\n'
        body += f'''    state_satp = 64'h{(8 << 60) | physical >> 12:x}; ports_1_request_bits_write = 0;
    ports_1_request_valid = 1; #1; while (!ports_1_request_ready) tick(); tick(); ports_1_request_valid = 0;
    while (!ports_1_response_valid) begin check(!memory_request_valid, "Denied PTE was offered to physical memory"); tick(); end
    check(ports_1_response_bits_fault && ports_1_response_bits_cause == 5 && ports_1_response_bits_address == 'h100, "PTE physical authorization uses S privilege");
    ports_1_response_ready = 1; tick(); ports_1_response_ready = 0;
'''
    if any(cached):
        for walking in range(2):
            hit = 1 - walking
            if not cached[hit]:
                continue
            body += '    reset = 1; tick(); reset = 0; tick();\n'
            if parameters['pmpEntries']:
                body += f"    pmp_config = 'h1f; pmp_address = 'h{(1 << (pa - 2)) - 1:x};\n"
            body += f'''    state_satp = 64'h{(8 << 60) | root >> 12:x}; state_sum = 0; state_mxr = 0;
    ports_{hit}_request_bits_address = 'h100; ports_{hit}_request_bits_privilege = 1;
    ports_{hit}_request_bits_fetch = {int(hit == 0)}; ports_{hit}_request_bits_write = 0; ports_{hit}_request_valid = 1;
    #1; while (!ports_{hit}_request_ready) tick(); tick(); ports_{hit}_request_valid = 0;
    while (!memory_request_valid) tick(); memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_data = 64'h{((base >> 12) << 10) | 0xcf:x}; memory_response_valid = 1;
    tick(); memory_response_valid = 0; ports_{hit}_response_ready = 1;
    while (!ports_{hit}_response_valid) tick(); tick(); ports_{hit}_response_ready = 0;
    ports_{walking}_request_bits_address = 'h40000100; ports_{walking}_request_bits_privilege = 1;
    ports_{walking}_request_bits_fetch = {int(walking == 0)}; ports_{walking}_request_bits_write = 0; ports_{walking}_request_valid = 1;
    #1; while (!ports_{walking}_request_ready) tick(); tick(); ports_{walking}_request_valid = 0;
    while (!memory_request_valid) tick();
    ports_{hit}_request_bits_address = 'h104; ports_{hit}_request_valid = 1; ports_{hit}_response_ready = 1;
    #1; check(ports_{hit}_request_ready && ports_{hit}_response_valid &&
      !ports_{hit}_response_bits_fault && ports_{hit}_response_bits_address == 'h{base+0x104:x} &&
      memory_request_valid && memory_request_bits_address == 'h{root+8:x},
      "Hit service overlaps the other client's stalled walk");
    tick(); ports_{hit}_request_valid = 0; ports_{hit}_response_ready = 0;
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    invalidate = 1; tick(); invalidate = 0;
    memory_response_bits_data = 64'h{((base >> 12) << 10) | 0xcf:x}; memory_response_valid = 1;
    tick(); memory_response_valid = 0; ports_{walking}_response_ready = 1;
    while (!ports_{walking}_response_valid) tick();
    check(!ports_{walking}_response_bits_fault && ports_{walking}_response_bits_address == 'h{base+0x100:x},
      "Concurrent hit preserves the walk context");
    tick(); ports_{walking}_response_ready = 0; ports_{walking}_request_valid = 1;
    #1; while (!ports_{walking}_request_ready) tick(); tick(); ports_{walking}_request_valid = 0;
    while (!memory_request_valid) begin check(!ports_{walking}_response_valid, "Invalidated walk refilled a translation"); tick(); end
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_valid = 1; tick(); memory_response_valid = 0; ports_{walking}_response_ready = 1;
    while (!ports_{walking}_response_valid) tick(); tick(); ports_{walking}_response_ready = 0;
'''
    if parameters.get('tlbEntries'):
        for target, key in enumerate(('iTlbEntries', 'dTlbEntries')):
            if not parameters.get(key):
                continue
            body += '''    reset = 1; tick(); reset = 0; tick();
    ports_0_request_valid = 0; ports_1_request_valid = 0; cancelInstruction = 0; invalidate = 0;
    ports_0_response_ready = 0; ports_1_response_ready = 0;
    memory_request_ready = 0; memory_response_valid = 0; memory_response_bits_fault = 0; memory_response_bits_tag = 0;
'''
            if parameters['pmpEntries']:
                body += f"    pmp_config = 'h1f; pmp_address = 'h{(1 << (pa - 2)) - 1:x};\n"
            body += f"    state_satp = 64'h{(8 << 60) | root >> 12:x}; state_sum = 0; state_mxr = 0;\n"
            def demand(port, virtual, miss):
                nonlocal body
                body += f'''    ports_{port}_request_bits_address = 64'h{virtual:x}; ports_{port}_request_bits_privilege = 1;
    ports_{port}_request_bits_fetch = {int(port == 0)}; ports_{port}_request_bits_write = 0; ports_{port}_request_valid = 1;
    #1; while (!ports_{port}_request_ready) tick(); tick(); ports_{port}_request_valid = 0;
'''
                if miss:
                    body += f'''    while (!memory_request_valid) begin check(!ports_{port}_response_valid, "Cold translation needs its walk"); tick(); end
    check(memory_request_bits_address == 'h{root + (virtual >> 30) * 8:x}, "Replacement walk uses independent root index");
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_data = 64'h{((base >> 12) << 10) | 0xcf:x}; memory_response_valid = 1;
    tick(); memory_response_valid = 0;
'''
                body += f'''    while (!ports_{port}_response_valid) begin check(!memory_request_valid, "Promoted translation survives shared replacement"); tick(); end
    check(!memory_request_valid && !ports_{port}_response_bits_fault && ports_{port}_response_bits_address == 'h{base + (virtual & ((1 << 30) - 1)):x}, "Local translation retains its leaf bytes");
    ports_{port}_response_ready = 1; tick(); ports_{port}_response_ready = 0;
'''
            demand(1 - target, 0x100, True)
            demand(target, 0x100, False)
            for page in range(1, parameters['tlbEntries'] + 1):
                demand(1 - target, (page << 30) | 0x100, True)
            demand(target, 0x100, False)
    body += '''    state_satp = 0; ports_0_request_bits_address = 'h40; ports_0_request_bits_fetch = 1;
    ports_1_request_bits_address = 'h80; ports_0_request_valid = 1; ports_1_request_valid = 1;
    ports_0_response_ready = 1; ports_1_response_ready = 1;
    #1; check(ports_0_request_ready && ports_1_request_ready && ports_0_response_valid && ports_1_response_valid &&
      ports_0_response_bits_address == 'h40 && ports_1_response_bits_address == 'h80 && !memory_request_valid,
      "Independent simultaneous Bare translations");
    tick(); ports_0_response_ready = 0; ports_1_response_ready = 0;
    tick(); ports_0_request_valid = 0; ports_1_request_valid = 0; state_satp = '1; cancelInstruction = 1;
'''
    body += '    invalidate = 1;\n' if any(cached) else ''
    body += '''    repeat (3) begin
      check(ports_0_response_valid && ports_1_response_valid && ports_0_response_bits_address == 'h40 &&
        ports_1_response_bits_address == 'h80 && !ports_0_response_bits_fault && !ports_1_response_bits_fault &&
        !ports_0_request_ready && !ports_1_request_ready, "Accepted responses survive context change and cancellation"); tick();
    end
    ports_0_response_ready = 1; ports_1_response_ready = 1; tick(); cancelInstruction = 0;
'''
    body += '    invalidate = 0;\n' if any(cached) else ''
    return body


def translation_context_contract(parameters):
    if parameters.get('asidBits') != 4 or parameters.get('tlbEntries') != 4:
        return ''
    base, root = int(parameters['resetVector']), int(parameters['resetVector']) + 0x1000
    body = ['    reset = 1; tick(); reset = 0; ports_0_request_valid = 0; ports_1_request_valid = 0;\n',
            '    ports_0_response_ready = 0; ports_1_response_ready = 0; cancelInstruction = 0;\n',
            '    invalidate = 0; maintenance_valid = 0; memory_request_ready = 0; memory_response_valid = 0;\n',
            '    memory_response_bits_fault = 0; memory_response_bits_tag = 0; state_sum = 0; state_mxr = 0;\n']
    if parameters['pmpEntries']:
        body += [f"    pmp_config = 'h1f; pmp_address = 'h{(1 << (parameters['physicalAddressBits'] - 2)) - 1:x};\n"]
    def context(asid, page_root=root):
        body.append(f"    state_satp = 64'h{8 << 60 | asid << 44 | page_root >> 12:x}; maintenance_valid = 1; maintenance_fence = 0; tick(); maintenance_valid = 0;\n")
    def fence(address=None, asid=None):
        body.append(f'''    maintenance_valid = 1; maintenance_fence = 1; maintenance_addressValid = {int(address is not None)};
    maintenance_address = 64'h{(address or 0):x}; maintenance_asidValid = {int(asid is not None)}; maintenance_asid = {asid or 0};
    #1; check(!ports_0_request_ready && !ports_1_request_ready, "Maintenance blocks new ownership"); tick(); maintenance_valid = 0;
''')
    def demand(asid, page, miss, global_page=False, port=1, page_root=root, switch=True):
        if switch:
            context(asid, page_root)
        virtual, physical = (page << 30) | 0x100, base + (asid if not global_page else 0) * 0x1000 + 0x100
        body.append(f'''    ports_{port}_request_bits_address = 64'h{virtual:x}; ports_{port}_request_bits_privilege = 1;
    ports_{port}_request_bits_fetch = {int(port == 0)}; ports_{port}_request_bits_write = 0;
    ports_{port}_request_valid = 1; #1; while (!ports_{port}_request_ready) tick(); tick(); ports_{port}_request_valid = 0;
''')
        if miss:
            tables = [(page_root + page * 8, ((root + 0x1000) >> 12) << 10 | 1 | (32 if global_page else 0)),
                      (root + 0x1000, ((root + 0x2000) >> 12) << 10 | 1),
                      (root + 0x2000, ((physical >> 12) << 10) | 0xcf)]
            for address, pte in tables:
                body.append(f'''    while (!memory_request_valid) begin check(!ports_{port}_response_valid, "Context miss requires PTE service"); tick(); end
    check(memory_request_bits_address == 64'h{address:x}, "ASID walk root and page ownership");
    memory_request_ready = 1; tick(); memory_request_ready = 0; memory_response_bits_data = 64'h{pte:x};
    memory_response_valid = 1; tick(); memory_response_valid = 0;
''')
        body.append(f'''    while (!ports_{port}_response_valid) begin check(!memory_request_valid, "Selective fence retained an eligible translation"); tick(); end
    check(!memory_request_valid && !ports_{port}_response_bits_fault && ports_{port}_response_bits_address == 64'h{physical:x}, "ASID and inherited global leaf identity");
    ports_{port}_response_ready = 1; tick(); ports_{port}_response_ready = 0;
''')
    entries = ((1, 0, False), (2, 0, False), (2, 1, False), (1, 2, True))
    for address_valid, asid_valid in ((False, False), (True, False), (False, True), (True, True)):
        body.append('    invalidate = 1; tick(); invalidate = 0;\n')
        for asid, page, global_page in entries:
            demand(asid, page, True, global_page)
        fence(0 if address_valid else None, 1 if asid_valid else None)
        for index, (asid, page, global_page) in enumerate(entries):
            invalidated = (not address_valid or page == 0) and (not asid_valid or asid == 1 and not global_page)
            if not invalidated:
                demand(2 if global_page else asid, page, False, global_page, index % 2)
        for asid, page, global_page in entries:
            if (not address_valid or page == 0) and (not asid_valid or asid == 1 and not global_page):
                demand(asid, page, True, global_page)
    fence(1 << 39)
    demand(1, 0, False)
    fence(None, 0)
    demand(1, 0, False)
    fence(None, 1)
    demand(1, 0, True, page_root=root + 0x3000)
    body.append('    invalidate = 1; tick(); invalidate = 0;\n')
    demand(1, 0, True, port=0)
    demand(1, 0, False, port=1, switch=False)
    fence(None, 2)
    demand(1, 0, False, port=0, switch=False)
    demand(1, 0, False, port=1, switch=False)
    fence(0, 1)
    demand(1, 0, True, port=0, switch=False)
    demand(1, 0, False, port=1, switch=False)
    for phase in ('waiting', 'leaf'):
        body.append('    invalidate = 1; tick(); invalidate = 0;\n')
        context(1)
        body.append("    ports_1_request_bits_address = 'h100; ports_1_request_bits_privilege = 1; ports_1_request_bits_fetch = 0; ports_1_request_valid = 1; #1; while (!ports_1_request_ready) tick(); tick(); ports_1_request_valid = 0;\n")
        for n, (address, pte) in enumerate(((root, (root + 0x1000) >> 2 | 1),
                (root + 0x1000, (root + 0x2000) >> 2 | 1), (root + 0x2000, (base + 0x1000) >> 2 | 0xcf))):
            body.append(f"    while (!memory_request_valid) tick(); check(memory_request_bits_address == 'h{address:x}, \"In-flight walk context\"); memory_request_ready = 1; tick(); memory_request_ready = 0;\n")
            if n == 0 and phase == 'waiting':
                fence(None, 1)
            if n == 2 and phase == 'leaf':
                body.append('    maintenance_valid = 1; maintenance_fence = 1; maintenance_addressValid = 0; maintenance_asidValid = 0;\n')
            body.append(f"    memory_response_bits_data = 'h{pte:x}; memory_response_valid = 1; tick(); memory_response_valid = 0; maintenance_valid = 0;\n")
        body.append(f"    while (!ports_1_response_valid) tick(); check(!ports_1_response_bits_fault && ports_1_response_bits_address == 'h{base + 0x1100:x}, \"Old response retains accepted context\"); ports_1_response_ready = 1; tick(); ports_1_response_ready = 0;\n")
        demand(1, 0, True, switch=False)
    return ''.join(body)


def translated_consumer_contract(parameters, fetch):
    physical = int(parameters['resetVector']) + 0x1000
    body = '    reset = 1; tick(); reset = 0; tick(); privilege = 1;\n'
    if parameters['pmpEntries']:
        addresses = ((physical >> 2) | 0x1ff) | ((((physical + 0x1000) >> 2) | 0x1ff) << (parameters['physicalAddressBits'] - 2))
        body += f"    pmp_config = 'h1f1f; pmp_address = 'h{addresses:x};\n"
    def start(virtual, operation=None):
        nonlocal body
        body += '    privilege = 1;\n'
        if fetch:
            body += f"    request_bits_pc = 'h{virtual:x}; request_bits_tag = 37; request_valid = 1;\n"
        else:
            body += f'''    storeAllowed = 1; input_bits_address = 'h{virtual:x}; input_bits_instruction_pc = 'h40; input_bits_instruction_tag = 37;
    input_bits_instruction_fault = 0; input_bits_memorySize = 3; input_bits_atomic = {int(operation is not None)};
    input_bits_load = {int(operation != 3)}; input_bits_store = {int(operation == 3)}; input_bits_instruction_instruction = 32'h{amo(operation, 1, 2) if operation is not None else ld(1, 2):x};
    input_valid = 1; tick(); input_valid = 0;
'''
        body += f'''    {'privilege = 3;' if not fetch else ''}
    repeat (2) begin
      check(translation_request_valid && translation_request_bits_address == 'h{virtual:x} && translation_request_bits_privilege == 1 && translation_request_bits_fetch == {int(fetch)} && translation_request_bits_write == {int(operation == 3)} && !memory_request_valid, "Retained virtual address and effective privilege"); tick();
    end
    translation_request_ready = 1; tick(); translation_request_ready = 0;
'''
        if fetch:
            body += '    request_valid = 0; privilege = 3;\n'
    def translated(address, cause=0):
        nonlocal body
        body += f'''    translation_response_bits_address = 64'h{address:x}; translation_response_bits_fault = {int(bool(cause))}; translation_response_bits_cause = {cause}; translation_response_valid = 1;
    check(translation_response_ready, "Translation response ownership"); tick(); translation_response_valid = 0;
'''
    def complete(virtual, address, operation=None, eligible=False):
        nonlocal body
        burst = fetch and parameters['iCacheBytes'] and parameters.get('enableBurstRefill')
        for word in range(1 if burst else 16 if fetch and parameters['iCacheBytes'] else 1):
            body += f'''    while (!memory_request_valid) tick();
    check(memory_request_bits_address == 64'h{address + 4*word:x} && memory_request_bits_privileged && memory_request_bits_scEligible == {int(eligible)}, "Physical request address and reservation qualification");
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_tag = 37;
'''
            for chunk in range(8 if burst else 1):
                body += f"    memory_response_bits_data = 'h13; memory_response_bits_last = {int(not burst or chunk == 7)}; memory_response_valid = 1; while (!memory_response_ready) tick(); tick(); memory_response_valid = 0;\n"
        body += f'''    while (!output_valid) tick();
    check(!output_bits_{'fault' if fetch else 'instruction_fault'} && output_bits_{'pc' if fetch else 'address'} == 'h{virtual:x}, "Architectural output retains virtual identity");
    output_ready = 1; tick(); output_ready = 0;
'''
    start(0x100, None if fetch else 2)
    translated(physical)
    complete(0x100, physical, None if fetch else 2)
    if not fetch:
        for virtual, address, operation, eligible in ((0x200, physical, 3, True), (0x100, physical, 2, False), (0x100, physical + 0x1000, 3, False)):
            start(virtual, operation)
            translated(address)
            complete(virtual, address, operation, eligible)
    for cause in ((12, 1) if fetch else (13, 5)):
        start(0x300)
        translated(0x300, cause)
        body += f'''    while (!output_valid) tick();
    check(!memory_request_valid && output_bits_{'fault' if fetch else 'instruction_fault'} && output_bits_{'cause' if fetch else 'instruction_cause'} == {cause} && output_bits_{'tval' if fetch else 'instruction_tval'} == 'h300, "Translation fault retains original virtual address");
    output_ready = 1; tick(); output_ready = 0;
'''
    if parameters['pmpEntries']:
        body += "    pmp_config = 'h1f; pmp_address = 'h40;\n"
        start(0x100)
        translated(physical)
        body += f'''    while (!output_valid) tick();
    check(!memory_request_valid && output_bits_{'fault' if fetch else 'instruction_fault'} && output_bits_{'cause' if fetch else 'instruction_cause'} == {1 if fetch else 5} && output_bits_{'tval' if fetch else 'instruction_tval'} == 'h100, "Final PMP checks physical address before a cached or external access");
    output_ready = 1; tick(); output_ready = 0;
'''
    if fetch:
        start(0x400)
        body += '    cancel = 1; tick(); cancel = 0;\n'
        translated(physical + 0x2000)
        body += '    repeat (3) begin check(!memory_request_valid && !output_valid, "Cancelled translation created a physical demand"); tick(); end\n'
    return body


def privilege_memory_contract(parameters, fetch, frontend=False):
    body = ''
    address = int(parameters['resetVector']) + 0x100
    for privilege in ((0, 1, 3) if parameters.get('enableSupervisorMode') else (0, 3)):
        if frontend:
            body += '    halt = 1; redirect = 0;\n'
        body += f'    reset = 1; tick(); reset = 0; tick(); privilege = {privilege}; memory_request_ready = 0; memory_response_valid = 0; output_ready = 0;\n'
        if parameters['pmpEntries']:
            body += f"    pmp_config = 'h1f; pmp_address = 'h{(1 << (parameters['physicalAddressBits'] - 2)) - 1:x};\n"
        body += (f"    redirect = 1; redirectPc = 'h{address:x}; tick(); redirect = 0; halt = 0; tick(); halt = 1;\n" if frontend else
                 f"    request_bits_pc = 'h{address:x}; request_valid = 1; tick(); request_valid = 0;\n" if fetch else
                 f"    input_bits_instruction_fault = 0; input_bits_address = 'h{address:x}; input_bits_load = 1; input_bits_store = 0; input_bits_memorySize = 3; input_valid = 1; tick(); input_valid = 0;\n")
        body += f'''    privilege = {0 if privilege == 3 else 3}; repeat (6) tick();
    repeat (3) begin
      check(memory_request_valid && memory_request_bits_privileged == {int(privilege != 0)}, "Accepted access retains privilege"); tick();
    end
'''
    if fetch and not frontend and parameters.get('enableSupervisorMode') and parameters['pmpEntries'] and parameters['iCacheBytes']:
        demand = address + 8
        body += f'''    reset = 1; tick(); reset = 0; tick(); privilege = 1;
    pmp_config = 'h14; pmp_address = 'h{demand >> 2:x}; memory_request_ready = 0; memory_response_valid = 0;
    request_bits_pc = 'h{demand:x}; request_valid = 1; tick(); request_valid = 0; privilege = 3;
    repeat (12) tick();
    check(memory_request_valid && memory_request_bits_address == 'h{demand:x} && memory_request_bits_privileged, "Captured S mode denies neighboring refill words");
    memory_response_bits_tag = memory_request_bits_tag; memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_data = 'h12345013; memory_response_valid = 1; tick(); memory_response_valid = 0;
    while (!output_valid) tick();
    check(!output_bits_fault && output_bits_pc == 'h{demand:x} && output_bits_instruction == 'h12345013 && !memory_request_valid, "Authorized S demand survives denied speculation");
'''
    return body + '    reset = 1; tick(); reset = 0; tick(); privilege = 3;\n'


def protection_contract(fetch):
    prefix = '    reset = 1; tick(); reset = 0; tick();\n    pmp_config = 128\'h98; pmp_address = \'h40;\n'
    if fetch:
        return prefix + '''
    output_ready = 0; memory_response_valid = 0; memory_request_ready = 0;
    request_bits_pc = 'h100; request_valid = 1; tick(); request_valid = 0;
    repeat (3) begin
      check(output_valid && output_bits_fault && output_bits_cause == 1 && output_bits_tval == 'h100 && !memory_request_valid, "Denied fetch escaped"); tick();
    end
    output_ready = 1; tick(); output_ready = 0;
    pmp_config = 0; request_valid = 1; tick(); request_valid = 0; pmp_config = 'h98;
    repeat (3) begin check(memory_request_valid, "Policy update withdrew a presented fetch"); tick(); end
    cancel = 1; tick(); cancel = 0;
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_valid = 1; tick(); memory_response_valid = 0; tick();
    check(!output_valid && request_ready, "Old authorized fetch did not drain");
'''
    return prefix + '''
    input_bits_memorySize = 3;
    input_bits_instruction_fault = 0; input_bits_address = 'h100; input_bits_load = 1; input_bits_store = 0;
    input_valid = 1; tick(); input_valid = 0;
    for (integer cycles = 0; !output_valid; cycles++) begin
      check(cycles < 2 && !memory_request_valid, "Denied load authorization bound"); tick();
    end
    repeat (3) begin
      check(output_valid && output_bits_instruction_fault && output_bits_instruction_cause == 5 && !memory_request_valid, "Denied load escaped"); tick();
    end
    output_ready = 1; tick(); output_ready = 0;
    input_bits_store = 1; input_bits_load = 0; storeAllowed = 1;
    input_valid = 1; tick(); input_valid = 0;
    check(output_valid && output_bits_instruction_cause == 7 && output_bits_instruction_tval == 'h100 && !memory_request_valid, "Denied store escaped");
    output_ready = 1; tick(); output_ready = 0;
    pmp_config = 0; input_bits_store = 0; input_bits_load = 1;
    input_valid = 1; tick(); input_valid = 0; pmp_config = 'h98;
    repeat (3) begin check(memory_request_valid, "Policy update withdrew a presented load"); tick(); end
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_tag = input_bits_instruction_tag; memory_response_valid = 1;
    tick(); memory_response_valid = 0; output_ready = 1; tick();
'''


def backend_protection_contract():
    def send(words, pc):
        return ''.join(f'''
    instruction_bits_pc = 'h{pc + 4 * i:x}; instruction_bits_instruction = 'h{word:x};
    instruction_bits_tag = {i}; instruction_valid = 1;
    while (!instruction_ready) tick(); tick(); instruction_valid = 0;
''' for i, word in enumerate(words))

    body = ''
    for younger in (ld(4, 0), sd(2, 0), mul(4, 2, 2)):
        body += '''
    reset = 1; tick(); reset = 0; tick();
    data_request_ready = 0; data_response_valid = 0; data_response_bits_fault = 0;
    begin
      integer redirects;
      redirects = 0;
      fork
        begin
          repeat (64) begin
            if (redirect) begin
              check(!status_trap && redirectPc == 'h10c, "PMP update restart");
              redirects = redirects + 1;
            end
            check(!data_request_valid, "Younger access escaped PMP update"); tick();
          end
        end
        begin
''' + send((0x10b7, addi(2, 0, 0x99), csr(0, 0x3a0, 2), younger), 0x100) + '''
        end
      join
      check(redirects == 1, "Missing or repeated PMP update redirect");
    end
''' + send((sd(4, 1),), 0x200) + '''
    while (!data_request_valid) tick();
    check(data_request_bits_data == 0 && data_request_bits_address == 'h1000, "Younger mulDiv wrote a destination");
    data_request_ready = 1; tick(); data_request_ready = 0;
    data_response_bits_tag = data_request_bits_tag; data_response_valid = 1;
    tick(); data_response_valid = 0; repeat (8) tick();
''' + send((csr(5, 0x3a0, 0, True), sd(5, 1)), 0x300) + '''
    while (!data_request_valid) begin check(!redirect, "PMP read restarted execution"); tick(); end
    check(data_request_bits_data == 'h99, "PMP read lost its owner or value");
    data_request_ready = 1; tick(); data_request_ready = 0;
    data_response_bits_tag = data_request_bits_tag; data_response_valid = 1;
    tick(); data_response_valid = 0; repeat (8) tick();
'''
    return body


def local_interrupt_contract(parameters):
    base, harts = int(parameters['localInterruptBase']), parameters['hartCount']
    model = LocalInterrupts(base, harts)
    body = '    timeTick = 0; memory_response_ready = 0;\n'

    def levels():
        return ''.join(f'''    check(interrupts_{hart}_software == {model.software[hart]} && interrupts_{hart}_timer == {int(model.time >= model.compare[hart])} && !interrupts_{hart}_external, "Independent interrupt levels {hart}");
''' for hart in range(harts))

    def access(offset, size=3, write=False, value=0, mask=None, fetch=False, atomic=False):
        nonlocal body
        mask = ((1 << (1 << size)) - 1 if write else 0) if mask is None else mask
        fault = fetch or atomic or (write and mask != (1 << (1 << size)) - 1)
        result = 0
        if not fault:
            try:
                result = model.access(base + offset, 1 << size, 'write' if write else 'read', value)
            except Fault:
                fault = True
        body += f'''    memory_request_bits_address = 64'h{base + offset:x}; memory_request_bits_size = {size};
    memory_request_bits_write = {int(write)}; memory_request_bits_fetch = {int(fetch)}; memory_request_bits_atomic = {int(atomic)};
    memory_request_bits_data = 64'h{value & ((1 << 64) - 1):x}; memory_request_bits_mask = {mask}; memory_request_bits_tag = 91;
    memory_request_valid = 1; check(memory_request_ready, "Local slot unavailable"); tick(); memory_request_valid = 0;
    memory_request_bits_address = 0; memory_request_bits_data = '1;
    repeat (3) begin
      check(memory_response_valid && !memory_request_ready && memory_response_bits_tag == 91 && memory_response_bits_fault == {int(fault)} && memory_response_bits_data == 64'h{result:x}, "Local response retention"); tick();
    end
''' + levels() + '''    memory_response_ready = 1; tick(); memory_response_ready = 0;
    check(!memory_response_valid && memory_request_ready, "Local response reused incorrectly");
'''

    body += levels()
    for hart in range(harts):
        access(4 * hart, 2, True, -1)
        access(4 * hart, 2)
        access(4 * hart, 2, True, 2)
        access(0x4000 + 8 * hart, 3, True, 12 + hart)
        access(0x4000 + 8 * hart)
    for offset, size in ((4 * harts, 2), (0x4000 + 8 * harts, 3), (0x1000, 3), (0, 3), (0x4000, 2), (0xbff8, 2), (0xbffc, 2)):
        access(offset, size, True, 1)
        access(offset, size)
    for options in (dict(mask=1), dict(fetch=True), dict(atomic=True)):
        access(0, 2, True, 1, **options)
    access(0xbff8, write=True, value=11)
    body += '    timeTick = 1; tick(); timeTick = 0;\n'
    model.time += 1
    body += levels()
    access(0xbff8)
    body += '''    timeTick = 1; memory_request_bits_address = 64'h''' + f'{base + 0xbff8:x}' + ''';
    memory_request_bits_size = 3; memory_request_bits_write = 1; memory_request_bits_fetch = 0; memory_request_bits_atomic = 0;
    memory_request_bits_mask = 255; memory_request_bits_data = 4; memory_request_valid = 1;
    tick(); memory_request_valid = 0; timeTick = 0;
    memory_response_ready = 1; tick(); memory_response_ready = 0;
'''
    model.time = 4
    body += levels()
    access(0xbff8)
    body += f'''    memory_request_bits_address = 64'h{base + 0xbff8:x}; memory_request_bits_size = 3;
    memory_request_bits_write = 0; memory_request_bits_mask = 0; memory_request_valid = 1; timeTick = 1;
    tick(); memory_request_valid = 0;
    repeat (3) begin
      check(memory_response_valid && memory_response_bits_data == 4 && !memory_response_bits_fault, "Timer read snapshot under backpressure"); tick();
    end
    memory_response_ready = 1; tick(); memory_response_ready = 0; timeTick = 0;
'''
    model.time = 9
    body += levels()
    access(0xbff8)
    access(0xbff8, write=True, value=(1 << 64) - 1)
    body += '    timeTick = 1; tick(); timeTick = 0;\n'
    model.time = 0
    body += levels()
    access(0xbff8)
    return body


def shared_cache_contract(parameters):
    width = parameters['axiDataBits']
    size, beat_bytes = (width // 8).bit_length() - 1, width // 8
    beats = 64 // beat_bytes
    region = next(r for r in parameters['memoryRegions'] if not r['device'] and
                  (r['executable'] or r['readable'] and r.get('dataCacheable')) and int(r['size']) >= 128)
    base = (int(region['base']) + 63) & ~63
    prot = 0 if region['readable'] and region.get('dataCacheable') else 4
    body = ''

    def read(address, miss, count=1, access_size=size, lock=False, error=-1, wrong_id=-1, chunks=None, version=0, cache=14):
        nonlocal body
        body += f'''    upstream_ar_bits_addr = {parameters['physicalAddressBits']}'h{address:x}; upstream_ar_bits_id = 1;
    upstream_ar_bits_len = {count-1}; upstream_ar_bits_size = {access_size}; upstream_ar_bits_burst = 1;
    upstream_ar_bits_lock = {int(lock)}; upstream_ar_bits_prot = {prot}; upstream_ar_bits_cache = {cache}; upstream_ar_bits_qos = 2;
    upstream_ar_valid = 1; upstream_r_ready = 0; downstream_ar_ready = 0;
    #1; while (!upstream_ar_ready) tick(); tick(); upstream_ar_valid = 0;
'''
        if miss:
            body += f'''    while (!downstream_ar_valid) begin check(!upstream_r_valid, "Cold read requires physical service"); tick(); end
    repeat (3) begin
      check(downstream_ar_valid && downstream_ar_bits_addr == {parameters['physicalAddressBits']}'h{address:x} &&
        downstream_ar_bits_id == 1 && downstream_ar_bits_len == {count-1} && downstream_ar_bits_size == {access_size} &&
        downstream_ar_bits_lock == {int(lock)} && downstream_ar_bits_prot == {prot} && downstream_ar_bits_cache == {cache} && downstream_ar_bits_qos == 2,
        "Miss address and attributes retained under backpressure"); tick();
    end
    downstream_ar_ready = 1; tick(); downstream_ar_ready = 0;
'''
        actual = count if chunks is None else chunks
        for beat in range(actual):
            physical = (address & -beat_bytes) + beat * beat_bytes
            value = sum(((physical + 8 * word + version + 19) * 0x0102030405060709 & MASK) << (64 * word) for word in range(width // 64))
            last, response, identity = int(beat == actual - 1), 2 if beat == error else 0, 1 ^ int(beat == wrong_id)
            if miss:
                body += f'''    downstream_r_bits_data = {width}'h{value:x}; downstream_r_bits_id = {identity};
    downstream_r_bits_resp = {response}; downstream_r_bits_last = {last}; downstream_r_valid = 1;
'''
            body += f'''    while (!upstream_r_valid) begin check(!downstream_ar_valid, "Hit issued an external read"); tick(); end
    repeat (3) begin
      check(upstream_r_valid && upstream_r_bits_data == {width}'h{value:x} && upstream_r_bits_id == {identity} &&
        upstream_r_bits_resp == {response} && upstream_r_bits_last == {last} && !upstream_ar_ready && !downstream_ar_valid,
        "Read bytes, identity and terminal framing held"); tick();
    end
    upstream_r_ready = 1; tick(); upstream_r_ready = 0;
'''
            if miss:
                body += '    downstream_r_valid = 0;\n'

    def write(address, order, response=0):
        nonlocal body
        body += f'''    upstream_aw_bits_addr = {parameters['physicalAddressBits']}'h{address:x}; upstream_aw_bits_id = 1;
    upstream_aw_bits_len = 0; upstream_aw_bits_size = 0; upstream_aw_bits_burst = 1;
    upstream_w_bits_data = 91; upstream_w_bits_strb = 1; upstream_w_bits_last = 1;
    downstream_aw_ready = 1; downstream_w_ready = 1; upstream_b_ready = 0;
'''
        for channel in (('aw', 'w') if order == 0 else ('w', 'aw') if order == 1 else ('aw',)):
            both = order == 2
            body += f'    upstream_{channel}_valid = 1;\n'
            if both:
                body += '    upstream_w_valid = 1;\n'
            body += f'''    #1; while (!upstream_{channel}_ready) tick();
    check(downstream_{channel}_valid, "Write channel forwarded");
    check(downstream_aw_bits_addr == {parameters['physicalAddressBits']}'h{address:x} && downstream_aw_bits_id == 1 &&
      downstream_w_bits_data == 91 && downstream_w_bits_strb == 1 && downstream_w_bits_last, "Write payload retained");
    tick(); upstream_{channel}_valid = 0;
'''
            if both:
                body += '    upstream_w_valid = 0;\n'
        body += f'''    downstream_aw_ready = 0; downstream_w_ready = 0;
    downstream_b_bits_id = 1; downstream_b_bits_resp = {response}; downstream_b_valid = 1;
    upstream_ar_valid = 1;
    repeat (3) begin
      check(upstream_b_valid && upstream_b_bits_id == 1 && upstream_b_bits_resp == {response} &&
        !downstream_b_ready && !upstream_ar_ready && !downstream_ar_valid, "Write response and invalidation ordered before new reads"); tick();
    end
    upstream_b_ready = 1; tick(); upstream_b_ready = 0; downstream_b_valid = 0; upstream_ar_valid = 0;
'''

    read(base, True, beats)
    for cache in (0, 1, 2, 3):
        read(base, True, beats, cache=cache)
    read(base, False, beats)
    read(base + 64, True, beats, cache=10)
    read(base + 64, True, beats, cache=10)
    read(base, False, beats, cache=10)
    if int(region['size']) < 2 * parameters['l2CacheBytes']:
        read(base, False, beats)
        for order in range(3):
            write(base, order, 2 if order == 1 else 0)
            read(base, True, beats, version=order + 1)
            read(base, False, beats, version=order + 1)
        read(base, True, beats, lock=True)
        read(base, True, beats)
        read(base, False, beats)
        return body
    write(base, 0)
    for address in (base, base + parameters['l2CacheBytes'] - 64):
        read(address, True, beats)
        read(address, False, beats)
        read(address + beat_bytes - 1, False, access_size=0)
    other = base + parameters['l2CacheBytes']
    read(other, True, beats)
    read(base, True, beats)
    for order in range(3):
        write(base, order, 2 if order == 1 else 0)
        read(base, True, beats, version=order + 1)
        read(base, False, beats, version=order + 1)
    read(base, True, beats, lock=True)
    read(base, True, beats)
    read(base, False, beats)
    for options in (dict(error=beats-1), dict(wrong_id=0), dict(chunks=beats+1), *([dict(chunks=beats-1)] if beats > 1 else [])):
        read(other, True, beats, **options)
        read(other, True, beats)
        read(base, True, beats)
    narrow = base + 64
    read(narrow, True, access_size=0)
    read(narrow, True, access_size=0)
    read(narrow, True)
    read(narrow, False)
    for bit in range((parameters['l2CacheBytes'] - 1).bit_length(), parameters['physicalAddressBits']):
        alias = base + (1 << bit)
        if alias + 64 <= int(region['base']) + int(region['size']):
            read(alias, True, beats)
            read(base, True, beats)
    for r in parameters['memoryRegions']:
        if r['device']:
            read(int(r['base']), True)
            read(int(r['base']), True)
            break
    return body


def verify(rtl, directory, modules=None):
    directory.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    parameters = manifest['parameters']
    def emitted_source(name): return (rtl / (name + '.sv')).read_text() if (rtl / (name + '.sv')).is_file() else ''
    verified = []
    enabled = parameters['pmpEntries'] != 0
    cached = bool(parameters['iCacheBytes'])
    if not parameters.get('enableA', True):
        lsu_source = emitted_source('DitDahA1Lsu')
        assert 'reservedWord' not in lsu_source and 'reservedDoubleword' not in lsu_source, 'Disabled reservation state was emitted'
    suites = (('DitDahA1Fetch', (burst_fetch_contract(parameters) if parameters.get('enableBurstRefill') else cached_fetch_contract(parameters)) if cached else FETCH + (protection_contract(True) if enabled else '')),
                       ('DitDahA1Lsu', lsu_queue_contract(parameters) if parameters.get('loadQueueEntries', 1) == 2 else
                        LSU + (lsu_reservation_contract(parameters) if parameters.get('enableA', True) else '') + (protection_contract(False) if enabled else '') + lsu_refill_contract(parameters)),
                       ('DitDahA1MulDiv', muldiv_contract()),
                       ('DitDahA1Frontend', (burst_fetch_contract(parameters, True) if parameters.get('enableBurstRefill') else cached_fetch_contract(parameters, True)) if cached else frontend_contract(parameters)),
                       ('DitDahA1Decode', decode_contract(parameters, directory)),
                       ('DitDahA1Execute', execute_contract(parameters)),
                       ('DitDahA1Backend', backend_queue_contract(parameters) if parameters.get('loadQueueEntries', 1) == 2 else
                        backend_contract(parameters) + backend_fence_contract() + (backend_protection_contract() if enabled else '') +
                        (backend_interrupt_contract() if parameters['enableInterrupts'] else '')),
                       ('DitDahA1MemoryArbiter', arbiter_contract(parameters)),
                       ('DitDahA1Memory', memory_contract(parameters)),
                       ('DitDahA1Axi', axi_contract(parameters['axiDataBits'], parameters['hartCount'], parameters.get('enableA', True)) +
                        (burst_axi_contract(parameters) if parameters.get('enableBurstRefill') else '') +
                        (burst_axi_contract(parameters, False) if parameters.get('dCacheRefillBytes') == 64 else '')),
                       ('DitDahA1MemoryFabric', fabric_contract(parameters)))
    if parameters.get('fabricReadSlots') or parameters['hartCount'] > 1:
        suites += (('DitDahA1ReadQueue', read_queue_contract(parameters)),)
    if cached:
        suites += (('DitDahA1InstructionCache', instruction_cache_contract(parameters)),)
    if parameters.get('localInterruptBase'):
        suites += (('DitDahA1LocalInterrupts', local_interrupt_contract(parameters)),)
    if parameters.get('dCacheBytes'):
        suites += (('DitDahA1DataCache', data_cache_queue_contract(parameters) if parameters.get('loadQueueEntries', 1) == 2 else data_cache_contract(parameters)),
                   ('DitDahA1Coherence', coherence_contract(parameters)))
    if manifest['implementation'].get('l2CacheBytes'):
        suites += (('DitDahA1SharedCache', shared_cache_contract(parameters)),)
    if enabled:
        suites += (('DitDahA1Pmp', pmp_contract(parameters)),)
    identity = ''.join(f'''    hartId = {hart}; readAddress = 'hf14;
    check(legal && readData == {hart}, "Hart identity");
    writeAddress = 'hf14; writeData = '1; write = 1; tick(); write = 0;
    check(readData == {hart}, "Hart identity is read-only");
''' for hart in range(16)) + '    hartId = 0;\n'
    identity += "    readAddress = 'hf15; check(legal && readData == 0, \"Configuration pointer zero\");\n"
    suites += (('DitDahA1Csr', identity + (csr_contract(parameters) if enabled else '') +
                (supervisor_csr_contract(parameters) if parameters.get('enableSupervisorMode') else
                 (interrupt_csr_contract(parameters) if parameters['enableInterrupts'] else '') +
                 (user_csr_contract(parameters) if parameters.get('enableUserMode') else ''))),)
    if parameters.get('enableUserMode'):
        suites = tuple((name, body + (privilege_memory_contract(parameters, name != 'DitDahA1Lsu', name == 'DitDahA1Frontend')
                       if name in ('DitDahA1Fetch', 'DitDahA1Frontend', 'DitDahA1Lsu') and
                       (name != 'DitDahA1Lsu' or parameters.get('loadQueueEntries', 1) == 1) else '')) for name, body in suites)
    if parameters.get('virtualAddressBits') == 39:
        suites = tuple((name, body) for name, body in suites if name not in
                       ('DitDahA1Fetch', 'DitDahA1Frontend', 'DitDahA1Lsu', 'DitDahA1Backend'))
        suites += (('DitDahA1Translation', translation_contract(parameters) + translation_context_contract(parameters)),)
        suites += (('DitDahA1Fetch', translated_consumer_contract(parameters, True)),
                   ('DitDahA1Lsu', lsu_queue_contract(parameters) if parameters.get('loadQueueEntries', 1) == 2 else
                    translated_consumer_contract(parameters, False) + lsu_refill_contract(parameters)))
        suites += (('DitDahA1Frontend', frontend_group_contract(parameters)),)
    if cached and parameters['issueWidth'] > 1:
        suites = tuple((name, body + (wide_fetch_contract(parameters) if name == 'DitDahA1Fetch' else '')) for name, body in suites)
    suites = tuple((name, (body if parameters['issueWidth'] == 1 and parameters.get('virtualAddressBits') != 39 else '') + frontend_group_contract(parameters) + prediction_contract(parameters)
                    if name == 'DitDahA1Frontend' else body) for name, body in suites)
    if parameters.get('enableC'):
        suites = tuple((name, compressed_fetch_contract(parameters, name == 'DitDahA1Frontend')
                        if name in ('DitDahA1Fetch', 'DitDahA1Frontend') else body) for name, body in suites)
    assert not modules or set(modules) <= {name for name, _ in suites}, 'Unsupported contract selection'
    for name, body in suites:
        if name == 'DitDahA1MulDiv' and not parameters.get('enableM', True):
            assert not (rtl / (name + '.sv')).exists(), 'Disabled arithmetic resource was emitted'
            assert name not in emitted_source('DitDahA1Backend'), 'Disabled arithmetic resource was instantiated'
            continue
        if modules and name not in modules:
            continue
        module = rtl / (name + '.sv')
        test = directory / (name + '_tb.sv')
        if name in ('DitDahA1Frontend', 'DitDahA1Backend'):
            port = 'output' if name == 'DitDahA1Frontend' else 'instruction'
            body = re.sub(rf'\b{port}_bits_(pc|tag|instruction|length|fault|cause|tval)\b', rf'{port}_bits_packets_0_\1', body)
            if name == 'DitDahA1Backend':
                body = '    instruction_bits_count = 1;\n' + body
                body = re.sub(r'\bdut\.(instruction|decoded|issued|result|memory|commit)Valid\b',
                              r'(dut.\1Count != 0)', body)
                body += backend_group_contract(parameters) + (backend_branch_contract() if parameters.get('loadQueueEntries', 1) == 1 else '') + backend_memory_group_contract(parameters)
        source = bench(module, body, 4 + 69 * body.count('MulDiv resource reuse')) if name == 'DitDahA1MulDiv' else bench(module, body)
        if name in ('DitDahA1Axi', 'DitDahA1ReadQueue'):
            prefix = 'axi_' if name == 'DitDahA1Axi' else ''
            checks = axi_cache_attributes(parameters)
            for channel in ('ar', 'aw') if name == 'DitDahA1Axi' else ('ar',):
                signal = prefix + channel
                checks += f'''  always @(posedge clock) if (!reset && {signal}_valid)
    if ({signal}_bits_cache != expected_cache({signal}_bits_addr,
      (1 << {signal}_bits_size) * (1 + integer'({signal}_bits_len)), {signal}_bits_prot[2],
      {int(channel == 'aw')}, {signal}_bits_lock)) $fatal(1, "AXI memory type and allocation attributes");
'''
            source = source.replace('  initial begin', checks + '  initial begin', 1)
        test.write_text(source)
        binary = directory / name
        dependencies = [rtl / 'DitDahA1Fetch.sv'] if name == 'DitDahA1Frontend' else []
        if cached and name in ('DitDahA1Fetch', 'DitDahA1Frontend'):
            dependencies.append(rtl / 'DitDahA1InstructionCache.sv')
        if cached and name in ('DitDahA1Fetch', 'DitDahA1Frontend', 'DitDahA1InstructionCache'):
            dependencies += [rtl / file for file in (rtl / 'filelist.f').read_text().splitlines()
                             if file.startswith(('instructions_', 'tags_', 'mem_'))]
        if name == 'DitDahA1MemoryFabric':
            dependencies = [rtl / (child + '.sv') for child in ('DitDahA1MemoryArbiter', 'DitDahA1Memory', 'DitDahA1Axi')]
            if parameters.get('dCacheBytes'):
                dependencies.append(rtl / 'DitDahA1Coherence.sv')
            if parameters.get('localInterruptBase'):
                dependencies.append(rtl / 'DitDahA1LocalInterrupts.sv')
            if parameters.get('fabricReadSlots') or parameters['hartCount'] > 1:
                dependencies.append(rtl / 'DitDahA1ReadQueue.sv')
        if name == 'DitDahA1DataCache':
            dependencies = [rtl / file for file in (rtl / 'filelist.f').read_text().splitlines()
                            if file.startswith(('data_', 'dataTags_', 'dataDirty_', 'mem_'))]
        if name == 'DitDahA1SharedCache':
            dependencies = [rtl / file for file in (rtl / 'filelist.f').read_text().splitlines()
                            if file.startswith(('sharedData_', 'sharedTags_', 'mem_'))]
        if name == 'DitDahA1Backend':
            dependencies = [rtl / ('DitDahA1' + child + '.sv') for child in ('Decode', 'Issue', 'Execute', 'Commit', 'Gpr', 'Csr', 'Lsu', *(('MulDiv',) if parameters.get('enableM', True) else ())) ]
        if enabled and name in ('DitDahA1Fetch', 'DitDahA1Lsu', 'DitDahA1Frontend', 'DitDahA1Backend'):
            dependencies.append(rtl / 'DitDahA1Pmp.sv')
        if enabled and name == 'DitDahA1Translation':
            dependencies.append(rtl / 'DitDahA1Pmp.sv')
        subprocess.run(['iverilog', '-g2012', '-s', 'contract_tb', '-o', str(binary),
                        str(module), *map(str, dependencies), str(test)], check=True)
        result = subprocess.run(['vvp', str(binary)], capture_output=True, text=True, timeout=30)
        (directory / (name + '.log')).write_text(result.stdout + result.stderr)
        assert result.returncode == 0 and 'PASS' in result.stdout, result.stdout + result.stderr
        print(f'  {name} interface contracts passed', flush=True)
        verified.append(name)
    if (parameters.get('dCacheWriteback') and parameters['hartCount'] == 2 and
            parameters['dCacheRefillBytes'] == 8 and
            (not modules or {'DitDahA1DataCache', 'DitDahA1Coherence'} <= set(modules))):
        verify_cache_coherence(rtl, rtl, directory / 'cache-coherence', mutations=True)
        verified.append('CacheCoherence')
    return verified
