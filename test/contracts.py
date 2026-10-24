# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Exercise cancellation, authorization and backpressure on unit interfaces."""

from pathlib import Path
import json
import re
import random
import subprocess

from programs import addi, alu, amo, beq, csr, sd, mul, ld, lw, sw, load, store, fence
from model import Fault, LocalInterrupts, Model, MASK, atomic_value, pmp_allowed, signed, sv39_walk


def verify_storage(rtl, directory):
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    size = manifest['implementation']['iCacheBytes']
    data_size = manifest['implementation'].get('dCacheBytes', 0)
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
              for file in files if file.startswith(('instructions_', 'tags_', 'data_', 'dataTags_', 'mem_'))}
    assert ('DitDahA1InstructionCache.sv' in files) == bool(size)
    assert ('DitDahA1DataCache.sv' in files) == bool(data_size)
    banks = 1 << (manifest['parameters']['issueWidth'] - 1).bit_length() if size else 1
    expected = {} if not size else {'instructions': (size // (4 * banks), 32),
        'tags': (size // 64, manifest['parameters']['physicalAddressBits'] - (size // 64).bit_length() - 5)}
    if data_size:
        expected.update(data=(data_size // 8, 64),
                        dataTags=(data_size // 64, manifest['parameters']['physicalAddressBits'] - (data_size // 64).bit_length() - 5))
    assert set(arrays.values()) == set(expected.values())
    if size:
        cache = (rtl / 'DitDahA1InstructionCache.sv').read_text()
        assert len(re.findall(r'^\s*instructions_\d+x32\s+\w+\s*\(', cache, re.M)) == banks
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
                                        for key, value in (('SIZE', depth), ('WIDTH', width))), 'Storage geometry mismatch'
        state = sum(len(cell['connections']['Q']) for cell in cells if cell['type'].startswith('$dff'))
        assert state <= 3 * width + 4 * depth.bit_length(), 'Storage expanded into word registers'
        report.append(dict(array=name, depth=depth, width=width, registerBits=state))
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


def lsu_reservation_contract(parameters):
    body, serial = '', 0

    def transfer(operation, address=0x1000, value=0, fault=False, eligible=False, local_fault=0, wrong_tag=False):
        nonlocal body, serial
        serial += 1
        tag = 80 + serial
        body += f'''    input_bits_atomic = 1; input_bits_instruction_instruction = 32'h{amo(operation, 7, 1, 0 if operation == 2 else 2):x};
    input_bits_instruction_fault = 0; input_bits_instruction_tag = {tag}; input_bits_memorySize = 3;
    input_bits_load = {int(operation != 3)}; input_bits_store = {int(operation != 2)};
    input_bits_address = 64'h{address:x}; input_bits_storeData = 9; input_bits_rd = 7; input_bits_rdWrite = 1;
    input_valid = 1; storeAllowed = 1; tick(); input_valid = 0; storeAllowed = 0;
    input_bits_atomic = 0; input_bits_address = 0;
'''
        if local_fault:
            body += f'    check(output_valid && output_bits_instruction_fault && output_bits_instruction_cause == {local_fault} && !memory_request_valid, "Reservation local fault");\n'
        else:
            body += f'''    repeat (3) begin
      check(memory_request_valid && memory_request_bits_atomic && memory_request_bits_atomicOperation == {operation} && memory_request_bits_scEligible == {int(eligible)} && memory_request_bits_address == 64'h{address:x} && memory_request_bits_mask == {0 if operation == 2 else 255}, "Reservation request capture"); tick();
    end
    memory_request_ready = 1; tick(); memory_request_ready = 0;
    memory_response_bits_tag = {tag + int(wrong_tag)}; memory_response_bits_fault = {int(fault)};
    memory_response_bits_data = 64'h{value:x}; memory_response_valid = 1; tick(); memory_response_valid = 0;
    repeat (3) begin
      check(output_valid && output_bits_instruction_fault == {int(fault or wrong_tag)} && output_bits_rd == 7 && output_bits_rdWrite && output_bits_value == 64'h{value:x}, "Reservation result retention"); tick();
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


def decode_contract(parameters):
    cases = ((0x12345337, 0, 0, 1), (0x12345317, 0, 0, 1),
             (0x12328313, 1, 0, 1), (0x00728333, 1, 1, 1),
             (0x00728463, 1, 1, 0), (0x0080036f, 0, 0, 1),
             (0x00428367, 1, 0, 1), (0x0082b303, 1, 0, 1),
             (0x0072b423, 1, 1, 0), (0x34029373, 1, 0, 1),
             (0x3402a373, 1, 0, 1), (0x00000073, 0, 0, 0),
             (0x30200073, 0, 0, 0), (0x10500073, 0, 0, 0), (0x10400073, 0, 0, 0), (0x10508073, 0, 0, 0), (0x105000f3, 0, 0, 0), (0xffffffff, 0, 0, 0))
    cases += ((mul(6, 5, 7), 1, 1, 1), (mul(6, 5, 7) | (1 << 12), 0, 0, 0))
    cases += ((lw(6, 5, 4), 1, 0, 1), (lw(6, 5, 4, True), 1, 0, 1), (sw(7, 5, 4), 1, 1, 0))
    extra = {alu(6, 5, 7, f): 22 for f in range(1, 8)}
    extra.update({alu(6, 5, 7, f, immediate=True): 21 for f in range(1, 8)})
    extra.update({alu(6, 5, 7, f, word=True, immediate=imm): 23 if imm else 24 for imm in (False, True) for f in (0, 1, 5)})
    extra.update({beq(5, 7, 8) | (f << 12): 25 for f in (1, 4, 5, 6, 7)})
    extra.update({load(6, 5, 4, s, u): 26 for s in (0, 1) for u in (False, True)})
    extra.update({store(7, 5, 4, s): 27 for s in (0, 1)})
    extra.update({csr(6, 0x340, 5, function=f): 28 for f in (3, 5, 6, 7)})
    extra.update({amo(op, 6, 5, 0 if op == 2 else 7, order): 30 for op in (1, 2, 3, 8) for order in range(4)})
    if parameters.get('enableSupervisorMode'):
        extra[0x10200073] = 31
    cases += tuple((word, int(op != 31 and (op != 28 or (word >> 12) & 4 == 0)), int(op in (22, 24, 25, 27) or op == 30 and word >> 27 != 2), int(op not in (25, 27, 31))) for word, op in extra.items())
    invalid = {amo(op, 6, 5, 0 if op == 2 else 7) ^ ((3 ^ size) << 12) for op in (0, 1, 2, 3, 8) for size in range(8) if size != 3}
    invalid.update(amo(op, 6, 5, 7) for op in range(32) if op not in (0, 1, 2, 3, 8))
    invalid.update(amo(2, 6, 5, rs) for rs in (1, 31))
    cases += tuple((word, 0, 0, 0) for word in sorted(invalid))
    cases += ((alu(6, 5, 32, 1, True, True), 0, 0, 0), (alu(6, 5, 64, 1, immediate=True), 0, 0, 0), (csr(6, 0x340, 5, function=4), 0, 0, 0))
    cases += tuple((0x0072b32f | (ordering << 25), 1, 1, 1) for ordering in range(4))
    cases += tuple((fence(instruction, reserved), 0, 0, 0) for instruction in (False, True)
                   for reserved in (0, 0x83328880, 0xffff8f80))
    cases += ((0x200f, 0, 0, 0), (0x700f, 0, 0, 0))
    body = '    input_valid = 1; output_ready = 1;\n'
    for word, rs1, rs2, rd in cases:
        serial = int((word & 127 == 0x73 and (word >> 12) & 7 in (1, 2, 3, 5, 6, 7)) or word in (0x30200073, 0x10500073) or word == 0x10200073 and parameters.get('enableSupervisorMode') or word & 0x707f in (0x0f, 0x100f))
        body += (f"    input_bits_instruction = 32'h{word:08x};\n"
                 f'    check(output_valid && input_ready && output_bits_usesRs1 == {rs1} && output_bits_usesRs2 == {rs2} && output_bits_writesRd == {rd} && output_bits_serializing == {serial}, "Decode dependency metadata {word:08x}");\n')
        if word in extra or word in invalid:
            body += f'    check(output_bits_operation == {extra.get(word, 0)}, "Scalar operation class {word:08x}");\n'
    if parameters.get('virtualAddressBits') == 39:
        for rs1, rs2 in ((0, 0), (1, 0), (0, 31), (31, 31)):
            word = 0x12000073 | (rs1 << 15) | (rs2 << 20)
            body += f'''    input_bits_instruction = 32'h{word:x};
    check(output_bits_operation == 16 && output_bits_serializing && !output_bits_usesRs1 && !output_bits_usesRs2 && !output_bits_writesRd, "Full local SFENCE accepts standard selectors");
'''
        for word in (0x120000f3, 0x12001073, 0x14000073):
            body += f"    input_bits_instruction = 32'h{word:x}; check(output_bits_operation != 16, \"SFENCE requires its complete standard encoding\");\n"
    return body + '''    input_bits_instruction = 32'h00728333; input_bits_fault = 1;
    check(!output_bits_usesRs1 && !output_bits_usesRs2 && !output_bits_writesRd, "Faulting instruction dependencies");
    input_bits_instruction = 32'h34029373;
    check(!output_bits_usesRs1 && !output_bits_writesRd && !output_bits_serializing, "Faulting CSR serialization");
    input_bits_instruction = 32'h0000100f;
    check(!output_bits_usesRs1 && !output_bits_usesRs2 && !output_bits_writesRd && !output_bits_serializing, "Faulting instruction synchronization");
'''


def execute_contract():
    config = dict(resetVector='0', physicalAddressBits=56, pmpEntries=0, enableInterrupts=True,
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
    for operation in (0, 1, 2, 3, 8):
        for order in range(4):
            body += f'''    input_bits_decoded_operation = {15 if operation == 0 else 30}; input_bits_decoded_immediate = 0;
    input_bits_decoded_instruction_instruction = 32'h{amo(operation, 6, 1, 0 if operation == 2 else 2, order):x};
    input_bits_decoded_writesRd = 1; input_bits_operand1 = 'h1000; input_bits_operand2 = 64'h{0 if operation == 2 else MASK:x};
    check(output_valid && output_bits_atomic && output_bits_load == {int(operation != 3)} && output_bits_store == {int(operation != 2)} && output_bits_memorySize == 3 && output_bits_address == 'h1000 && output_bits_storeData == 64'h{0 if operation == 2 else MASK:x}, "Doubleword atomic execution metadata");
'''
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
    ram_atomic = any(r.get('atomic', False) and int(r['base']) <= base + 0x1000 < int(r['base']) + int(r['size'])
                     for r in parameters['memoryRegions'])
    cases += ((0x1000, 3, 1, 0, 255, 1, ram_atomic),
              (0x1000, 3, 0, 0, 255, 1, False), (0x1000, 3, 1, 1, 255, 1, False),
              (0x1000, 2, 1, 0, 15, 1, False), (0x1000, 3, 1, 0, 127, 1, False),
              (0x1001, 3, 1, 0, 255, 1, False), (0x4000, 3, 1, 0, 255, 1, False),
              (0x5000, 3, 1, 0, 255, 1, False), (0x7000, 3, 1, 0, 255, 1, False),
              (0x8000, 3, 1, 0, 255, 1, False))
    cases = tuple((*case[:-1], 0, 0, case[-1]) for case in cases)
    cases += tuple((0x1000, 3, int(op != 2), 0, 0 if op == 2 else 255, 1, op, int(op == 3), ram_atomic) for op in (1, 2, 3, 8))
    cases += ((0x1000, 3, 1, 0, 255, 1, 3, 0, ram_atomic),
              (0x1000, 3, 1, 0, 255, 1, 2, 0, False), (0x1000, 3, 0, 0, 0, 1, 3, 1, False))
    cases += tuple((0x1000, 3, 1, 0, 255, 1, op, 0, False) for op in (4, 5, 12, 16, 20, 24, 28))
    cases += tuple((0x1000, 2, int(op != 2), 0, 0 if op == 2 else 15, 1, op, 0, False) for op in (1, 2, 3, 8))
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


def axi_contract(width, harts):
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
    return body + axi_atomic_contract(width) + axi_reservation_contract(width, harts)


def axi_atomic_contract(width):
    lane = width // 8 - 8
    shift = lane * 8
    body = ''
    cases = ((1, 0, 1, 0, 0, False), (1, 0, 1, 0, 2, False),
             (0, 0, 1, 0, 0, False), (2, 0, 1, 0, 0, False),
             (3, 0, 1, 0, 0, False), (1, 1, 1, 0, 0, False),
             (1, 0, 2, 0, 0, False), (1, 0, 3, 0, 0, False),
             (1, 0, 1, 1, 0, False), (1, 0, 0, 1, 0, False),
             (1, 0, 1, 0, 0, True))
    cases = tuple((0, *case) for case in cases) + tuple((op, 1, 0, 1, 0, retries, False) for op in (1, 8) for retries in (0, 2))
    for index, (operation, read_resp, read_id, write_resp, write_id, retries, malformed) in enumerate(cases):
        body += f'''
    memory_request_bits_atomic = 1; memory_request_bits_write = 1; memory_request_bits_atomicOperation = {operation};
    memory_request_bits_address = 'h{0x1000 + lane:x}; memory_request_bits_size = 3;
    memory_request_bits_mask = 255; memory_request_bits_data = 5; memory_request_bits_tag = 201;
    memory_request_valid = 1; tick(); memory_request_valid = 0;
    memory_request_bits_atomic = 0; memory_request_bits_data = 99; memory_request_bits_address = 0;
'''
        fault = read_resp != 1 or read_id != 0 or write_resp != 1 or write_id != 0 or malformed
        for attempt in range(retries + 1):
            old = ((1 << 64) - 3 + attempt * 11) & ((1 << 64) - 1)
            value = atomic_value(operation, old, 5, 8)
            body += f'''
    repeat (3) begin
      check(axi_ar_valid && !axi_aw_valid && !axi_w_valid && !memory_response_valid && !memory_request_ready && axi_ar_bits_lock && axi_ar_bits_addr == 'h{0x1000 + lane:x} && axi_ar_bits_id == 0 && axi_ar_bits_len == 0 && axi_ar_bits_size == 3, "Exclusive read ownership"); tick();
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
      check(axi_aw_valid && axi_w_valid && !axi_ar_valid && !memory_response_valid && !memory_request_ready && axi_aw_bits_lock && axi_aw_bits_addr == 'h{0x1000 + lane:x} && axi_aw_bits_id == 0 && axi_aw_bits_len == 0 && axi_aw_bits_size == 3 && axi_w_bits_data == 'h{value << shift:x} && axi_w_bits_strb == 'h{255 << lane:x} && axi_w_bits_last, "Exclusive sum and captured operand"); tick();
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


def instruction_cache_contract(parameters):
    base = int(parameters['resetVector'])
    burst = parameters.get('enableBurstRefill')
    banks = 1 << (parameters['issueWidth'] - 1).bit_length()
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
    banks = 1 << (parameters['issueWidth'] - 1).bit_length()
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


def data_cache_contract(parameters):
    region = next(r for r in parameters['memoryRegions'] if r.get('dataCacheable'))
    base, size = int(region['base']), parameters['dCacheBytes']
    assert int(region['size']) >= 2 * size
    fields = dict(address=64, data=64, size=3, mask=8, tag=8, write=1, fetch=1,
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
            body += f"    invalidate_bits = 64'h{address:x}; invalidate_valid = 1;\n"
        return body + '    #1; while (!upstream_request_ready) tick(); tick(); upstream_request_valid = 0; invalidate_valid = 0;\n'

    def invalidate(address):
        return f'''    invalidate_bits = 64'h{address:x}; invalidate_valid = 1;
    check(invalidate_ready, "Invalidation must not wait for local or physical service");
    tick(); invalidate_valid = 0;
'''

    def bus(value, fault=0, wrong_tag=False, invalidation=None, expanded=False, fallback=False):
        body = '''    while (!downstream_request_valid) begin check(!upstream_response_valid, "Miss completed before physical service"); tick(); end
    repeat (3) begin
'''
        physical = dict(current, address=current['address'] & ~7, size=3) if expanded else dict(current)
        if fallback:
            physical['refillSize'] = 0
        body += '      check(' + ' && '.join(f"downstream_request_bits_{key} == {fields[key]}'h{value:x}" for key, value in physical.items())
        body += ', "Captured request payload changed"); tick();\n    end\n'
        if invalidation == 'held':
            body += invalidate(current['address'])
        body += '    downstream_request_ready = 1; tick(); downstream_request_ready = 0;\n'
        if invalidation == 'waiting':
            body += invalidate(current['address'])
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

    body = request(base) + bus(0x123456789abcdef0) + reply(0x123456789abcdef0)
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
        values = tuple(0xfedcba9876543210 ^ (0x0101010101010101 * word) for word in range(8))

        def line(fault=-1, wrong_tag=-1, chunks=8, invalidation=None):
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
    downstream_response_bits_data = 64'h{values[chunk % 8]:x}; downstream_response_bits_tag = {current['tag'] ^ int(chunk == wrong_tag)};
    downstream_response_bits_fault = {int(chunk == fault)}; downstream_response_bits_last = {int(chunk == chunks - 1)};
    downstream_response_valid = 1; check(downstream_response_ready, "Line response ownership");
'''
                body += invalidate(current['address']) if invalidation == chunk else '    tick();\n'
                body += '    downstream_response_valid = 0; downstream_response_bits_fault = 0;\n'
            return body

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
    return body


def coherence_contract(parameters):
    count = parameters['hartCount']
    base = int(next(r for r in parameters['memoryRegions'] if r.get('dataCacheable'))['base'])
    body = ''
    for case, (write, atomic, operation, cacheable) in enumerate(((1, 0, 0, True), (1, 0, 0, True), (1, 1, 0, True),
                                               (1, 1, 3, True), (0, 1, 2, True), (0, 0, 0, True),
                                               (1, 0, 0, False))):
        writer = 0 if case == 0 else count - 1
        address = base if cacheable else 1 << parameters['physicalAddressBits']
        body += f'''    @(negedge clock);
    hartId = {writer}; upstream_request_bits_address = 64'h{address:x}; upstream_request_bits_tag = 37;
    upstream_request_bits_size = 3; upstream_request_bits_mask = {255 if write else 0};
    upstream_request_bits_write = {write}; upstream_request_bits_atomic = {atomic};
    upstream_request_bits_atomicOperation = {operation}; upstream_request_bits_data = 19;
    upstream_request_valid = 1; downstream_request_ready = 0;
'''
        if write and cacheable:
            body += '    tick();\n'
            targets = [hart for hart in range(count) if atomic or hart != writer]
            for hart in targets:
                for peer in range(count):
                    body += f'''    check(invalidate_{peer}_valid == {int(peer in targets and peer >= hart)} && (!invalidate_{peer}_valid || invalidate_{peer}_bits == 64'h{address:x}), "Invalidation identity and one completion per target");
'''
                body += f'''    check(!downstream_request_valid && !upstream_request_ready, "Write forwarded before every invalidation completed");
    invalidate_{hart}_ready = 1; tick(); invalidate_{hart}_ready = 0;
'''
        else:
            body += '    #1;\n' + ''.join(f'    check(!invalidate_{hart}_valid, "Bypass generated invalidation");\n' for hart in range(count))
        body += ''.join(f'    check(!invalidate_{hart}_valid, "Completed write has no pending invalidation");\n' for hart in range(count))
        body += f'''    repeat (3) begin
      check(downstream_request_valid && downstream_request_bits_address == 64'h{address:x} && downstream_request_bits_tag == 37 && downstream_request_bits_write == {write} && downstream_request_bits_atomic == {atomic} && downstream_request_bits_atomicOperation == {operation} && !upstream_request_ready, "Forwarded request retention"); tick();
    end
    downstream_request_ready = 1; tick(); downstream_request_ready = 0; upstream_request_valid = 0;
    downstream_response_bits_tag = 37; downstream_response_bits_data = 23; downstream_response_valid = 1;
    repeat (3) begin
      check(upstream_response_valid && upstream_response_bits_tag == 37 && upstream_response_bits_data == 23 && !downstream_response_ready, "Shared response retention"); tick();
    end
    upstream_response_ready = 1; tick(); upstream_response_ready = 0; downstream_response_valid = 0;
'''
    return body


def line_read_window(parameters, expected_peak=None, fault_beat=-1, terminal='normal', stalls=False):
    data = parameters.get('dCacheRefillBytes') == 64
    if not data and not parameters.get('enableBurstRefill'):
        return ''
    width, harts = parameters['axiDataBits'], parameters['hartCount']
    base = int(next(r['base'] for r in parameters['memoryRegions'] if not r['device'] and
                   (r['readable'] and r.get('dataCacheable') if data else r['executable'])))
    count = min(harts, 4)
    identities = (*range(count - 1), harts - 1)
    ports = tuple(2 * hart + int(data) for hart in identities)
    if expected_peak is None:
        expected_peak = min(count, parameters.get('fabricReadSlots') or 2)
    target, beats, slices = expected_peak - 1, 512 // width, width // 64
    lengths = [slices if n == target and terminal == 'early' else 9 if n == target and terminal == 'late' else 8 for n in range(count)]
    body = f'''    reset = 1; tick(); reset = 0; tick();
    begin
      integer cycles, peak, selected, id, expected, delay[{count}], sent[{count}], received[{count}];
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
        ports_{port}_request_bits_size = 6; ports_{port}_request_bits_fetch = {int(not data)};
        ports_{port}_request_bits_write = 0; ports_{port}_request_bits_atomic = 0;
        ports_{port}_request_bits_tag = {71 + n}; ports_{port}_response_ready = {'cycles % 5 != 0' if stalls else '1'};
'''
    body += f'''        if (!holding) begin
          r_valid = 0;
          for (integer n = {count-1}; n >= 0; n--) if (live[n] && delay[n] == 0) begin
            selected = n; r_valid = 1;
          end
          if (r_valid) begin
            r_bits_id = selected == {count-1} ? {harts - 1} : selected; r_bits_resp = selected == {target} && sent[selected] == {fault_beat} ? 2 : 0;
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
          id = ar_bits_id == {harts - 1} ? {count-1} : integer'(ar_bits_id);
          if (id >= {count} || !accepted[id] || issued[id] || ar_bits_id != (id == {count-1} ? {harts - 1} : id) ||
              ar_bits_addr != 64'h{base + 0x100:x} + 64 * id || ar_bits_len != {512 // width - 1} ||
              ar_bits_size != {int(width // 8).bit_length() - 1}) $fatal(1, "Line window address identity");
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
      check(ar_bits_id == {0 if n == 0 else harts - 1} && ar_bits_addr == 64'h{base + 0x100 + 64 * n:x} && ar_bits_len == {beats - 1 if size == 6 else 0} && ar_bits_size == {int(width // 8).bit_length() - 1 if size == 6 else size}, "Concurrent line AR stable before any R"); tick();
    end
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
                body += f'''    r_bits_id = {0 if n == 0 else harts - 1}; r_bits_data = {width}'h{value:x};
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
            body += f'''    r_bits_id = 0; r_bits_resp = 0; r_bits_last = 0; r_valid = 1; #1;
    while (!r_ready) tick(); tick(); r_valid = 0;
    check(!ports_{port}_response_valid && !empty, "Overlong line drains without extra chunks");
    r_bits_last = 1; r_valid = 1; tick(); r_valid = 0;
    while (!ports_{port}_response_valid) tick();
    check(ports_{port}_response_bits_fault && ports_{port}_response_bits_last && ports_{port}_response_bits_tag == 91, "Overlong line terminates with owned error");
    ports_{port}_response_ready = 1; tick(); ports_{port}_response_ready = 0;
'''
        body += '    check(empty, "Both interleaved transactions consumed");\n'
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
    repeat (3) begin check(ar_bits_id == {hart} && ar_bits_addr == 64'h{address:x} && ar_bits_len == 0 && !ports_{port-1}_request_ready, "Serial AR stability and hart exclusion"); tick(); end
    ar_ready = 1; tick(); ar_ready = 0;
'''
                if mode == 'unknown':
                    body += f'''    r_bits_id = {hart ^ 1}; r_valid = 1; tick(); r_valid = 0;
    check(!ports_{port}_response_valid && !empty, "Unknown RID cannot complete a real owner");
'''
                body += f'''    r_bits_id = {hart}; r_bits_data = 64'h123456789abcdef0; r_valid = 1;
'''
                if mode == 'late':
                    body += f'''    r_bits_last = 0; tick(); r_valid = 0;
    check(!ports_{port}_response_valid, "Unterminated short read retains ownership");
    r_bits_last = 1; r_valid = 1;
'''
                body += '    tick(); r_valid = 0;\n'
            body += f'''    repeat (3) begin
      check(ports_{port}_response_valid && ports_{port}_response_bits_tag == 59 && ports_{port}_response_bits_last &&
        ports_{port}_response_bits_fault == {int(mode != 'short')} && !ports_{port-1}_request_ready &&
        (ports_{port}_response_bits_fault || ports_{port}_response_bits_data == 64'h123456789abcdef0), "Serial completion identity, data and retention"); tick();
    end
    ports_{port}_response_ready = 1; tick(); ports_{port}_response_ready = 0;
    check(empty == {int(mode != 'unknown')}, "Serial release or sticky protocol containment");
    ports_{port}_request_bits_write = 0; ports_{port}_request_bits_atomic = 0;
'''
    return body + '    reset = 1; tick(); reset = 0; tick();\n'


def read_queue_contract(parameters):
    stress = ''.join(line_read_window(parameters, fault_beat=beat, stalls=True) for beat in range(512 // parameters['axiDataBits']))
    stress += line_read_window(parameters, terminal='late', stalls=True)
    if parameters['axiDataBits'] < 512:
        stress += line_read_window(parameters, terminal='early', stalls=True)
    if parameters.get('fabricReadSlots') == 1:
        return read_queue_serial_contract(parameters) + line_read_window(parameters) + stress
    base = int(parameters['memoryRegions'][0]['base'])
    last = 2*parameters['hartCount']-1
    hart = parameters['hartCount']-1
    width = parameters['axiDataBits']
    first_address, second_address = base+0x138, base+0x124
    first_data, second_data = 0x1122334455667788, 0x98765432
    body = f'''
        ports_1_request_bits_address = 64'h{first_address:x}; ports_1_request_bits_size = 3;
        ports_1_request_bits_tag = 17; ports_1_request_valid = 1;
        check(ports_1_request_ready, "First read acceptance"); tick(); ports_1_request_valid = 0;
        ports_{last}_request_bits_address = 64'h{second_address:x}; ports_{last}_request_bits_size = 2;
        ports_{last}_request_bits_tag = 34; ports_{last}_request_valid = 1;
        check(ports_{last}_request_ready, "Different hart overlap"); tick(); ports_{last}_request_valid = 0;
        ports_0_request_bits_address = 64'h{base+0x180:x}; ports_0_request_bits_size = 2;
        ports_0_request_bits_fetch = 1; ports_0_request_valid = 1;
        while (!ar_valid) tick();
        repeat (3) begin
          check(ar_bits_id == 0 && ar_bits_addr == 64'h{first_address:x} && ar_bits_len == 0 && !ports_0_request_ready, "First AR hold and hart ownership"); tick();
        end
        ar_ready = 1; tick(); ar_ready = 0;
        while (!ar_valid) tick();
        check(ar_bits_id == {hart} && ar_bits_addr == 64'h{second_address:x}, "Second AR before first response");
        ar_ready = 1; tick(); ar_ready = 0;
        r_bits_id = {hart}; r_bits_data = {width}'h{second_data << (8*(second_address%(width//8))):x}; r_bits_last = 1; r_valid = 1;
        check(r_ready, "Reordered return accepted"); tick(); r_valid = 0;
        repeat (3) begin
          check(ports_{last}_response_valid && ports_{last}_response_bits_data == 64'h{second_data:x} && ports_{last}_response_bits_tag == 34 && !ports_{last}_response_bits_fault && !ports_1_response_valid && !ports_0_request_ready && !empty, "Reordered response retained"); tick();
        end
        ports_{last}_response_ready = 1; tick(); ports_{last}_response_ready = 0;
        r_bits_id = 0; r_bits_data = {width}'h{first_data << (8*(first_address%(width//8))):x}; r_valid = 1;
        tick(); r_valid = 0;
        check(ports_1_response_valid && ports_1_response_bits_data == 64'h{first_data:x} && ports_1_response_bits_tag == 17 && !ports_1_response_bits_fault && !ports_0_request_ready, "First response identity");
        ports_1_response_ready = 1; tick(); ports_1_response_ready = 0;
        check(ports_0_request_ready && empty, "Hart released only after response consumption"); ports_0_request_valid = 0;
        ports_1_request_bits_address = 64'h{1<<parameters['physicalAddressBits']:x}; ports_1_request_bits_tag = 51; ports_1_request_valid = 1;
        tick(); ports_1_request_valid = 0;
        while (!ports_1_response_valid) begin check(!ar_valid, "PMA denial reached AXI"); tick(); end
        check(ports_1_response_bits_fault && ports_1_response_bits_tag == 51, "Local denial ownership");
        ports_1_response_ready = 1; tick(); ports_1_response_ready = 0;
        ports_{last}_request_bits_size = 3; ports_{last}_request_bits_address = 64'h{base+0x130:x}; ports_{last}_request_valid = 1;
        tick(); ports_{last}_request_valid = 0;
        while (!ar_valid) tick(); ar_ready = 1; tick(); ar_ready = 0;
        r_bits_id = {hart}; r_bits_last = 0; r_valid = 1; tick(); r_valid = 0;
        check(!ports_{last}_response_valid && r_ready, "Malformed response drains");
        r_bits_last = 1; r_valid = 1; tick(); r_valid = 0;
        check(ports_{last}_response_valid && ports_{last}_response_bits_fault, "Malformed response reports fault");
        ports_{last}_response_ready = 1; tick();
        check(empty, "Final ownership release");
    '''
    body += f'''    ports_{last}_response_ready = 0; r_bits_last = 1;
    ports_{last}_request_valid = 1; tick(); ports_{last}_request_valid = 0;
    while (!ar_valid) tick(); ar_ready = 1; tick(); ar_ready = 0;
    ports_1_request_bits_address = 64'h{first_address:x}; ports_1_request_valid = 1;
    tick(); ports_1_request_valid = 0; while (!ar_valid) tick();
    r_bits_id = 0; r_valid = 1; tick(); r_valid = 0;
    ports_1_request_valid = 1;
    repeat (3) begin check(!ports_1_request_ready && ar_valid && ar_bits_id == 0 && ar_bits_addr == 64'h{first_address:x} && !empty && !ports_{last}_response_valid, "Unknown RID preserves held AR and real owners"); tick(); end
    ar_ready = 1; tick(); ar_ready = 0;
    r_bits_id = {hart}; r_valid = 1; tick(); r_valid = 0;
    check(ports_{last}_response_valid && ports_{last}_response_bits_fault, "Known response drains after protocol fault");
    ports_{last}_response_ready = 1; tick(); ports_{last}_response_ready = 0;
    r_bits_id = 0; r_valid = 1; tick(); r_valid = 0;
    check(ports_1_response_valid && ports_1_response_bits_fault, "Previously held AR drains with owned fault");
    ports_1_response_ready = 1; tick(); ports_1_response_ready = 0;
    check(!empty && !ports_1_request_ready && !ar_valid, "Protocol fault blocks exclusive handover and ID reuse");
    ports_1_request_valid = 0; reset = 1; tick(); reset = 0; tick();
    check(empty, "Reset clears protocol containment");
'''
    return body + line_read_contract(parameters) + stress


def fabric_contract(parameters):
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
    tick(); data_request_valid = 0; instruction_request_valid = {int(parameters["hartCount"] == 1)};
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
    check(axi_ar_bits_addr == 'h{instruction_address:x} && axi_ar_bits_prot == 5 && axi_ar_bits_id == {parameters['hartCount'] - 1}, "Instruction ownership");
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    axi_r_bits_data = 'h{instruction_value << instruction_shift:x}; axi_r_bits_id = {parameters['hartCount'] - 1}; axi_r_valid = 1;
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
    if parameters['hartCount'] > 1:
        overlap = read_queue_contract(parameters)
        overlap = re.sub(r'\bports_(\d+)_', lambda m: f'{"instruction" if int(m[1]) % 2 == 0 else "data"}_{int(m[1]) // 2}_', overlap)
        overlap = re.sub(r'\b(ar|r)_', r'axi_\1_', overlap).replace('empty', 'dut.readers.empty')
        body += '    axi_r_bits_resp = 0;\n' + overlap
        body += fabric_exclusive_contract(parameters)
    return body


def fabric_exclusive_contract(parameters):
    hart = parameters['hartCount'] - 1
    base = int(next(r['base'] for r in parameters['memoryRegions'] if r['writable'] and not r['device']))
    depth = parameters.get('fabricReadSlots') or 2
    identities = (*range(depth - 1), hart)
    body = '    axi_r_bits_resp = 0; axi_r_bits_last = 1;\n'
    for index, reader in enumerate(identities):
        body += f'''    data_{reader}_request_bits_write = 0; data_{reader}_request_bits_atomic = 0; data_{reader}_request_bits_fetch = 0;
    data_{reader}_request_bits_address = 'h{base+0x100+8*index:x}; data_{reader}_request_bits_size = 3;
    data_{reader}_response_ready = 0; data_{reader}_request_valid = 1; #1;
    while (!data_{reader}_request_ready) tick(); tick(); data_{reader}_request_valid = 0;
'''
    body += f'''    repeat ({depth}) begin while (!axi_ar_valid) tick(); axi_ar_ready = 1; tick(); axi_ar_ready = 0; end
    data_0_request_bits_address = 'h{base+0x200:x}; data_0_request_bits_size = 3;
    data_0_request_bits_write = 1; data_0_request_bits_atomic = 0; data_0_request_bits_fetch = 0; data_0_request_bits_mask = 255;
    data_0_request_bits_data = 17; data_0_request_bits_tag = 85; data_0_request_valid = 1;
    instruction_{hart}_request_bits_address = 'h{base+0x180:x};
    instruction_{hart}_request_bits_size = 2; instruction_{hart}_request_valid = 1;
    repeat (3) begin
      check(!data_0_request_ready && !instruction_{hart}_request_ready && !axi_aw_valid && !axi_w_valid, "Exclusive request waits for all accepted reads"); tick();
    end
'''
    for reader in identities[:-1]:
        body += f'''    axi_r_bits_id = {reader}; axi_r_valid = 1; tick(); axi_r_valid = 0;
    data_{reader}_response_ready = 1; tick(); data_{reader}_response_ready = 0;
    check(!data_0_request_ready && !axi_aw_valid && !axi_w_valid, "Partial drain cannot release exclusive traffic");
'''
    body += f'''    axi_r_bits_id = {hart}; axi_r_valid = 1; tick(); axi_r_valid = 0;
    repeat (3) begin
      check(data_{hart}_response_valid && !data_0_request_ready && !axi_aw_valid && !axi_w_valid, "Exclusive request waits for held read response"); tick();
    end
    data_{hart}_response_ready = 1; tick(); data_{hart}_response_ready = 0;
    check(data_0_request_ready && !instruction_{hart}_request_ready, "Waiting writer precedes another read");
    tick(); data_0_request_valid = 0;
'''
    if parameters.get('dCacheBytes'):
        body += ''.join(f'    invalidate_{i}_ready = 1;\n' for i in range(parameters['hartCount']))
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
    check(axi_ar_bits_id == {hart}, "Post-write read identity");
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    axi_r_bits_id = {hart}; axi_r_valid = 1; tick(); axi_r_valid = 0;
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
    while (!axi_aw_valid || !axi_w_valid) tick();
    axi_aw_ready = 1; axi_w_ready = 1; tick(); axi_aw_ready = 0; axi_w_ready = 0;
    axi_b_bits_id = {hart}; axi_b_bits_resp = 0; axi_b_valid = 1;
    while (!axi_b_ready) tick(); tick(); axi_b_valid = 0;
    while (!data_{hart}_response_valid) tick();
    check(data_{hart}_response_bits_tag == 94 && !data_{hart}_response_bits_fault, "Waiting write completes after line release");
    data_{hart}_response_ready = 1; tick(); data_{hart}_response_ready = 0;
'''
    return body


def multiply_contract():
    edges = (0, 1, 2, (1 << 64) - 1, 1 << 63, (1 << 63) - 1, 1 << 32, 0xaaaaaaaa55555555)
    rng = random.Random(2026)
    pairs = [(a, b) for a in edges for b in edges]
    pairs += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(32)]
    body = ''
    for a, b in pairs:
        body += f'''
    input_bits_operand1 = 64'h{a:x}; input_bits_operand2 = 64'h{b:x}; input_valid = 1;
    check(input_ready && !output_valid, "Multiply resource reuse"); tick();
    input_bits_operand1 = ~input_bits_operand1; input_bits_operand2 = ~input_bits_operand2;
    for (integer cycles = 0; !output_valid; cycles++) begin
      check(!input_ready && cycles < 64, "Multiply acceptance or completion bound"); tick();
    end
    input_valid = 0;
    repeat (3) begin
      check(!input_ready && output_valid && output_bits == 64'h{(a * b) & ((1 << 64) - 1):x}, "Multiply value and held completion"); tick();
    end
    output_ready = 1; tick(); output_ready = 0;
'''
    return body


def backend_multiply_contract():
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
    while (!dut.multiply.output_valid) tick();
    repeat (3) begin
      check(data_request_valid && data_request_bits_write && data_request_bits_tag == 10 &&
        dut.executePending && dut.issuedValid && !dut.multiply.input_valid &&
        dut.multiply.output_valid && dut.multiply.output_bits == 1, "Blocked multiply retains owner and destination"); tick();
    end
''' + complete + send((sd(5, 0),), 0x200, 20) + '''
    while (!data_request_valid) tick();
    check(data_request_bits_write && data_request_bits_data == 2, "Dependent instruction used a stale multiply result");
''' + complete
    for held in (False, True):
        body += reset + setup
        words = (0x00003303 if held else 0x73, mul(4, 2, 3), sd(2, 0))
        body += send(words, 0x180, 10)
        if held:
            body += '''
    while (!data_request_valid || dut.multiply.multiplier != 7) tick();
    check(dut.executePending && !dut.multiply.output_valid, "Fault response did not precede multiply completion");
    data_request_ready = 1; tick(); data_request_ready = 0;
    data_response_bits_tag = 10; data_response_bits_fault = 1; data_response_valid = 1;
    tick(); data_response_valid = 0; data_response_bits_fault = 0;
'''
        body += f'''
    while (!redirect) begin check(!data_request_valid, "Younger store escaped before redirect"); tick(); end
    check(dut.executePending && dut.multiply.{'valid' if held else 'busy'}, "Redirect did not overlap the multiply operation");
    tick();
    check(!dut.issuedValid && !data_request_valid, "Redirect retained a younger effect");
'''
        body += send((addi(5, 4, 7), sd(5, 0)), 0x200, 20) + '''
    while (!data_request_valid) tick();
    check(data_request_bits_write && data_request_bits_data == 7 && data_request_bits_tag == 21,
      "Cancelled multiply wrote its destination or polluted slot reuse");
''' + complete
    return body


def backend_contract():
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
''' + backend_multiply_contract()


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
    instruction_bits_packets_1_pc = 'h204; instruction_bits_packets_1_instruction = 'h{mul(3, 1, 1):x};
    instruction_bits_packets_1_length = 4; instruction_bits_packets_1_fault = 0;
    instruction_valid = 1; while (!instruction_ready) tick(); tick(); instruction_valid = 0;
    while (dut.commitCount == 0 || !dut.commitPackets_0_wfi) tick();
    tick(); check(status_sleep && dut.executePending && dut.resumePc == 'h204, "WFI cancels younger multiply and retains resume PC");
    repeat (8) begin check(status_sleep && !instruction_ready && !data_request_valid, "Sleep drains owned execution"); tick(); end
    check(!dut.executePending, "Cancelled multiply drained");
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


def bench(module, body):
    header = module.read_text().split(');', 1)[0].split('(', 1)[1]
    declarations, connections, names = [], [], []
    direction, width = None, ''
    for item in header.split(','):
        match = re.fullmatch(r'\s*(?:(input|output)\s+)?(\[\d+:\d+\])?\s*(\w+)\s*', item)
        assert match, item
        new_direction, new_width, name = match.groups()
        if new_direction:
            direction, width = new_direction, new_width or ''
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
  initial begin #100000; $fatal(1, "Timeout"); end
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
    readAddress = 'h341; check(readData == 'h120, "Trap PC alignment");
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
    flush = '    invalidate = 1; tick(); invalidate = 0; tick();\n' if parameters.get('tlbEntries') else ''
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
        if parameters.get('tlbEntries') and reads and not fault:
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
    if parameters.get('tlbEntries'):
        for walking in range(2):
            hit = 1 - walking
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
    body += '''    state_satp = 0; ports_0_request_bits_address = 'h40; ports_0_request_bits_fetch = 1;
    ports_1_request_bits_address = 'h80; ports_0_request_valid = 1; ports_1_request_valid = 1;
    ports_0_response_ready = 1; ports_1_response_ready = 1;
    #1; check(ports_0_request_ready && ports_1_request_ready && ports_0_response_valid && ports_1_response_valid &&
      ports_0_response_bits_address == 'h40 && ports_1_response_bits_address == 'h80 && !memory_request_valid,
      "Independent simultaneous Bare translations");
    tick(); ports_0_response_ready = 0; ports_1_response_ready = 0;
    tick(); ports_0_request_valid = 0; ports_1_request_valid = 0; state_satp = '1; cancelInstruction = 1;
'''
    body += '    invalidate = 1;\n' if parameters.get('tlbEntries') else ''
    body += '''    repeat (3) begin
      check(ports_0_response_valid && ports_1_response_valid && ports_0_response_bits_address == 'h40 &&
        ports_1_response_bits_address == 'h80 && !ports_0_response_bits_fault && !ports_1_response_bits_fault &&
        !ports_0_request_ready && !ports_1_request_ready, "Accepted responses survive context change and cancellation"); tick();
    end
    ports_0_response_ready = 1; ports_1_response_ready = 1; tick(); cancelInstruction = 0;
'''
    body += '    invalidate = 0;\n' if parameters.get('tlbEntries') else ''
    return body


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
    check(data_request_bits_data == 0 && data_request_bits_address == 'h1000, "Younger multiply wrote a destination");
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


def verify(rtl, directory, modules=None):
    directory.mkdir(parents=True, exist_ok=True)
    parameters = json.loads((rtl / 'ditdah_a1_config.json').read_text())['parameters']
    verified = []
    enabled = parameters['pmpEntries'] != 0
    cached = bool(parameters['iCacheBytes'])
    suites = (('DitDahA1Fetch', (burst_fetch_contract(parameters) if parameters.get('enableBurstRefill') else cached_fetch_contract(parameters)) if cached else FETCH + (protection_contract(True) if enabled else '')),
                       ('DitDahA1Lsu', LSU + lsu_reservation_contract(parameters) + (protection_contract(False) if enabled else '') + lsu_refill_contract(parameters)),
                       ('DitDahA1Multiply', multiply_contract()),
                       ('DitDahA1Frontend', (burst_fetch_contract(parameters, True) if parameters.get('enableBurstRefill') else cached_fetch_contract(parameters, True)) if cached else frontend_contract(parameters)),
                       ('DitDahA1Decode', decode_contract(parameters)),
                       ('DitDahA1Execute', execute_contract()),
                       ('DitDahA1Backend', backend_contract() + backend_fence_contract() + (backend_protection_contract() if enabled else '') +
                        (backend_interrupt_contract() if parameters['enableInterrupts'] else '')),
                       ('DitDahA1MemoryArbiter', arbiter_contract(parameters)),
                       ('DitDahA1Memory', memory_contract(parameters)),
                       ('DitDahA1Axi', axi_contract(parameters['axiDataBits'], parameters['hartCount']) +
                        (burst_axi_contract(parameters) if parameters.get('enableBurstRefill') else '') +
                        (burst_axi_contract(parameters, False) if parameters.get('dCacheRefillBytes') == 64 else '')),
                       ('DitDahA1MemoryFabric', fabric_contract(parameters)))
    if parameters['hartCount'] > 1:
        suites += (('DitDahA1ReadQueue', read_queue_contract(parameters)),)
    if cached:
        suites += (('DitDahA1InstructionCache', instruction_cache_contract(parameters)),)
    if parameters.get('localInterruptBase'):
        suites += (('DitDahA1LocalInterrupts', local_interrupt_contract(parameters)),)
    if parameters.get('dCacheBytes'):
        suites += (('DitDahA1DataCache', data_cache_contract(parameters)),
                   ('DitDahA1Coherence', coherence_contract(parameters)))
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
                       if name in ('DitDahA1Fetch', 'DitDahA1Frontend', 'DitDahA1Lsu') else '')) for name, body in suites)
    if parameters.get('virtualAddressBits') == 39:
        suites = tuple((name, body) for name, body in suites if name not in
                       ('DitDahA1Fetch', 'DitDahA1Frontend', 'DitDahA1Lsu', 'DitDahA1Backend'))
        suites += (('DitDahA1Translation', translation_contract(parameters)),)
        suites += (('DitDahA1Fetch', translated_consumer_contract(parameters, True)),
                   ('DitDahA1Lsu', translated_consumer_contract(parameters, False) + lsu_refill_contract(parameters)))
        suites += (('DitDahA1Frontend', frontend_group_contract(parameters)),)
    if cached and parameters['issueWidth'] > 1:
        suites = tuple((name, body + (wide_fetch_contract(parameters) if name == 'DitDahA1Fetch' else '')) for name, body in suites)
    suites = tuple((name, (body if parameters['issueWidth'] == 1 and parameters.get('virtualAddressBits') != 39 else '') + frontend_group_contract(parameters)
                    if name == 'DitDahA1Frontend' else body) for name, body in suites)
    assert not modules or set(modules) <= {name for name, _ in suites}, 'Unsupported contract selection'
    for name, body in suites:
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
                body += backend_group_contract(parameters) + backend_branch_contract() + backend_memory_group_contract(parameters)
        test.write_text(bench(module, body))
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
            if parameters['hartCount'] > 1:
                dependencies.append(rtl / 'DitDahA1ReadQueue.sv')
        if name == 'DitDahA1DataCache':
            dependencies = [rtl / file for file in (rtl / 'filelist.f').read_text().splitlines()
                            if file.startswith(('data_', 'dataTags_', 'mem_'))]
        if name == 'DitDahA1Backend':
            dependencies = [rtl / ('DitDahA1' + child + '.sv') for child in ('Decode', 'Issue', 'Execute', 'Multiply', 'Commit', 'Gpr', 'Csr', 'Lsu')]
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
    return verified
