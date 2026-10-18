# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Exercise cancellation, authorization and backpressure on unit interfaces."""

from pathlib import Path
import json
import re
import random
import subprocess

from programs import addi, csr, sd, mul, ld, fence
from model import Model, pmp_allowed


def verify_storage(rtl, directory):
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    size = manifest['implementation']['iCacheBytes']
    files = (rtl / 'filelist.f').read_text().splitlines()
    arrays = [file for file in files if file.startswith(('instructions_', 'tags_'))]
    assert ('DitDahA1InstructionCache.sv' in files) == bool(size)
    expected = {} if not size else {'instructions': (size // 4, 32),
        'tags': (size // 64, manifest['parameters']['physicalAddressBits'] - (size // 64).bit_length() - 5)}
    assert set(arrays) == {f'{name}_{depth}x{width}.sv' for name, (depth, width) in expected.items()}
    report = []
    directory.mkdir(parents=True, exist_ok=True)
    for name, (depth, width) in expected.items():
        module = f'{name}_{depth}x{width}'
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
    input_bits_load = 1; input_bits_store = 1; storeAllowed = 0;
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
    input_bits_load = 0; input_bits_store = 0;
'''


def arbiter_contract(parameters):
    count = 2 * parameters['hartCount']
    body = ''.join(f"    ports_{i}_request_valid = 1; ports_{i}_response_ready = 1;\n"
                   f"    ports_{i}_request_bits_address = {0x100 + 8*i};\n"
                   f"    ports_{i}_request_bits_data = {0x1000 + i};\n"
                   f"    ports_{i}_request_bits_tag = 7; ports_{i}_request_bits_size = 3;\n"
                   f"    ports_{i}_request_bits_mask = 255; ports_{i}_request_bits_write = {i % 2};\n"
                   f"    ports_{i}_request_bits_fetch = {1-i % 2}; ports_{i}_request_bits_atomic = {i % 2};\n" for i in range(count))
    no_ready = ' && '.join(f'!ports_{i}_request_ready' for i in range(count))
    for owner in list(range(count)) * 2:
        ready = ' && '.join(f'ports_{i}_request_ready == {int(i == owner)}' for i in range(count))
        response = ' && '.join(f'ports_{i}_response_valid == {int(i == owner)}' for i in range(count))
        body += f'''    check({ready}, "Round-robin service order"); tick();
    ports_{owner}_request_valid = 0; ports_{owner}_request_bits_address = 0;
    repeat (3) begin
      check(downstream_request_valid && downstream_request_bits_address == {0x100+8*owner} && downstream_request_bits_data == {0x1000+owner} && downstream_request_bits_tag == 7 && downstream_request_bits_size == 3 && downstream_request_bits_mask == 255 && downstream_request_bits_write == {owner % 2} && downstream_request_bits_fetch == {1-owner % 2} && downstream_request_bits_atomic == {owner % 2} && {no_ready}, "Captured request survives contention and backpressure"); tick();
    end
    ports_{owner}_request_bits_address = {0x100+8*owner}; ports_{owner}_request_valid = 1;
    downstream_request_ready = 1; tick(); downstream_request_ready = 0;
    downstream_response_valid = 1; downstream_response_bits_data = {0x2000+owner};
    downstream_response_bits_tag = 7; downstream_response_bits_fault = {owner % 2};
    ports_{owner}_response_ready = 0;
    repeat (3) begin
      check({response} && !downstream_response_ready && {no_ready} && ports_{owner}_response_bits_data == {0x2000+owner} && ports_{owner}_response_bits_tag == 7 && ports_{owner}_response_bits_fault == {owner % 2}, "Retained response owner with colliding tags"); tick();
    end
    ports_{owner}_response_ready = 1; tick(); downstream_response_valid = 0;
'''
    return body


def decode_contract():
    cases = ((0x12345337, 0, 0, 1), (0x12345317, 0, 0, 1),
             (0x12328313, 1, 0, 1), (0x00728333, 1, 1, 1),
             (0x00728463, 1, 1, 0), (0x0080036f, 0, 0, 1),
             (0x00428367, 1, 0, 1), (0x0082b303, 1, 0, 1),
             (0x0072b423, 1, 1, 0), (0x34029373, 1, 0, 1),
             (0x3402a373, 1, 0, 1), (0x00000073, 0, 0, 0),
             (0x30200073, 0, 0, 0), (0xffffffff, 0, 0, 0))
    cases += ((mul(6, 5, 7), 1, 1, 1), (mul(6, 5, 7) | (1 << 12), 0, 0, 0))
    cases += tuple((0x0072b32f | (ordering << 25), 1, 1, 1) for ordering in range(4))
    cases += tuple((fence(instruction, reserved), 0, 0, 0) for instruction in (False, True)
                   for reserved in (0, 0x83328880, 0xffff8f80))
    cases += ((0x200f, 0, 0, 0), (0x700f, 0, 0, 0))
    body = '    input_valid = 1; output_ready = 1;\n'
    for word, rs1, rs2, rd in cases:
        serial = int(word in (0x34029373, 0x3402a373, 0x30200073) or word & 0x707f in (0x0f, 0x100f))
        body += (f"    input_bits_instruction = 32'h{word:08x};\n"
                 f'    check(output_valid && input_ready && output_bits_usesRs1 == {rs1} && output_bits_usesRs2 == {rs2} && output_bits_writesRd == {rd} && output_bits_serializing == {serial}, "Decode dependency metadata {word:08x}");\n')
    return body + '''    input_bits_instruction = 32'h00728333; input_bits_fault = 1;
    check(!output_bits_usesRs1 && !output_bits_usesRs2 && !output_bits_writesRd, "Faulting instruction dependencies");
    input_bits_instruction = 32'h34029373;
    check(!output_bits_usesRs1 && !output_bits_writesRd && !output_bits_serializing, "Faulting CSR serialization");
    input_bits_instruction = 32'h0000100f;
    check(!output_bits_usesRs1 && !output_bits_usesRs2 && !output_bits_writesRd && !output_bits_serializing, "Faulting instruction synchronization");
'''


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
    body = ''
    for tag, (offset, size, write, fetch, mask, atomic, allowed) in enumerate(cases, 1):
        body += f'''    upstream_request_bits_address = 64'h{base + offset:x};
    upstream_request_bits_size = {size}; upstream_request_bits_write = {write};
    upstream_request_bits_fetch = {fetch}; upstream_request_bits_mask = {mask};
    upstream_request_bits_atomic = {atomic};
    upstream_request_bits_tag = {tag}; upstream_request_valid = 1;
    check(downstream_request_valid == {int(allowed)} && upstream_request_ready == {int(not allowed)}, "Memory permission and shape {tag}");
'''
        if allowed:
            body += f'''    repeat (3) begin
      check(downstream_request_valid && downstream_request_bits_tag == {tag} && downstream_request_bits_atomic == {atomic} && !upstream_request_ready, "Memory request backpressure {tag}");
      tick();
    end
    downstream_request_ready = 1; tick(); downstream_request_ready = 0;
    downstream_response_valid = 1; downstream_response_bits_tag = {tag};
    downstream_response_bits_data = 64'hfedcba9876543210;
'''
        else:
            body += '    tick();\n'
        body += f'''    upstream_request_valid = 0;
    repeat (3) begin
      check(upstream_response_valid && upstream_response_bits_fault == {int(not allowed)} && upstream_response_bits_tag == {tag} && !downstream_request_valid && !upstream_request_ready, "Memory response backpressure {tag}");
      tick();
    end
    upstream_response_ready = 1; tick(); upstream_response_ready = 0;
    downstream_response_valid = 0;
'''
    return body


def axi_contract(width):
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
    return body + axi_atomic_contract(width)


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
    for index, (read_resp, read_id, write_resp, write_id, retries, malformed) in enumerate(cases):
        body += f'''
    memory_request_bits_atomic = 1; memory_request_bits_write = 1;
    memory_request_bits_address = 'h{0x1000 + lane:x}; memory_request_bits_size = 3;
    memory_request_bits_mask = 255; memory_request_bits_data = 5; memory_request_bits_tag = 201;
    memory_request_valid = 1; tick(); memory_request_valid = 0;
    memory_request_bits_atomic = 0; memory_request_bits_data = 99; memory_request_bits_address = 0;
'''
        fault = read_resp != 1 or read_id != 0 or write_resp != 1 or write_id != 0 or malformed
        for attempt in range(retries + 1):
            old = ((1 << 64) - 3 + attempt * 11) & ((1 << 64) - 1)
            value = (old + 5) & ((1 << 64) - 1)
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
        body += f'''    redirect = 1; invalidate = 1; redirectPc = 'h{base + 0x100:x}; tick(); redirect = 0; invalidate = 0;
'''
        return body + refill(base + 0x100) + output(base + 0x100, "32'h10000000")
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


def fabric_contract(parameters):
    base, width = int(parameters['resetVector']), parameters['axiDataBits']
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
    tick(); data_request_valid = 0; instruction_request_valid = 1;
    while (!axi_ar_valid) tick();
    repeat (3) begin
      check(axi_ar_bits_addr == 'h{data_address:x} && axi_ar_bits_prot == 1 && !instruction_response_valid, "Data ownership under AXI backpressure"); tick();
    end
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    axi_r_bits_data = 'h{data_value << data_shift:x}; axi_r_bits_last = 1; axi_r_valid = 1;
    tick(); axi_r_valid = 0;
    repeat (3) begin
      check(data_response_valid && data_response_bits_tag == 34 && data_response_bits_data == 64'h{data_value:x} && !data_response_bits_fault && !instruction_response_valid && !axi_ar_valid, "Held data completion retains owner"); tick();
    end
    data_response_ready = 1; tick(); data_response_ready = 0;
    check(instruction_request_ready, "Instruction client did not recover");
    tick(); instruction_request_valid = 0;
    while (!axi_ar_valid) tick();
    check(axi_ar_bits_addr == 'h{instruction_address:x} && axi_ar_bits_prot == 5, "Instruction ownership");
    axi_ar_ready = 1; tick(); axi_ar_ready = 0;
    axi_r_bits_data = 'h{instruction_value << instruction_shift:x}; axi_r_valid = 1;
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
    axi_r_bits_resp = 2; axi_r_valid = 1; tick(); axi_r_valid = 0;
    repeat (3) begin
      check(data_response_valid && data_response_bits_fault && data_response_bits_tag == 68 && !instruction_response_valid, "Bus fault completion ownership"); tick();
    end
    data_response_ready = 1; tick(); data_response_ready = 0;
'''
    return body.replace('instruction_', f"instruction_{parameters['hartCount']-1}_").replace('data_request_', 'data_0_request_').replace('data_response_', 'data_0_response_')


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
    body = reset + setup + send((sd(3, 0), mul(4, 2, 3), addi(5, 4, 1)), 0x180, 10)
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
    body = '    instruction_bits_length = 4;\n'
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
    repeat (3) begin
      check(!instruction_ready && data_request_valid && data_request_bits_write && data_request_bits_address == 'h2000 && data_request_bits_data == 42 && data_request_bits_mask == 255 && data_request_bits_tag == 2, "Backend RAW dependencies and blocked store"); tick();
    end
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
        initial = " = '0" if direction == 'input' else ''
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
    for _ in range(320):
        configs = [rng.randrange(256) & 0x9f for _ in range(16)]
        addresses = [rng.choice((0, 0x400 + rng.randrange(16), (1 << width) - 1)) for _ in range(16)]
        tests.append((configs, addresses, rng.choice((0, 0x1000 + rng.randrange(64), (1 << pa) - 8)),
                      rng.randrange(4), rng.choice(('fetch', 'read', 'write', 'atomic'))))
    body = ''
    for configs, addresses, address, size, kind in tests:
        config = sum(v << (i * 8) for i, v in enumerate(configs))
        points = sum(v << (i * width) for i, v in enumerate(addresses))
        kinds = ('read', 'write') if kind == 'atomic' else (kind,)
        expected = int(all(pmp_allowed(configs, addresses, address, 1 << size, access, pa) for access in kinds))
        body += f'''    state_config = 128'h{config:x}; state_address = {16 * width}'h{points:x};
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
    return body + '''
    trap = 1; trapPc = 'h123; trapCause = 64'h800000000000000b; trapValue = 0; tick(); trap = 0;
    readAddress = 'h300; check(readData == 'h1880 && !interruptPending, "Entry masks interrupts");
    readAddress = 'h341; check(readData == 'h120, "Trap PC alignment");
    readAddress = 'h342; check(readData == 64'h800000000000000b, "Interrupt cause flag");
    readAddress = 'h343; check(readData == 0, "Interrupt trap value");
    mret = 1; tick(); mret = 0; readAddress = 'h300;
    check(readData == 'h1888 && interruptPending, "Return reevaluates held sources");
    interrupts_software = 0; interrupts_timer = 0; interrupts_external = 0;
    check(!interruptPending, "Source deassertion");
'''


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
    input_bits_instruction_fault = 0; input_bits_address = 'h100; input_bits_load = 1; input_bits_store = 0;
    input_valid = 1; tick(); input_valid = 0;
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


def verify(rtl, directory, modules=None):
    directory.mkdir(parents=True, exist_ok=True)
    parameters = json.loads((rtl / 'ditdah_a1_config.json').read_text())['parameters']
    verified = []
    enabled = parameters['pmpEntries'] != 0
    cached = bool(parameters['iCacheBytes'])
    suites = (('DitDahA1Fetch', cached_fetch_contract(parameters) if cached else FETCH + (protection_contract(True) if enabled else '')),
                       ('DitDahA1Lsu', LSU + (protection_contract(False) if enabled else '')),
                       ('DitDahA1Multiply', multiply_contract()),
                       ('DitDahA1Frontend', cached_fetch_contract(parameters, True) if cached else frontend_contract(parameters)),
                       ('DitDahA1Decode', decode_contract()),
                       ('DitDahA1Backend', backend_contract() + backend_fence_contract() + (backend_protection_contract() if enabled else '') +
                        (backend_interrupt_contract() if parameters['enableInterrupts'] else '')),
                       ('DitDahA1MemoryArbiter', arbiter_contract(parameters)),
                       ('DitDahA1Memory', memory_contract(parameters)),
                       ('DitDahA1Axi', axi_contract(parameters['axiDataBits'])),
                       ('DitDahA1MemoryFabric', fabric_contract(parameters)))
    if enabled:
        suites += (('DitDahA1Pmp', pmp_contract(parameters)),)
    identity = ''.join(f'''    hartId = {hart}; readAddress = 'hf14;
    check(legal && readData == {hart}, "Hart identity");
    writeAddress = 'hf14; writeData = '1; write = 1; tick(); write = 0;
    check(readData == {hart}, "Hart identity is read-only");
''' for hart in range(16)) + '    hartId = 0;\n'
    suites += (('DitDahA1Csr', identity + (csr_contract(parameters) if enabled else '') +
                (interrupt_csr_contract(parameters) if parameters['enableInterrupts'] else '')),)
    assert not modules or set(modules) <= {name for name, _ in suites}, 'Unsupported contract selection'
    for name, body in suites:
        if modules and name not in modules:
            continue
        module = rtl / (name + '.sv')
        test = directory / (name + '_tb.sv')
        test.write_text(bench(module, body))
        binary = directory / name
        dependencies = [rtl / 'DitDahA1Fetch.sv'] if name == 'DitDahA1Frontend' else []
        if cached and name in ('DitDahA1Fetch', 'DitDahA1Frontend'):
            dependencies.append(rtl / 'DitDahA1InstructionCache.sv')
            dependencies += [rtl / file for file in (rtl / 'filelist.f').read_text().splitlines()
                             if file.startswith(('instructions_', 'tags_'))]
        if name == 'DitDahA1MemoryFabric':
            dependencies = [rtl / (child + '.sv') for child in ('DitDahA1MemoryArbiter', 'DitDahA1Memory', 'DitDahA1Axi')]
        if name == 'DitDahA1Backend':
            dependencies = [rtl / ('DitDahA1' + child + '.sv') for child in ('Decode', 'Issue', 'Execute', 'Multiply', 'Commit', 'Gpr', 'Csr', 'Lsu')]
        if enabled and name in ('DitDahA1Fetch', 'DitDahA1Lsu', 'DitDahA1Frontend', 'DitDahA1Backend'):
            dependencies.append(rtl / 'DitDahA1Pmp.sv')
        subprocess.run(['iverilog', '-g2012', '-s', 'contract_tb', '-o', str(binary),
                        str(module), *map(str, dependencies), str(test)], check=True)
        result = subprocess.run(['vvp', str(binary)], capture_output=True, text=True, timeout=30)
        (directory / (name + '.log')).write_text(result.stdout + result.stderr)
        assert result.returncode == 0 and 'PASS' in result.stdout, result.stdout + result.stderr
        print(f'  {name} interface contracts passed', flush=True)
        verified.append(name)
    return verified
