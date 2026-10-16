# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Exercise cancellation, authorization and backpressure on unit interfaces."""

from pathlib import Path
import json
import re
import subprocess


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
'''


ARBITER = r'''
    instruction_request_valid = 1;
    instruction_request_bits_address = 64'h100;
    instruction_request_bits_size = 2;
    instruction_request_bits_fetch = 1;
    instruction_request_bits_tag = 8'h31;
    data_request_valid = 1;
    data_request_bits_address = 64'h1008;
    data_request_bits_data = 64'hfedcba9876543210;
    data_request_bits_size = 3;
    data_request_bits_mask = 8'hff;
    data_request_bits_write = 1;
    data_request_bits_tag = 8'h72;
    check(data_request_ready && !instruction_request_ready, "Data arbitration priority");
    tick(); data_request_valid = 0;
    data_request_bits_address = 0; data_request_bits_tag = 0;
    repeat (3) begin
      check(downstream_request_valid && downstream_request_bits_address == 64'h1008 && downstream_request_bits_tag == 8'h72 && downstream_request_bits_data == 64'hfedcba9876543210 && downstream_request_bits_mask == 8'hff && !instruction_request_ready && !data_request_ready, "Captured arbitration request hold");
      tick();
    end
    downstream_request_ready = 1; tick(); downstream_request_ready = 0;
    downstream_response_valid = 1;
    downstream_response_bits_data = 64'h1234;
    downstream_response_bits_tag = 8'h72;
    instruction_response_ready = 1;
    repeat (3) begin
      check(data_response_valid && data_response_bits_tag == 8'h72 && data_response_bits_data == 64'h1234 && !instruction_response_valid && !downstream_response_ready && !instruction_request_ready, "Data response ownership under backpressure");
      tick();
    end
    data_response_ready = 1; tick(); downstream_response_valid = 0;
    check(instruction_request_ready, "Instruction request recovery");
    tick(); instruction_request_valid = 0;
    check(downstream_request_valid && downstream_request_bits_address == 64'h100 && downstream_request_bits_tag == 8'h31 && downstream_request_bits_fetch, "Instruction request routing");
    downstream_request_ready = 1; tick(); downstream_request_ready = 0;
    data_request_valid = 1;
    instruction_response_ready = 0;
    downstream_response_valid = 1;
    downstream_response_bits_tag = 8'h31;
    downstream_response_bits_fault = 1;
    repeat (3) begin
      check(instruction_response_valid && instruction_response_bits_tag == 8'h31 && instruction_response_bits_fault && !data_response_valid && !downstream_response_ready && !data_request_ready, "Instruction response ownership under backpressure");
      tick();
    end
    instruction_response_ready = 1; tick(); downstream_response_valid = 0;
'''


def decode_contract():
    cases = ((0x12345337, 0, 0, 1), (0x12345317, 0, 0, 1),
             (0x12328313, 1, 0, 1), (0x00728333, 1, 1, 1),
             (0x00728463, 1, 1, 0), (0x0080036f, 0, 0, 1),
             (0x00428367, 1, 0, 1), (0x0082b303, 1, 0, 1),
             (0x0072b423, 1, 1, 0), (0x34029373, 1, 0, 1),
             (0x3402a373, 1, 0, 1), (0x00000073, 0, 0, 0),
             (0x30200073, 0, 0, 0), (0xffffffff, 0, 0, 0))
    body = '    input_valid = 1; output_ready = 1;\n'
    for word, rs1, rs2, rd in cases:
        serial = int(word in (0x34029373, 0x3402a373, 0x30200073))
        body += (f"    input_bits_instruction = 32'h{word:08x};\n"
                 f'    check(output_valid && input_ready && output_bits_usesRs1 == {rs1} && output_bits_usesRs2 == {rs2} && output_bits_writesRd == {rd} && output_bits_serializing == {serial}, "Decode dependency metadata {word:08x}");\n')
    return body + '''    input_bits_instruction = 32'h00728333; input_bits_fault = 1;
    check(!output_bits_usesRs1 && !output_bits_usesRs2 && !output_bits_writesRd, "Faulting instruction dependencies");
    input_bits_instruction = 32'h34029373;
    check(!output_bits_usesRs1 && !output_bits_writesRd && !output_bits_serializing, "Faulting CSR serialization");
'''


def memory_contract(parameters):
    base = int(parameters['resetVector'])
    cases = ((0x1000, 0, 1, 0, 1, True), (0x1002, 1, 1, 0, 2, True),
             (0x1004, 2, 0, 0, 0, True), (0x1008, 3, 1, 0, 0xff, True),
             (0x4000, 3, 0, 0, 0, True), (0x4000, 3, 1, 0, 0xff, False),
             (0x5000, 2, 0, 1, 0, False), (0x7000, 3, 0, 0, 0, False),
             (0x1000, 4, 0, 0, 0, False), (0x1001, 3, 0, 0, 0, False),
             (0x1000, 1, 1, 0, 0, False), (0x1000, 1, 1, 0, 4, False),
             (1 << parameters['physicalAddressBits'], 3, 0, 0, 0, False),
             (0x8000, 2, 0, 1, 0, True), (0x8000, 2, 0, 0, 0, False))
    body = ''
    for tag, (offset, size, write, fetch, mask, allowed) in enumerate(cases, 1):
        body += f'''    upstream_request_bits_address = 64'h{base + offset:x};
    upstream_request_bits_size = {size}; upstream_request_bits_write = {write};
    upstream_request_bits_fetch = {fetch}; upstream_request_bits_mask = {mask};
    upstream_request_bits_tag = {tag}; upstream_request_valid = 1;
    check(downstream_request_valid == {int(allowed)} && upstream_request_ready == {int(not allowed)}, "Memory permission and shape {tag}");
'''
        if allowed:
            body += f'''    repeat (3) begin
      check(downstream_request_valid && downstream_request_bits_tag == {tag} && !upstream_request_ready, "Memory request backpressure {tag}");
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
        for lane in sorted({0, bus_bytes - byte_count}):
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
  initial begin #10000; $fatal(1, "Timeout"); end
endmodule
''')


def verify(rtl, directory):
    directory.mkdir(parents=True, exist_ok=True)
    parameters = json.loads((rtl / 'ditdah_a1_config.json').read_text())['parameters']
    for name, body in (('DitDahA1Fetch', FETCH), ('DitDahA1Lsu', LSU),
                       ('DitDahA1Frontend', frontend_contract(parameters)),
                       ('DitDahA1Decode', decode_contract()),
                       ('DitDahA1MemoryArbiter', ARBITER),
                       ('DitDahA1Memory', memory_contract(parameters)),
                       ('DitDahA1Axi', axi_contract(parameters['axiDataBits']))):
        module = rtl / (name + '.sv')
        test = directory / (name + '_tb.sv')
        test.write_text(bench(module, body))
        binary = directory / name
        dependencies = [rtl / 'DitDahA1Fetch.sv'] if name == 'DitDahA1Frontend' else []
        subprocess.run(['iverilog', '-g2012', '-s', 'contract_tb', '-o', str(binary),
                        str(module), *map(str, dependencies), str(test)], check=True)
        result = subprocess.run(['vvp', str(binary)], capture_output=True, text=True, timeout=30)
        (directory / (name + '.log')).write_text(result.stdout + result.stderr)
        assert result.returncode == 0 and 'PASS' in result.stdout, result.stdout + result.stderr
        print(f'  {name} interface contracts passed', flush=True)
