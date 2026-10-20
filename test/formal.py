# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Prove execution and transaction safety on generated RTL."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

import click


FETCH = r'''
  reg past_valid = 0;
  reg outstanding;
  reg killed;
  reg have_request;
  reg response_seen;
  reg [63:0] accepted_pc;
  reg [7:0] accepted_tag;
  reg accepted_privileged;
  always @(posedge clock) begin
    past_valid <= 1;
    if (!past_valid) assume(reset);
    else assume(!reset);
    if (reset) begin
      outstanding <= 0;
      killed <= 0;
      have_request <= 0;
      response_seen <= 0;
    end else begin
      assume(!memory_response_valid || outstanding);
      if (past_valid && $past(!reset && memory_response_valid && !memory_response_ready)) begin
        assume(memory_response_valid);
        assume($stable({memory_response_bits_data, memory_response_bits_fault, memory_response_bits_tag, memory_response_bits_last}));
      end
      if (memory_response_valid && memory_response_ready) begin
        assert(outstanding);
        outstanding <= 0;
        response_seen <= 1;
      end
      if (memory_request_valid && memory_request_ready) begin
        assert(!outstanding || (memory_response_valid && memory_response_ready));
        outstanding <= 1;
      end
      if (output_valid && output_ready) have_request <= 0;
      if (cancel) killed <= 1;
      if (request_valid && request_ready) begin
        assert(!have_request || killed || (output_valid && output_ready));
        have_request <= 1;
        killed <= 0;
        response_seen <= 0;
        accepted_pc <= request_bits_pc;
        accepted_tag <= request_bits_tag;
        accepted_privileged <= PRIVILEGED;
      end
      assert(!memory_response_ready || outstanding);
      if (memory_request_valid) assert(!memory_request_bits_atomic && !memory_request_bits_atomicOperation && !memory_request_bits_scEligible);
      if (memory_request_valid) assert(memory_request_bits_privileged == accepted_privileged);
      if (output_valid) begin
        assert(have_request);
        assert(response_seen || accepted_pc[1:0] != 0);
        assert(output_bits_pc == accepted_pc && output_bits_tag == accepted_tag);
      end
      if (killed || cancel) assert(!output_valid);
      if (past_valid && $past(!reset && memory_request_valid && !memory_request_ready)) begin
        assert(memory_request_valid);
        assert($stable({memory_request_bits_address, memory_request_bits_data,
          memory_request_bits_size, memory_request_bits_mask, memory_request_bits_tag,
          memory_request_bits_write, memory_request_bits_fetch, memory_request_bits_privileged, memory_request_bits_atomic,
          memory_request_bits_atomicOperation, memory_request_bits_scEligible}));
      end
      cover(past_valid && $past(!reset && memory_request_valid && !memory_request_ready)
        && cancel && memory_request_valid && !memory_request_ready);
      cover(killed && outstanding && memory_response_valid && memory_response_ready && memory_response_bits_fault);
      cover(killed && request_ready);
      cover(output_valid && output_ready && !output_bits_fault);
      cover(output_valid && output_ready && output_bits_fault && response_seen);
    end
  end
'''

FETCH_PHYSICAL = r'''
  reg fetch_physical_owned = 0, fetch_physical_line;
  always @(posedge clock) if (reset) fetch_physical_owned <= 0;
  else begin
    assume(!memory_response_valid || fetch_physical_owned);
    cover(observed_killed && fetch_physical_owned && memory_response_valid && memory_response_ready && memory_response_bits_fault);
    cover($past(!reset && memory_request_valid && !memory_request_ready) && (cancel || invalidate) && memory_request_valid && !memory_request_ready);
    if ($past(!reset && memory_request_valid && !memory_request_ready)) begin assert(memory_request_valid); assert($stable({memory_request_bits_address, memory_request_bits_size, memory_request_bits_tag, memory_request_bits_privileged})); end
    assume(!memory_response_valid || fetch_physical_line || memory_response_bits_last);
    if ($past(!reset && memory_response_valid && !memory_response_ready)) begin assume(memory_response_valid); assume($stable({memory_response_bits_data, memory_response_bits_tag, memory_response_bits_fault, memory_response_bits_last})); end
    if (memory_request_valid && memory_request_ready) begin assert(!fetch_physical_owned); fetch_physical_owned <= 1; fetch_physical_line <= memory_request_bits_size == 6; end
    if (memory_response_valid && memory_response_ready && memory_response_bits_last) fetch_physical_owned <= 0;
  end
'''

MULTIPLY = r'''
  reg past_valid = 0;
  reg pending, completed;
  reg [6:0] age;
  reg [63:0] first, second;
  always @(posedge clock) begin
    past_valid <= 1;
    if (!past_valid) assume(reset);
    else assume(!reset);
    if (reset) begin
      pending <= 0;
      completed <= 0;
      age <= 0;
    end else begin
      if (input_valid && input_ready) begin
        assert(!pending);
        pending <= 1;
        age <= 0;
        first <= input_bits_operand1;
        second <= input_bits_operand2;
      end else if (pending && !output_valid) age <= age + 1;
      if (output_valid && output_ready) begin pending <= 0; completed <= 1; end
      assert(input_ready == !pending);
      assert(pending == (busy || valid));
      assert(!(busy && valid));
      assert(age <= 64);
      if (pending) assert(multiplier == (second >> age));
      if (pending && first == 0) assert(multiplicand == 0 && product == 0);
      if (pending && second == 0) assert(multiplier == 0 && product == 0);
      if (pending && second == 1) assert(
        (busy && multiplier == 1 && product == 0 && multiplicand == first) ||
        (valid && product == first));
      if (output_valid) begin
        assert(pending);
        if (first == 0 || second == 0) assert(output_bits == 0);
        if (second == 1) assert(output_bits == first);
      end
      if (past_valid && $past(!reset && output_valid && !output_ready)) begin
        assert(output_valid);
        assert($stable(output_bits));
      end
      cover(output_valid && !output_ready && second == 1);
      cover(output_valid && output_ready && (first == 0 || second == 0));
      cover(output_valid && age == 64);
      cover(pending && age > 2 && input_valid && !input_ready);
      cover(completed && input_valid && input_ready);
    end
  end
'''

def backend_names(text, source):
    text = re.sub(r'\b(instruction|decoded|issued|result|memory|commit)Packet_', r'\1Packets_0_', text)
    for name in ('instruction', 'decoded', 'issued', 'result', 'memory', 'commit'):
        text = re.sub(rf'\b{name}Valid\b', f'({name}Count != 0)', text)
    for name in ('issued', 'executed', 'issueCount', 'retireCount', 'memoryAdvance', 'resultAdvance'):
        candidates = re.findall(rf'\bwire\s+(?:\[[^\]]+\]\s+)?({name}(?:_layerCapture|_\d+)?)\s*=', source)
        if candidates:
            text = re.sub(rf'\b{name}\b', candidates[-1], text)
        elif name == 'issueCount':
            text = re.sub(r'\bissueCount\b', 'issued_layerCapture', text)
    text = re.sub(r'\breceived\b', '(instruction_valid && instruction_ready)', text)
    text = text.replace('commit_output_valid_layerCapture', '_commit_output_valid')
    for _, pins in instance_ports(source, 'DitDahA1Commit'):
        for pin, value in pins.items():
            if pin.startswith('output') and re.fullmatch(r'\w+', value):
                text = re.sub(rf'\b_commit_{pin}\b', value, text)
    return text


def pipeline_case(source, parameters):
    width, capacity = parameters['issueWidth'], 6 * parameters['issueWidth']
    stages = ('commit', 'memory', 'result', 'issued', 'decoded', 'instruction')
    identity = lambda p: '{' + p + '_pc, ' + p + '_instruction}'
    body = f'''
  reg pipeline_past = 0;
  reg [{capacity.bit_length()-1}:0] pipeline_owned;
  reg pipeline_fifo[{capacity}];
  (* anyconst *) reg [6:0] pipeline_bit;
  wire [95:0] pipeline_input[{width}];
  wire [{width.bit_length()-1}:0] pipeline_added = received ? instruction_bits_count : 0;
  wire [{capacity.bit_length()-1}:0] pipeline_remaining = pipeline_owned - retireCount;
  always @* assume(pipeline_bit < 96);
'''
    for lane in range(width):
        body += f'  assign pipeline_input[{lane}] = {identity(f"instruction_bits_packets_{lane}")};\n'
    older = '0'
    for stage in stages:
        suffix = '_decoded_instruction' if stage == 'issued' else '' if stage == 'instruction' else '_instruction'
        for lane in range(width):
            body += f'''  wire [95:0] pipeline_{stage}_{lane} = {identity(f'{stage}Packets_{lane}' + suffix)};
  always @(posedge clock) if (!reset && {stage}Count > {lane})
    assert(pipeline_{stage}_{lane}[pipeline_bit] == pipeline_fifo[{older} + {lane}]);
'''
        older += f' + {stage}Count'
    body += f'''
  integer pipeline_i;
  always @(posedge clock) begin
    pipeline_past <= 1;
    if (!pipeline_past) assume(reset); else assume(!reset);
    if (reset || redirect_0) pipeline_owned <= 0;
    else begin
      pipeline_owned <= pipeline_remaining + pipeline_added;
      for (pipeline_i = 0; pipeline_i < {capacity}; pipeline_i = pipeline_i + 1) begin
        if (pipeline_i < pipeline_remaining)
          pipeline_fifo[pipeline_i] <= pipeline_fifo[pipeline_i + retireCount];
        else if (pipeline_i < pipeline_remaining + pipeline_added)
          pipeline_fifo[pipeline_i] <= pipeline_input[pipeline_i - pipeline_remaining][pipeline_bit];
      end
    end
    if (!reset) begin
      assert(pipeline_owned <= {capacity} && pipeline_owned == ({older}));
      assert(retireCount <= commitCount && issueCount <= decodedCount);
      if (redirect_0) assert(!received && !issued && !executed && !data_request_valid);
      if (memoryPending) assert(memoryCount == 1 && !commitValid);
      if (lsu_input_valid) assert(resultCount == 1);
      if (multiply_input_valid) assert(issuedCount == 1);
      cover(pipeline_owned == {capacity} && received && retireCount == {width});
      cover(memoryPending && decodedValid && !issued);
      cover(issueCount == {width} && retireCount == {width});
      cover(issueCount == 0 && pipeline_owned != 0);
'''
    if width > 1:
        body += f'      cover(issueCount > 0 && issueCount < {width} && decodedCount == {width});\n'
    body += '    end\n  end\n'
    for stage in stages:
        body += f'  always @(posedge clock) if (!reset) assert({stage}Count <= {width});\n'
        if stage in ('issued', 'result', 'memory', 'commit'):
            for lane in range(width):
                fault = f'{stage}Packets_{lane}_' + ('decoded_' if stage == 'issued' else '') + 'instruction_fault'
                body += f'  always @(posedge clock) if (!reset && {stage}Count > 1 && {stage}Count > {lane}) assert(!{fault});\n'
    for stage in ('result', 'memory', 'commit'):
        p = stage + 'Packets_0'
        effects = ' || '.join(f'{p}_{field}' for field in ('load', 'store', 'atomic', 'csrWrite', 'mret', 'sret', 'wfi', 'fenceI', 'sfenceVma', 'instruction_fault')
                             if re.search(rf'\b{p}_{field}\b', source))
        body += f'  always @(posedge clock) if (!reset && {stage}Count > 1) assert(!({effects}));\n'
    gpr = instance_ports(source, 'DitDahA1Gpr')[0][1]
    for lane in range(width):
        p = f'commitPackets_{lane}'
        body += f'''  always @(posedge clock) if (!reset) begin
    assert(({gpr[f'we_{lane}']}) == (retireCount > {lane} && {p}_rdWrite && {p}_rd != 0 && !{p}_instruction_fault));
    if ({gpr[f'we_{lane}']}) assert(({gpr[f'waddr_{lane}']}) == {p}_rd && ({gpr[f'wdata_{lane}']}) == {p}_value);
  end
'''
    issues = [pins for _, pins in instance_ports(source, 'DitDahA1Issue')]
    assert len(issues) == width
    for lane in range(width):
        d = f'decodedPackets_{lane}'
        for stage, packet in (('decoded', d), ('issued', f'issuedPackets_{lane}_decoded')):
            simple = ' || '.join(f'{packet}_operation == {op}' for op in (1, 2, 3, 4, 21, 22, 23, 24))
            body += f'  wire pipeline_simple_{stage}_{lane} = !{packet}_instruction_fault && ({simple});\n'
        body += f'  always @(posedge clock) if (!reset && issuedCount > 1 && issuedCount > {lane}) assert(pipeline_simple_issued_{lane});\n'
        blocked = []
        for operand in (1, 2):
            writers = []
            for stage in ('issued', 'result', 'memory', 'commit'):
                for previous in reversed(range(width)):
                    p = f'{stage}Packets_{previous}'
                    if stage == 'issued':
                        p += '_decoded'
                        ready = '_execute_output_valid && !_execute_output_bits_instruction_fault && !_execute_output_bits_load && !_execute_output_bits_store' if previous == 0 else '_execute_output_valid && !' + p + '_instruction_fault'
                        value = 'isMultiply ? _multiply_output_bits : _execute_output_bits_value' if previous == 0 else f'pipeline_execution_{previous}'
                    else:
                        ready = ('!memoryOperation && ' if stage == 'result' and previous == 0 else
                                 '(!memoryCompletion || (memoryPending && _lsu_output_valid)) && ' if stage == 'memory' and previous == 0 else '') + (
                                     '!completion_instruction_fault' if stage == 'memory' and previous == 0 else '!' + p + '_instruction_fault')
                        value = 'memoryPending ? _lsu_output_bits_value : ' + p + '_value' if stage == 'memory' and previous == 0 else p + '_value'
                    present = f'{stage}Count > {previous} && {p}_{"writesRd" if stage == "issued" else "rdWrite"} && {p}_rd != 0 && {d}_rs{operand} == {p}_rd'
                    writers.append((present, ready, value))
            stem = f'pipeline_operand_{lane}_{operand}'
            body += f'  reg [63:0] {stem};\n  reg {stem}_blocked;\n  always @* begin\n'
            body += f'    {stem} = {d}_usesRs{operand} ? _gpr_rdata{operand}_{lane} : 0; {stem}_blocked = 0;\n'
            body += f'    if ({d}_usesRs{operand} && {d}_rs{operand} != 0) begin\n'
            for index, (present, ready, value) in enumerate(writers):
                body += f'      {"else " if index else ""}if ({present}) begin {stem} = {value}; {stem}_blocked = !({ready}); end\n'
            body += f'''    end
  end
  always @(posedge clock) if (!reset && issueCount > {lane}) begin
    assert(!{stem}_blocked && ({issues[lane][f'output_bits_operand{operand}']}) == {stem});
  end
'''
            blocked.append(stem + '_blocked')
        conflict = []
        for previous in range(lane):
            p = f'decodedPackets_{previous}'
            conflict.append(f'({p}_writesRd && {p}_rd != 0 && (({d}_usesRs1 && {p}_rd == {d}_rs1) || ({d}_usesRs2 && {p}_rd == {d}_rs2) || ({d}_writesRd && {p}_rd == {d}_rd)))')
        body += f'''  wire pipeline_prefix_{lane} = decodedCount > {lane} && !({' || '.join(blocked)}) &&
    !({d}_serializing && (issuedValid || resultValid || memoryValid || commitValid)) &&
    {f"pipeline_prefix_{lane-1} && pipeline_simple_decoded_0 && pipeline_simple_decoded_{lane} && !(" + " || ".join(conflict) + ")" if lane else "1'b1"};
'''
    for lane in range(1, width):
        match = re.search(rf'resultPackets_{lane}_value <=\s*([^;]+);', source)
        assert match
        body += f'  wire [63:0] pipeline_execution_{lane} = {match[1]};\n'
    expected = ' + '.join(f"{{{width.bit_length()-1}'b0, pipeline_prefix_{lane}}}" if width > 1 else f'pipeline_prefix_{lane}' for lane in range(width))
    sleeping = 'sleep' if parameters.get('enableInterrupts') else "1'b0"
    body += f'''  always @(posedge clock) if (!reset) begin
    assert(issueCount == ((!issuedValid || executed) && !executePending && !redirect_0 && !{sleeping} ? ({expected}) : 0));
  end
'''
    before = re.search(r'commitPackets_0_instruction_pc <=\s*[^;]+;', source).group()
    translation = ' || translation_request_valid || translation_response_ready' if parameters.get('virtualAddressBits') == 39 else ''
    body += f'''  always @(posedge clock) if (!reset)
    assert(memoryPending == (data_request_valid || data_response_ready || _lsu_output_valid{translation}));
'''
    body += '''  always @(posedge clock) if (!reset && memoryPending) begin
    assert(memoryPackets_0_instruction_tag == _lsu_output_bits_instruction_tag &&
      memoryPackets_0_instruction_pc == _lsu_output_bits_instruction_pc &&
      memoryPackets_0_instruction_instruction == _lsu_output_bits_instruction_instruction);
  end
'''
    return ('PipelineBackend', backend_names(body, source), before, "commitPackets_0_instruction_pc <= 64'h0;")


RESOURCE = r'''
  reg pending, valid;
  reg [63:0] data;
  (* anyseq *) reg finish;
  (* anyseq *) reg [63:0] result;
  assign input_ready = !pending;
  assign output_valid = valid;
  assign output_bits = data;
  always @(posedge clock) begin
    if (reset) begin pending <= 0; valid <= 0; end
    else begin
      if (input_valid && input_ready) pending <= 1;
      if (pending && !valid && finish) begin valid <= 1; data <= result; end
      if (output_valid && output_ready) begin pending <= 0; valid <= 0; end
    end
  end
'''

BACKEND = r'''
  reg past_valid = 0;
  reg owned, cancelled;
  reg [63:0] owner_pc;
  reg [7:0] owner_tag;
  reg [4:0] owner_rd;
  always @(posedge clock) begin
    past_valid <= 1;
    if (!past_valid) assume(reset);
    else assume(!reset);
    if (reset) begin owned <= 0; cancelled <= 0; end
    else begin
      if (multiply_input_valid && _multiply_input_ready) begin
        assert(!owned);
        owned <= 1;
        cancelled <= 0;
        owner_pc <= issuedPacket_decoded_instruction_pc;
        owner_tag <= issuedPacket_decoded_instruction_tag;
        owner_rd <= issuedPacket_decoded_rd;
      end
      if (redirect_0 && owned) cancelled <= 1;
      if (_multiply_output_valid && multiply_output_ready) begin
        assert(owned);
        owned <= 0;
      end
      assert(owned == executePending);
      if (owned) begin
        assert(!issued && !multiply_input_valid);
        assert(issuedPacket_decoded_instruction_pc == owner_pc);
        assert(issuedPacket_decoded_instruction_tag == owner_tag && issuedPacket_decoded_rd == owner_rd);
        if (cancelled) assert(!issuedValid && !executed && !commitValid && !data_request_valid);
      end
      if (redirect_0) assert(!executed && !multiply_input_valid);
      cover(owned && !cancelled && _multiply_output_valid && !multiply_output_ready);
      cover(owned && redirect_0 && !_multiply_output_valid);
      cover(owned && redirect_0 && _multiply_output_valid);
      cover(owned && cancelled && _multiply_output_valid && multiply_output_ready);
      cover(owned && cancelled && instruction_valid && instruction_ready);
    end
  end
'''


def header(text):
    return text[text.index('module '):text.index(');') + 2]


def module_ports(source):
    direction, width = None, ''
    for item in header(source).split('(', 1)[1].rsplit(');', 1)[0].split(','):
        match = re.fullmatch(r'\s*(?:(input|output)\s+)?(\[\d+:\d+\])?\s*(\w+)\s*', item)
        assert match, item
        new_direction, new_width, name = match.groups()
        if new_direction:
            direction, width = new_direction, new_width or ''
        yield direction, width, name


def witness_wrapper(source, body, values):
    text, assignments = 'module formal_witness(input clock, reset);\n', ''
    for direction, width, name in module_ports(source):
        if name not in ('clock', 'reset'):
            text += f'  wire {width} {name};\n'
            if direction == 'input':
                value = values.get(name, "'0")
                assignments += f'  assign {name} = {value};\n'
    module = header(source).split('(', 1)[0].split()[-1]
    return text + body + assignments + f'  {module} dut (.*);\nendmodule\n'


def resource_witness(parameters, mode):
    body = r'''
  reg [1:0] packet = 0;
  reg pending = 0;
  (* anyseq *) reg respond;
  always @(posedge clock) if (!reset) begin
    if (instruction_valid && instruction_ready && packet != 3) packet <= packet + 1;
    if (data_request_valid && data_request_ready) pending <= 1;
    if (data_response_valid && data_response_ready) pending <= 0;
  end
'''
    first = "32'h00003023"
    if parameters['pmpEntries']:
        body += '  (* anyconst *) reg permission;\n'
        first = "(permission ? 32'h3a001073 : 32'h00003023)"
    return body, dict(instruction_valid=1, instruction_bits_count=1,
                      instruction_bits_packets_0_pc=f"64'h{int(parameters['resetVector']):x}",
                      instruction_bits_packets_0_length=4,
                      instruction_bits_packets_0_instruction=f"packet == 0 ? {first} : packet == 1 ? 32'h020000b3 : 32'h13",
                      data_request_ready=1, data_response_valid='pending && respond',
                      data_response_bits_fault=1, data_response_bits_last=1)


def pipeline_witness(parameters, mode):
    width = parameters['issueWidth']
    body = r'''
  (* anyconst *) reg [1:0] scenario;
  (* anyseq *) reg respond;
  reg started = 0, pending = 0;
  reg [63:0] pc = 64'h100;
  always @* assume(scenario < 3);
  always @(posedge clock) if (!reset) begin
    if (instruction_valid && instruction_ready) begin started <= 1; pc <= pc + 4 * instruction_bits_count; end
    if (data_request_valid && data_request_ready) pending <= 1;
    if (data_response_valid && data_response_ready) pending <= 0;
  end
'''
    values = dict(instruction_valid=1, instruction_bits_count=f'scenario == 1 && !started ? 1 : {width}',
                  data_request_ready=1, data_response_valid='pending && respond', data_response_bits_last=1)
    for lane in range(width):
        packet = f'instruction_bits_packets_{lane}_'
        word = (1 << 20) | ((lane + 1) << 7) | 0x13
        values[packet + 'instruction'] = (f"scenario == 1 && !started ? 32'h00003023 : 32'h{word:x}" if lane == 0 else
                                         f"scenario == 2 ? 32'h{word | (1 << 15):x} : 32'h{word:x}" if lane == 1 else f"32'h{word:x}")
        values[packet + 'pc'], values[packet + 'length'] = f'pc + {4 * lane}', 4
    return body, values


def protection_cases(parameters):
    width = parameters['physicalAddressBits'] - 2
    fetch_sizes = ([4] if parameters.get('iCacheBytes') and parameters['issueWidth'] == 3 else []) + ([6] if parameters.get('enableBurstRefill') else [])
    line_size = ''.join(f' || (size == {size} && fetch && !write && !atomic)' for size in fetch_sizes)
    machine = "privilege == 3" if parameters.get('enableUserMode') else "1'b1"
    decode = f'''
  reg expected, any_byte, every_byte, carry, hit;
  reg [7:0] config;
  reg [64:0] point, low, high, length, cursor;
  integer i, b;
  always @* begin
    expected = 1; hit = 0; cursor = 0;
    for (i = 15; i >= 0; i = i - 1) begin
      config = state_config[i*8 +: 8];
      point = state_address[i*{width} +: {width}];
      low = 0; high = 0; length = 7; carry = 1;
      for (b = 0; b < {width}; b = b + 1) begin
        carry = carry & point[b];
        length[b+3] = carry;
      end
      case (config[4:3])
        1: begin
          if (i != 0) low = {{2'b0, state_address[(i-1)*{width} +: {width}]}} << 2;
          high = point << 2;
        end
        2: begin low = point << 2; high = low + 4; end
        3: begin low = (point << 2) & ~length; high = low + length + 1; end
      endcase
'''
    low_signals = ', '.join(['base'] + [f'base_{i}' for i in range(15)])
    high_signals = ', '.join(['limit'] + [f'limit_{i}' for i in range(15)])
    decode += '      case (i)\n' + ''.join(
        f"        {i}: assert({('base' if i == 15 else f'base_{14-i}')} == low && {('limit' if i == 15 else f'limit_{14-i}')} == high);\n"
        for i in range(16)) + '      endcase\n    end\n    assert(start == {1\'b0, address});\n    assert(end_0 == (size <= 3 ? {1\'b0, address} + (65\'d1 << size) : {1\'b0, address}));\n    cover(state_config[4:3] == 3 && state_address[0]);\n  end\n'
    if line_size:
        supported = 'size <= 3' + ''.join(f' || size == {size}' for size in fetch_sizes)
        decode = decode.replace('size <= 3 ?', f'({supported}) ?')
    interval = r'''
  reg any_byte, every_byte, hit;
  reg [64:0] cursor;
  integer b;
  wire [64:0] finish = {1'b0, address} + (65'd1 << size);
  always @* begin
    any_byte = 0; every_byte = 1; hit = 0; cursor = 0;
    for (b = 0; b < 8; b = b + 1) if (b < (1 << size)) begin
      cursor = {1'b0, address} + b;
      hit = cursor >= low && cursor < high;
      any_byte = any_byte | hit;
      every_byte = every_byte & hit;
    end
    if (size <= 3) begin
      assert(any_byte == (high > low && {1'b0, address} < high && finish > low));
      assert(!any_byte || every_byte == ({1'b0, address} >= low && finish <= high));
    end
    cover(any_byte && !every_byte && size == 3);
  end
'''
    if line_size:
        interval = r'''
  (* anyconst *) reg [OFFSET:0] offset;
  wire supported = SUPPORTED;
  wire [64:0] begin_address = {1'b0, address};
  wire [64:0] finish = begin_address + (65'd1 << size);
  wire [64:0] selected = begin_address + offset;
  wire overlap = high > low && begin_address < high && finish > low;
  wire contained = begin_address >= low && finish <= high;
  wire [64:0] first = begin_address >= low ? begin_address : low;
  wire [64:0] outside = begin_address < low ? begin_address : finish - 1;
  always @* if (supported) begin
    if (offset < (1 << size) && selected >= low && selected < high) assert(overlap);
    if (overlap) assert(first >= begin_address && first < finish && first >= low && first < high);
    if (offset < (1 << size) && contained) assert(selected >= low && selected < high);
    if (overlap && !contained) assert(outside >= begin_address && outside < finish && (outside < low || outside >= high));
    cover(overlap && !contained && size == EXTRA);
  end
'''.replace('OFFSET', str(max(fetch_sizes)-1)).replace('SUPPORTED', supported).replace('EXTRA', str(max(fetch_sizes)))
    pmp = f'''
  wire [1039:0] decoded_low = {{{low_signals}}};
  wire [1039:0] decoded_high = {{{high_signals}}};
  reg expected, any_byte, every_byte, hit;
  reg [64:0] cursor;
  integer i, b;
  always @* begin
    expected = {machine}; hit = 0; cursor = 0; any_byte = 0; every_byte = 1;
    for (i = 15; i >= 0; i = i - 1) begin
      any_byte = 0; every_byte = 1;
      for (b = 0; b < 8; b = b + 1) if (b < (1 << size)) begin
        cursor = {{1'b0, address}} + b;
        hit = state_config[i*8+3 +: 2] != 0 && cursor >= decoded_low[i*65 +: 65] && cursor < decoded_high[i*65 +: 65];
        any_byte = any_byte | hit;
        every_byte = every_byte & hit;
      end
      if (size <= 3) begin
        assume(any_byte == (state_config[i*8+3 +: 2] != 0 && decoded_high[i*65 +: 65] > decoded_low[i*65 +: 65] &&
          start < decoded_high[i*65 +: 65] && end_0 > decoded_low[i*65 +: 65]));
        assume(!any_byte || every_byte == (start >= decoded_low[i*65 +: 65] && end_0 <= decoded_high[i*65 +: 65]));
      end
      if (any_byte) expected = every_byte && (({machine}) && !state_config[i*8+7] ||
        (atomic ? state_config[i*8] && state_config[i*8+1] :
          fetch ? state_config[i*8+2] : write ? state_config[i*8+1] : state_config[i*8]));
    end
    assert(allowed == (expected && (size <= 3{line_size}) &&
      ({{1'b0, address}} + (65'd1 << size)) <= (65'd1 << {width + 2})));
    cover(allowed && fetch);
    cover(!allowed && write);
    cover(!allowed && size == 3 && !state_config[7]);
    cover(atomic && allowed);
    cover(atomic && !allowed && write);
  end
'''
    if line_size:
        start = pmp.index('      for (b = 0;')
        end = pmp.index('      if (any_byte) expected', start)
        pmp = pmp[:start] + '''
      any_byte = state_config[i*8+3 +: 2] != 0 && decoded_high[i*65 +: 65] > decoded_low[i*65 +: 65] &&
        {1'b0, address} < decoded_high[i*65 +: 65] && ({1'b0, address} + (65'd1 << size)) > decoded_low[i*65 +: 65];
      every_byte = {1'b0, address} >= decoded_low[i*65 +: 65] &&
        ({1'b0, address} + (65'd1 << size)) <= decoded_high[i*65 +: 65];
''' + pmp[end:]
        pmp = pmp.replace("({1'b0, address} + (65'd1 << size))", 'end_0').replace("{1'b0, address}", 'start')
        for size in fetch_sizes:
            pmp += f"  always @* begin cover(allowed && size == {size} && fetch); cover(!allowed && size == {size} && fetch); cover(!allowed && size == {size} && write); end\n"
    csr = '''
  reg past_valid = 0;
  always @(posedge clock) begin
    past_valid <= 1;
    if (!past_valid) assume(reset);
    if (past_valid && $past(reset)) assert(pmp_config == 0 && pmp_address == 0);
    if (past_valid) begin
'''
    for i in range(16):
        cfg = f'pmp_config[{i * 8} +: 8]'
        addr = f'pmp_address[{i * width} +: {width}]'
        prior = "1'b0" if i == 15 else f'(pmp_config[{(i + 1) * 8 + 7}] && pmp_config[{(i + 1) * 8 + 3} +: 2] == 1)'
        csr += f'''
      assert(({cfg} & 8'h60) == 0 && !(({cfg} & 3) == 2));
      if (!$past(reset)) begin
        if ($past({cfg}[7])) assert($stable({cfg}));
        if ($past({cfg}[7] || {prior})) assert($stable({addr}));
        if ($past(write && writeAddress == 12'h{0x3b0 + i:x} && !{cfg}[7] && !{prior}))
          assert({addr} == ($past(writeData) & {width}'h{(1 << width) - 1:x}));
      end
'''.replace(f'{cfg}[7]', f'pmp_config[{i * 8 + 7}]')
    csr += '''
      if (readAddress >= 12'h3a0 && readAddress <= 12'h3af && readAddress[0]) assert(!legal);
      if (readAddress >= 12'h3c0 && readAddress <= 12'h3ef) assert(legal && readData == 0);
      cover(pmp_config[127]);
      cover(pmp_config[15:8] == 8'h89 && write && writeAddress == 12'h3b0);
      cover($past(pmp_config[7]) && reset);
    end
  end
'''
    if parameters.get('enableUserMode'):
        csr = csr.replace("if (readAddress >=", "if (privilege == 3 && readAddress >=")
    fetch = FETCH.replace('reg outstanding;', 'reg outstanding;\n  reg local_denied;')
    fetch = fetch.replace('killed', 'observed_killed')
    fetch = fetch.replace('outstanding <= 0;', 'outstanding <= 0;\n      local_denied <= 0;', 1)
    fetch = fetch.replace('accepted_pc <= request_bits_pc;', 'local_denied <= !_pmp_allowed;\n        accepted_pc <= request_bits_pc;')
    fetch = fetch.replace('response_seen || accepted_pc[1:0] != 0', 'response_seen || accepted_pc[1:0] != 0 || local_denied')
    fetch = fetch.replace('if (observed_killed || cancel)', 'if (have_request && local_denied) assert(!memory_request_valid);\n      cover(output_valid && local_denied && output_bits_fault);\n      if (observed_killed || cancel)')
    backend = BACKEND + '''
  wire permission_update = commit_output_valid_layerCapture && _commit_output_bits_csrWrite &&
    ((_commit_output_bits_csrAddress >= 12'h3a0 && _commit_output_bits_csrAddress <= 12'h3ae) ||
     (_commit_output_bits_csrAddress >= 12'h3b0 && _commit_output_bits_csrAddress <= 12'h3ef));
  always @(posedge clock) if (!reset) begin
    if (permission_update) assert(redirect_0 && !executed && !data_request_valid);
    if (past_valid && $past(!reset && permission_update))
      assert(!instructionValid && !decodedValid && !issuedValid && !resultValid && !memoryValid && !commitValid);
    cover(permission_update && issuedValid);
    cover(permission_update && decodedValid);
  end
'''
    return [('PmpInterval', interval, 'high > low', "1'b0"),
            ('PmpDecode', decode, "mask = _GEN_0 ^ _GEN_0 + 62'h1;", "mask = _GEN_0 ^ _GEN_0 + 62'h3;"),
            ('Pmp', pmp, 'assign allowed =', "assign allowed = 1'h1 |"),
            ('Csr', csr, '& ~(config_0[5])', "& 1'h1"),
            ('Fetch', fetch, '& ~killed & ~cancel', '& ~cancel'),
            ('Backend', backend, '| _commit_output_bits_csrWrite\n', "| 1'h0 & _commit_output_bits_csrWrite\n")]


def interrupt_cases(parameters):
    csr = r'''
  reg irq_past = 0;
  wire [2:0] irq_levels = {interrupts_external, interrupts_timer, interrupts_software};
  wire [2:0] irq_enabled = enables & irq_levels;
  always @(posedge clock) begin
    irq_past <= 1;
    if (!irq_past) assume(reset);
    if (irq_past) begin
      if ($past(reset)) assert(enables == 0 && status == 0);
      else begin
        assert(enables == ($past(write && writeAddress == 12'h304) ?
          {$past(writeData[11]), $past(writeData[7]), $past(writeData[3])} : $past(enables)));
        if ($past(trap)) begin
          assert(mepc == ($past(trapPc) & ~64'd3));
          assert(mcause == $past(trapCause) && mtval == $past(trapValue));
          assert(!status[3] && status[7] == $past(status[3]));
        end else if ($past(mret)) assert(status[3] == $past(status[7]) && status[7]);
        else if ($past(write && writeAddress == 12'h300)) assert(status == ($past(writeData) & 64'h88));
      end
      assert(interruptPending == (status[3] && irq_enabled != 0));
      assert(wakeup == (irq_enabled != 0));
      if (interruptPending) assert(interruptCause == (64'h8000000000000000 |
        (irq_enabled[2] ? 64'd11 : irq_enabled[0] ? 64'd3 : 64'd7)));
      if (readAddress == 12'h304) assert(legal && readData ==
        (({61'd0, enables} & 1) << 3 | ({61'd0, enables} & 2) << 6 | ({61'd0, enables} & 4) << 9));
      if (readAddress == 12'h344) assert(legal && readData ==
        (({61'd0, irq_levels} & 1) << 3 | ({61'd0, irq_levels} & 2) << 6 | ({61'd0, irq_levels} & 4) << 9));
      cover(interruptPending && interruptCause[3:0] == 11 && irq_levels == 7);
      cover(interruptPending && interruptCause[3:0] == 3);
      cover(interruptPending && interruptCause[3:0] == 7);
      cover(irq_levels != 0 && !status[3] && readAddress == 12'h344);
      cover($past(mret && !reset) && interruptPending);
      cover(wakeup && !status[3]);
      cover(!wakeup && irq_levels != 0);
    end
  end
'''
    if parameters.get('enableUserMode'):
        csr = csr.replace("status == ($past(writeData) & 64'h88)",
                          "status == (($past(writeData) & 64'h220088) | ($past(writeData[12:11]) == 3 ? 64'h1800 : 0))")
        csr = csr.replace('status[3] && irq_enabled != 0', '(privilege < 3 || status[3]) && irq_enabled != 0')
        csr = csr.replace("if (readAddress ==", "if (privilege == 3 && readAddress ==")
    backend = BACKEND + f'''
  reg irq_memory_owned = 0;
  reg [1:0] irq_service_age = 0;
  reg [63:0] irq_memory_pc;
  reg [7:0] irq_memory_tag;
  wire irq_memory_commit = commitValid && (commitPacket_load || commitPacket_store);
  always @(posedge clock) begin
    if (reset) begin irq_memory_owned <= 0; irq_service_age <= 0; end
    else begin
      if (data_response_valid && data_response_ready && !data_response_bits_fault &&
          data_response_bits_tag == irq_memory_tag && _csr_interruptPending) irq_service_age <= 1;
      else if (irq_service_age != 0) irq_service_age <= irq_service_age + 1;
      if (!_csr_interruptPending || takeInterrupt_layerCapture) irq_service_age <= 0;
      if (irq_service_age == 3 && _csr_interruptPending)
        assert(takeInterrupt_layerCapture || (commit_output_valid_layerCapture && commitPacket_instruction_fault));
      if (lsu_input_valid && _lsu_input_ready) begin
        assert(!irq_memory_owned);
        irq_memory_owned <= 1;
        irq_memory_pc <= resultPacket_instruction_pc;
        irq_memory_tag <= resultPacket_instruction_tag;
      end
      if (commit_output_valid_layerCapture && irq_memory_commit && irq_memory_owned) begin
        assert(commitPacket_instruction_pc == irq_memory_pc && commitPacket_instruction_tag == irq_memory_tag);
        irq_memory_owned <= 0;
      end
      if (takeInterrupt_layerCapture) begin
        assert(_csr_interruptPending && !irq_memory_owned && !memoryPending && !irq_memory_commit);
        assert(!commit_output_valid_layerCapture && !formal_we && !formal_write);
        assert(redirect_0 && status_trap && !lsu_input_valid && !data_request_valid);
        assert(formal_trapPc == resumePc && formal_trapCause == csr_interruptCause_layerCapture && formal_trapValue == 0);
        assert(redirectPc == csr_trapVector_layerCapture);
      end
      if (commitValid && commitPacket_instruction_fault) assert(!takeInterrupt_layerCapture);
      if (_csr_interruptPending && !memoryPending && !irq_memory_commit && !(commitValid && commitPacket_instruction_fault))
        assert(takeInterrupt_layerCapture);
      if (past_valid && $past(!reset && data_request_valid && !data_request_ready)) begin
        assert(data_request_valid);
        assert($stable({{data_request_bits_address, data_request_bits_data, data_request_bits_tag,
          data_request_bits_mask, data_request_bits_size, data_request_bits_write,
          data_request_bits_fetch, data_request_bits_atomic, data_request_bits_atomicOperation, data_request_bits_scEligible}}));
      end
      if (past_valid) begin
        if ($past(reset)) assert(resumePc == 64'h{int(parameters['resetVector']):x});
        else if ($past(takeInterrupt_layerCapture)) begin
          assert(resumePc == $past(csr_trapVector_layerCapture));
          assert(!instructionValid && !decodedValid && !issuedValid && !resultValid && !memoryValid && !commitValid);
        end else if ($past(commit_output_valid_layerCapture)) assert(resumePc == $past(commit_output_bits_nextPc_layerCapture));
        else assert($stable(resumePc));
      end
      cover(_csr_interruptPending && memoryPending && data_request_valid && !data_request_ready);
      cover(_csr_interruptPending && memoryPending && data_request_valid && data_request_bits_atomic);
      cover(_csr_interruptPending && irq_memory_commit && !memoryPending);
      cover(takeInterrupt_layerCapture && !instructionValid && !decodedValid && !issuedValid && !resultValid && !memoryValid && !commitValid);
      cover(takeInterrupt_layerCapture && executePending);
      cover(takeInterrupt_layerCapture && $past(commit_output_valid_layerCapture && irq_memory_commit));
      cover(irq_service_age == 3 && takeInterrupt_layerCapture);
      cover(takeInterrupt_layerCapture && issuedValid && issuedPacket_decoded_instruction_instruction[6:0] == 7'h0f);
      cover(_csr_interruptPending && memoryPending && decodedValid && decodedPacket_instruction_instruction[6:0] == 7'h0f);
    end
  end
'''
    return [('InterruptCsr', csr, 'status[3]\n    &', "1'h1\n    &"),
            ('InterruptBackend', backend, '_csr_interruptPending & ~memoryPending', '_csr_interruptPending')]


def user_cases():
    csr = r'''
  reg user_past = 0;
  always @(posedge clock) begin
    user_past <= 1;
    if (!user_past) assume(reset);
    if (user_past) begin
      assert(privilege == 0 || privilege == 3);
      assert(status[12:11] == 0 || status[12:11] == 3);
      assert((status & ~64'h221888) == 0);
      if (privilege == 0) assert(!status[17]);
      assert(dataPrivilege == (status[17] ? status[12:11] : privilege));
      assert(wfiLegal == (privilege == 3 || !status[21]));
      if (privilege == 0) assert(!legal);
      if (readAddress == 12'h300 && legal) assert(readData[33:32] == 2);
      if ($past(reset)) begin
        assert(privilege == 3 && !status[3] && !status[17]);
      end else if ($past(trap)) begin
        assert(privilege == 3 && status[12:11] == $past(privilege));
        assert(!status[3] && status[7] == $past(status[3]));
        assert(status[17] == $past(status[17]) && status[21] == $past(status[21]));
      end else if ($past(mret)) begin
        assert(privilege == $past(status[12:11]) && status[12:11] == 0);
        assert(status[3] == $past(status[7]) && status[7]);
        assert(status[17] == ($past(status[12:11]) == 3 && $past(status[17])));
        assert(status[21] == $past(status[21]));
      end else begin
        assert(privilege == $past(privilege));
        if ($past(write && writeAddress == 12'h300)) begin
          assert(status[12:11] == ($past(writeData[12:11]) == 3 ? 3 : 0));
          assert(status[3] == $past(writeData[3]) && status[7] == $past(writeData[7]));
          assert(status[17] == $past(writeData[17]) && status[21] == $past(writeData[21]));
        end else assert($stable(status));
      end
      cover(privilege == 0 && !status[21]);
      cover(privilege == 0 && status[21]);
      cover(privilege == 3 && dataPrivilege == 0);
      cover($past(!reset && trap && privilege == 0) && privilege == 3);
      cover($past(!reset && mret && status[17] && status[12:11] == 3) && privilege == 3 && dataPrivilege == 0);
    end
  end
'''
    execute = r'''
  wire [4:0] u_op = input_bits_decoded_operation;
  wire u_fault = input_bits_decoded_instruction_fault;
  wire [31:0] u_word = input_bits_decoded_instruction_instruction;
  always @* begin
    assume(privilege == 0 || privilege == 3);
    if (u_op == 12 || u_op == 13 || u_op == 29) begin
      assert(output_bits_instruction_fault == (u_fault || u_op == 12 ||
        (u_op == 13 && privilege != 3) || (u_op == 29 && !wfiLegal)));
      if (u_fault) begin
        assert(output_bits_instruction_cause == input_bits_decoded_instruction_cause);
        assert(output_bits_instruction_tval == input_bits_decoded_instruction_tval);
      end else if (u_op == 12) begin
        assert(output_bits_instruction_cause == (privilege == 0 ? 8 : 11));
        assert(output_bits_instruction_tval == 0);
      end else if ((u_op == 13 && privilege != 3) || (u_op == 29 && !wfiLegal)) begin
        assert(output_bits_instruction_cause == 2 && output_bits_instruction_tval == {32'd0, u_word});
      end
    end
    cover(input_valid && !u_fault && u_op == 12 && privilege == 0);
    cover(input_valid && !u_fault && u_op == 13 && privilege == 0);
    cover(input_valid && !u_fault && u_op == 13 && privilege == 3);
    cover(input_valid && !u_fault && u_op == 29 && !wfiLegal);
  end
'''
    return [('UserCsr', csr, 'assign privilege =', 'assign privilege = 3 |'),
            ('UserExecute', execute, 'assign output_bits_instruction_cause =', 'assign output_bits_instruction_cause = 11 |')]


def supervisor_cases(parameters):
    csr = r'''
  reg supervisor_past = 0;
  wire [63:0] delegation = trapCause[63] ? mideleg : medeleg;
  wire route_supervisor = privilege != 3 && trapCause[62:6] == 0 && delegation[trapCause[5:0]];
  wire [11:0] source_pending = {interrupts_external, 3'b0, interrupts_timer, 3'b0, interrupts_software, 3'b0} |
    {2'b0, softwarePending[2], 3'b0, softwarePending[1], 3'b0, softwarePending[0], 1'b0};
  wire [11:0] active_sources = source_pending & enables;
  wire [11:0] machine_sources = active_sources & ~mideleg[11:0];
  wire [11:0] supervisor_sources = active_sources & mideleg[11:0];
  wire machine_eligible = (privilege != 3 || status[3]) && machine_sources != 0;
  wire supervisor_eligible = (privilege == 0 || privilege == 1 && status[1]) && supervisor_sources != 0;
  wire [11:0] selected_sources = machine_eligible ? machine_sources : supervisor_sources;
  wire [63:0] selected_cause = 64'h8000000000000000 | (selected_sources[11] ? 11 : selected_sources[3] ? 3 :
    selected_sources[7] ? 7 : selected_sources[9] ? 9 : selected_sources[1] ? 1 : 5);
  always @* begin
    assume(!write || writeAddress[9:8] <= privilege);
    assume(!mret || privilege == 3);
    assume(!sret || privilege == 3 || privilege == 1 && !status[22]);
    assume(!(write && (trap || mret || sret)) && !(mret && sret) && !(trap && (mret || sret)));
    if (supervisor_past) begin
    assert(dataPrivilege == (privilege == 3 && status[17] ? status[12:11] : privilege));
    assert(wfiLegal == (privilege == 3 || privilege == 1 && !status[21]));
    assert(sretLegal == (privilege == 3 || privilege == 1 && !status[22]));
    assert(trapVector == (route_supervisor ? stvec : mtvec));
    assert(returnPc == (sret ? sepc : mepc));
    assert(interruptPending == (machine_eligible || supervisor_eligible));
    assert(wakeup == (active_sources != 0));
    if (interruptPending) assert(interruptCause == selected_cause);
    if (readAddress == 12'h100) begin
      assert(legal == (privilege >= 1));
      if (legal) assert(readData == (64'h200000000 | (status & 64'h122)));
    end
    if (readAddress == 12'h180) assert(legal == (privilege == 3 || privilege == 1 && !status[20]) && readData == 0);
    if (readAddress == 12'h300 && privilege == 3) assert(legal && readData == (64'ha00000000 | status));
    if (readAddress == 12'h104 && privilege >= 1) assert(legal && readData == (enables & mideleg));
    if (readAddress == 12'h144 && privilege >= 1) assert(legal && readData == (source_pending & mideleg));
    if (readAddress[9:8] > privilege) assert(!legal);
    end
  end
  always @(posedge clock) begin
    supervisor_past <= 1;
    if (!supervisor_past) assume(reset);
    if (supervisor_past) begin
      assert(privilege == 0 || privilege == 1 || privilege == 3);
      assert(status[12:11] == 0 || status[12:11] == 1 || status[12:11] == 3);
      assert((status & ~64'h7219aa) == 0 && (medeleg & ~64'h3ff) == 0 && (mideleg & ~64'h222) == 0);
      assert((enables & ~12'haaa) == 0 && mepc[1:0] == 0 && sepc[1:0] == 0);
      if ($past(reset)) assert(privilege == 3 && status == 0 && medeleg == 0 && mideleg == 0);
      else begin
        if ($past(trap)) begin
          if ($past(route_supervisor)) begin
            assert(privilege == 1 && status[8] == ($past(privilege) == 1));
            assert(!status[1] && status[5] == $past(status[1]));
            assert(sepc == ($past(trapPc) & ~64'd3) && scause == $past(trapCause) && stval == $past(trapValue));
            assert($stable({mepc, mcause, mtval, status[12:11], status[7], status[3]}));
          end else begin
            assert(privilege == 3 && status[12:11] == $past(privilege));
            assert(!status[3] && status[7] == $past(status[3]));
            assert(mepc == ($past(trapPc) & ~64'd3) && mcause == $past(trapCause) && mtval == $past(trapValue));
            assert($stable({sepc, scause, stval, status[8], status[5], status[1]}));
          end
        end else if ($past(mret)) begin
          assert(privilege == $past(status[12:11]) && status[12:11] == 0);
          assert(status[3] == $past(status[7]) && status[7]);
          assert(status[17] == ($past(status[12:11]) == 3 && $past(status[17])));
          assert($stable({status[8], status[5], status[1]}));
        end else if ($past(sret)) begin
          assert(privilege == ($past(status[8]) ? 1 : 0) && !status[8] && !status[17]);
          assert(status[1] == $past(status[5]) && status[5]);
          assert($stable({status[12:11], status[7], status[3]}));
        end else assert($stable(privilege));
        if ($past(write && writeAddress == 12'h304)) assert(enables == ($past(writeData) & 12'haaa));
        else if ($past(write && writeAddress == 12'h104)) assert(enables == (($past(enables) & ~$past(mideleg[11:0])) | ($past(writeData[11:0]) & $past(mideleg[11:0]))));
        else assert($stable(enables));
        if ($past(write && writeAddress == 12'h344)) assert(softwarePending == {$past(writeData[9]), $past(writeData[5]), $past(writeData[1])});
        else if ($past(write && writeAddress == 12'h144 && mideleg[1])) assert(softwarePending == {$past(softwarePending[2:1]), $past(writeData[1])});
        else assert($stable(softwarePending));
      end
      cover(privilege == 1 && dataPrivilege == 1);
      cover(privilege == 3 && dataPrivilege == 1);
      cover($past(!reset && trap && route_supervisor && privilege == 0) && privilege == 1);
      cover($past(!reset && trap && route_supervisor && privilege == 1) && privilege == 1);
      cover($past(!reset && sret && status[8]) && privilege == 1);
      cover($past(!reset && sret && !status[8]) && privilege == 0);
      cover(privilege == 0 && supervisor_eligible && !status[1]);
      cover(privilege == 3 && supervisor_sources != 0 && !supervisor_eligible);
      cover(machine_eligible && supervisor_eligible);
    end
  end
'''
    if parameters.get('virtualAddressBits') == 39:
        csr = csr.replace("64'h122", "64'hc0122").replace("64'h7219aa", "64'h7e19aa").replace("64'h3ff", "64'hb3ff")
        csr = csr.replace("&& readData == 0);", "&& readData == translationState_satp);")
        root_fits = "1'b1" if parameters['physicalAddressBits'] == 56 else f"writeData[43:{parameters['physicalAddressBits']-12}] == 0"
        csr += f'''
  always @* if (supervisor_past) begin
    assert(sfenceLegal == (privilege == 3 || privilege == 1 && !status[20]));
    assert(translationState_sum == status[18] && translationState_mxr == status[19]);
    assert(translationState_satp[59:44] == 0);
    assert(translationState_satp[63:60] == 0 || translationState_satp[63:60] == 8);
  end
  always @(posedge clock) if (supervisor_past) begin
    if ($past(reset)) assert(translationState_satp == 0);
    else begin
      if ($past(write && writeAddress == 12'h180 && writeData[63:60] == 0)) assert(translationState_satp == 0);
      else if ($past(write && writeAddress == 12'h180 && writeData[63:60] == 8 && ({root_fits})))
        assert(translationState_satp == (64'h8000000000000000 | ($past(writeData) & 64'hfffffffffff)));
      else assert($stable(translationState_satp));
      if ($past(write && (writeAddress == 12'h100 || writeAddress == 12'h300)))
        assert(status[19:18] == $past(writeData[19:18]));
      else assert($stable(status[19:18]));
    end
    cover(translationState_satp[63:60] == 8 && translationState_sum && translationState_mxr);
    cover(privilege == 1 && !sfenceLegal && readAddress == 12'h180 && !legal);
    cover($past(write && writeAddress == 12'h180 && writeData[63:60] != 0 && writeData[63:60] != 8) && $stable(translationState_satp));
  end
'''
    execute = r'''
  wire [4:0] s_op = input_bits_decoded_operation;
  wire s_prior_fault = input_bits_decoded_instruction_fault;
  wire s_illegal = s_op == 31 && !sretLegal || s_op == 13 && privilege != 3 || s_op == 29 && !wfiLegal;
  always @* begin
    assume(privilege == 0 || privilege == 1 || privilege == 3);
    if (s_op == 12 || s_op == 13 || s_op == 29 || s_op == 31) begin
      assert(output_bits_instruction_fault == (s_prior_fault || s_op == 12 || s_illegal));
      if (!s_prior_fault && s_op == 12) assert(output_bits_instruction_cause == (privilege == 3 ? 11 : privilege == 1 ? 9 : 8));
      if (!s_prior_fault && s_illegal) assert(output_bits_instruction_cause == 2 && output_bits_instruction_tval == {32'd0, input_bits_decoded_instruction_instruction});
      assert(output_bits_sret == (s_op == 31));
    end
    cover(input_valid && !s_prior_fault && s_op == 31 && sretLegal && privilege == 1);
    cover(input_valid && !s_prior_fault && s_op == 31 && !sretLegal && privilege == 1);
    cover(input_valid && !s_prior_fault && s_op == 12 && privilege == 1);
  end
'''
    if parameters.get('virtualAddressBits') == 39:
        execute += r'''
  wire s_sfence = s_op == 16 && (input_bits_decoded_instruction_instruction & 32'hfe007fff) == 32'h12000073;
  always @* begin
    assert(output_bits_sfenceVma == s_sfence);
    if (s_sfence) begin
      assert(output_bits_instruction_fault == (s_prior_fault || !sfenceLegal));
      if (!s_prior_fault && !sfenceLegal) assert(output_bits_instruction_cause == 2 &&
        output_bits_instruction_tval == {32'd0, input_bits_decoded_instruction_instruction});
    end
    cover(input_valid && s_sfence && !s_prior_fault && sfenceLegal);
    cover(input_valid && s_sfence && !s_prior_fault && !sfenceLegal);
  end
'''
    fetch = r'''
  reg context_past = 0, context_owned = 0, context_cancelled = 0;
  reg [1:0] retained_fetch_mode;
  wire context_lookup = state == 0 || PIPELINED && output_valid && output_ready && !output_bits_fault;
  wire [1:0] context_mode = context_lookup ? privilege : retained_fetch_mode;
  always @(posedge clock) begin
    context_past <= 1;
    if (!context_past) assume(reset); else assume(!reset);
    if (reset) context_owned <= 0;
    else begin
      if (request_valid && request_ready) begin
        context_owned <= 1; context_cancelled <= 0;
        retained_fetch_mode <= privilege;
      end else if (state == 0) context_owned <= 0;
      if (context_owned && cancel) context_cancelled <= 1;
      if (cancel || context_cancelled) assert(!output_valid);
      if (state != 0) assert(context_owned && formal_fetch_mode == context_mode);
      if (request_valid && request_ready) assert(formal_fetch_mode == privilege);
      if (formal_fetch_request_valid) assert(formal_fetch_privileged == (context_mode != 0));
      cover(state != 0 && retained_fetch_mode == 1 && privilege == 3);
      cover(formal_fetch_request_valid && retained_fetch_mode == 1 && privilege == 3);
      cover(formal_fetch_request_valid && retained_fetch_mode == 0 && privilege == 3);
    end
  end
'''
    pipelined = bool(parameters.get('iCacheBytes')) and parameters.get('virtualAddressBits') != 39
    fetch = fetch.replace('PIPELINED', str(int(pipelined)))
    if pipelined and parameters['issueWidth'] > 1:
        banks = 1 << (parameters['issueWidth'] - 1).bit_length()
        fetch = fetch.replace('&& !output_bits_fault;', f'&& !output_bits_fault && output_bits_count >= {banks} - output_bits_pc[{banks.bit_length()}:2];')
    if pipelined:
        fetch += '\n  always @(posedge clock) if (!reset) cover(state != 0 && request_valid && request_ready && retained_fetch_mode != privilege);\n'
    return [('SupervisorCsr', csr, 'assign trapVector = supervisorTrap_1 ? stvec : mtvec;', 'assign trapVector = mtvec;'),
            ('SupervisorExecute', execute, 'assign output_bits_instruction_cause =', 'assign output_bits_instruction_cause = 11 |'),
            ('SupervisorFetch', fetch, 'wire [1:0] formal_fetch_mode =', "wire [1:0] formal_fetch_mode = 2'd3 |")]


def translation_case(parameters):
    ordinary = ' || '.join(f"(walk_address >= 64'h{int(region['base']):x} && walk_address <= 64'h{int(region['base']) + int(region['size']) - 8:x})"
                          for region in parameters['memoryRegions'] if region['readable'] and not region['device'] and int(region['size']) >= 8) or "1'b0"
    permit = '_pmp_allowed' if parameters['pmpEntries'] else "1'b1"
    body = f'''
  wire formal_permit = {permit};
  wire ordinary = ({ordinary}) && walk_address <= 64'h{(1 << parameters['physicalAddressBits']) - 8:x};
''' + r'''
  reg translation_past = 0, active, client, priority_client, translation_cancelled;
  reg bus_owned, offered, denied, done, expected_fault, expected_page_fault, completed_leaf;
  reg [63:0] virtual_address, walk_address, expected_address;
  reg [1:0] effective_privilege, walk_level;
  reg fetch_access, write_access, allow_sum, allow_mxr;
  wire cancel_now = translation_cancelled || cancelInstruction && !client;
  wire data_selected = ports_1_request_valid && (!(ports_0_request_valid && !cancelInstruction) || priority_client);
  wire [63:0] access_cause = fetch_access ? 1 : write_access ? 7 : 5;
  wire [63:0] page_cause = fetch_access ? 12 : write_access ? 15 : 13;
  wire [63:0] pte = memory_response_bits_data;
  wire leaf_pte = pte[1] || pte[3];
  wire access_allowed = fetch_access ? pte[3] : write_access ? pte[2] : pte[1] || allow_mxr && pte[3];
  wire mode_allowed = effective_privilege == 0 ? pte[4] : !pte[4] || allow_sum && !fetch_access;
  wire bad_alignment = walk_level == 2 && pte[27:10] != 0 || walk_level == 1 && pte[18:10] != 0;
  wire bad_pte = !pte[0] || !pte[1] && pte[2] || pte[63:54] != 0 ||
    (leaf_pte ? !access_allowed || !mode_allowed || bad_alignment || !pte[6] || write_access && !pte[7] :
      walk_level == 0 || pte[4] || pte[6] || pte[7]);
  wire [63:0] page_mask = walk_level == 2 ? 64'h3fffffff : walk_level == 1 ? 64'h1fffff : 64'hfff;
  wire [63:0] leaf_address = ((pte >> 10 << 12) & ~page_mask) | (virtual_address & page_mask);
  wire [63:0] next_address = ((pte >> 10) & 64'hfffffffffff) * 4096 +
    ((walk_level == 2 ? (virtual_address >> 21) : (virtual_address >> 12)) & 511) * 8;
  wire any_response = ports_0_response_valid || ports_1_response_valid;
  always @(posedge clock) begin
    translation_past <= 1;
    if (!translation_past) assume(reset); else assume(!reset);
    if (reset) begin
      active <= 0; priority_client <= 0; translation_cancelled <= 0;
      bus_owned <= 0; offered <= 0; denied <= 0; done <= 0;
    end else begin
      assert(state <= 4 && active == (state != 0) && priority_client == next);
      assert(bus_owned == (state == 3));
      if (active) begin
        assert(owner == client && request_address == virtual_address && request_privilege == effective_privilege);
        assert(request_fetch == fetch_access && request_write == write_access && sum == allow_sum && mxr == allow_mxr);
        assert(killed == translation_cancelled);
        if (state != 4) begin
          assert(address == walk_address && level == walk_level && walk_level <= 2 && !done && !denied);
          assert(expected_address == virtual_address && !expected_fault && !expected_page_fault && !completed_leaf);
          assert(!fault && !pageFault);
        end
        if (state == 2 || state == 3) assert(offered || state == 2);
        if (state != 2) assert(offered == (state == 3));
      end
      assume(!memory_response_valid || bus_owned);
      if ($past(!reset && memory_response_valid && !memory_response_ready)) begin
        assume(memory_response_valid);
        assume($stable({memory_response_bits_data, memory_response_bits_fault, memory_response_bits_tag, memory_response_bits_last}));
      end
      assert(!(ports_0_request_ready && ports_1_request_ready));
      assert(ports_0_request_ready == (!active && !data_selected && !cancelInstruction));
      assert(ports_1_request_ready == (!active && data_selected));
      assert(!memory_response_ready || bus_owned);
      assert(!(ports_0_response_valid && ports_1_response_valid));
      if (active && !done && !offered && !bus_owned && !memory_request_valid && (!ordinary || !formal_permit)) denied <= 1;
      if (active && cancelInstruction && !client) begin
        translation_cancelled <= 1;
        if (!done && !offered && !bus_owned && !memory_request_valid) done <= 1;
      end
      if (memory_request_valid) begin
        assert(active && !done && !bus_owned);
        assert(!translation_cancelled || offered);
        assert(memory_request_bits_address == walk_address);
        assert(memory_request_bits_size == 3 && memory_request_bits_data == 0 && memory_request_bits_mask == 0 && memory_request_bits_tag == 0);
        assert(memory_request_bits_privileged && !memory_request_bits_write && !memory_request_bits_fetch && !memory_request_bits_atomic && !memory_request_bits_atomicOperation && !memory_request_bits_scEligible);
        if (!offered) assert($past(ordinary && formal_permit));
        offered <= 1;
        if (memory_request_ready) bus_owned <= 1;
      end
      if (memory_response_valid && memory_response_ready) begin
        assert(bus_owned && active && offered && !done);
        bus_owned <= 0; offered <= 0; denied <= 0; done <= 1;
        if (!cancel_now) begin
          if (memory_response_bits_fault || memory_response_bits_tag != 0) expected_fault <= 1;
          else if (bad_pte) begin expected_fault <= 1; expected_page_fault <= 1; end
          else if (leaf_pte) begin expected_address <= leaf_address; completed_leaf <= 1; end
          else begin walk_address <= next_address; walk_level <= walk_level - 1; done <= 0; end
        end
      end
      if (any_response) begin
        assert(active && !bus_owned && (done || denied));
        assert(ports_0_response_valid == !client && ports_1_response_valid == client);
        assert(ports_0_response_bits_address == expected_address && ports_1_response_bits_address == expected_address);
        assert(ports_0_response_bits_fault == (expected_fault || !done) && ports_1_response_bits_fault == (expected_fault || !done));
        assert(ports_0_response_bits_cause == ((expected_fault || !done) ? (expected_page_fault ? page_cause : access_cause) : 0));
        assert(ports_1_response_bits_cause == ports_0_response_bits_cause);
        if (!done) begin done <= 1; expected_fault <= 1; end
        if (client ? ports_1_response_ready : ports_0_response_ready) begin
          active <= 0; priority_client <= !client;
        end
      end
      if ($past(!reset && memory_request_valid && !memory_request_ready)) begin
        assert(memory_request_valid);
        assert($stable({memory_request_bits_address, memory_request_bits_data, memory_request_bits_size,
          memory_request_bits_mask, memory_request_bits_tag, memory_request_bits_write, memory_request_bits_fetch,
          memory_request_bits_privileged, memory_request_bits_atomic, memory_request_bits_atomicOperation, memory_request_bits_scEligible}));
      end
      if ($past(!reset && any_response && !(client ? ports_1_response_ready : ports_0_response_ready))) begin
        assert(any_response);
        assert($stable({ports_0_response_valid, ports_1_response_valid, ports_0_response_bits_address,
          ports_0_response_bits_fault, ports_0_response_bits_cause}));
      end
      cover(memory_request_valid && !memory_request_ready && cancelInstruction && !client);
      cover(cancel_now && bus_owned && memory_response_valid && memory_response_ready && !leaf_pte);
      cover(any_response && expected_page_fault && write_access);
      cover(any_response && expected_fault && !expected_page_fault);
      cover(any_response && completed_leaf && walk_level == 0);
      cover(any_response && completed_leaf && walk_level == 1);
      cover(any_response && completed_leaf && walk_level == 2);
    end
''' + ''.join(f'''
    if (!reset && ports_{port}_request_valid && ports_{port}_request_ready) begin
      assert(!active);
      active <= 1; client <= {port}; translation_cancelled <= 0; offered <= 0; denied <= 0;
      bus_owned <= 0; expected_fault <= 0; expected_page_fault <= 0; completed_leaf <= 0; done <= 1;
      virtual_address <= ports_{port}_request_bits_address;
      effective_privilege <= ports_{port}_request_bits_privilege;
      fetch_access <= ports_{port}_request_bits_fetch; write_access <= ports_{port}_request_bits_write;
      allow_sum <= state_sum; allow_mxr <= state_mxr; walk_level <= 2;
      expected_address <= ports_{port}_request_bits_address;
      walk_address <= (state_satp & 64'hfffffffffff) * 4096 + ((ports_{port}_request_bits_address >> 30) & 511) * 8;
      if (ports_{port}_request_bits_privilege != 3 && state_satp[63:60] != 0) begin
        done <= 0;
        if (state_satp[63:60] != 8 || ports_{port}_request_bits_address[63:39] != {{25{{ports_{port}_request_bits_address[38]}}}}) begin
          done <= 1; expected_fault <= 1; expected_page_fault <= 1;
        end
      end
    end
''' for port in range(2)) + '  end\n'
    if parameters.get('tlbEntries'):
        count = parameters['tlbEntries']
        hit = [f"(tlbValid[{i}] && (virtual_address[38:12] >> (9 * tlb_{i}_level)) == (tlb_{i}_vpn >> (9 * tlb_{i}_level)))" for i in range(count)]
        cached_pte = ''.join(f'{hit[i]} ? tlb_{i}_pte : ' for i in range(count)) + "64'd0"
        cached_level = ''.join(f'{hit[i]} ? tlb_{i}_level : ' for i in range(count)) + "2'd0"
        declarations = f'''
  wire cached_hit = ({' || '.join(hit)}) && !invalidate;
  wire [63:0] cached_pte = {cached_pte};
  wire [1:0] cached_level = {cached_level};
  wire [63:0] cached_mask = cached_level == 2 ? 64'h3fffffff : cached_level == 1 ? 64'h1fffff : 64'hfff;
  wire [63:0] cached_address = ((cached_pte >> 10 << 12) & ~cached_mask) | (virtual_address & cached_mask);
  wire cached_access = fetch_access ? cached_pte[3] : write_access ? cached_pte[2] : cached_pte[1] || allow_mxr && cached_pte[3];
  wire cached_mode = effective_privilege == 0 ? cached_pte[4] : !cached_pte[4] || allow_sum && !fetch_access;
  wire cached_denied = !cached_access || !cached_mode || !cached_pte[6] || write_access && !cached_pte[7];
  reg cache_refill_allowed = 0;
  wire cache_leaf = bus_owned && memory_response_valid && memory_response_ready && !cancel_now &&
    !memory_response_bits_fault && memory_response_bits_tag == 0 && !bad_pte && leaf_pte;
  wire cache_fill = cache_leaf && cache_refill_allowed && !invalidate;
'''
        body = body.replace('  always @(posedge clock) begin\n    translation_past', declarations + '  always @(posedge clock) begin\n    translation_past')
        body = body.replace('assert(state <= 4', 'assert(state <= 5')
        body = body.replace('if (active && !done && !offered && !bus_owned && !memory_request_valid && (!ordinary || !formal_permit))', 'if (state == 1 && active && !done && !offered && !bus_owned && !memory_request_valid && (!ordinary || !formal_permit))')
        body = body.replace('      if (any_response) begin', '''      if (state == 5 && (cached_hit || cancel_now)) begin
        done <= 1;
        expected_address <= cancel_now || cached_denied ? virtual_address : cached_address;
        expected_fault <= !cancel_now && cached_denied;
        expected_page_fault <= !cancel_now && cached_denied;
        completed_leaf <= !cancel_now && !cached_denied;
        walk_level <= cached_level;
      end
      if (any_response) begin''')
        body += '''
  always @(posedge clock) begin
    if (reset) cache_refill_allowed <= 0;
    else if (invalidate) cache_refill_allowed <= 0;
    else if (ports_0_request_valid && ports_0_request_ready || ports_1_request_valid && ports_1_request_ready)
      cache_refill_allowed <= 1;
    if (translation_past) begin
      assert(refillAllowed == cache_refill_allowed);
      if ($past(reset || invalidate)) assert(tlbValid == 0 && replacement == 0);
      else begin
        if ($past(cache_fill)) assert(replacement == ($past(replacement) + 1) % CACHE_COUNT);
        else assert($stable({tlbValid, replacement}));
'''.replace('CACHE_COUNT', str(count))
        for i in range(count):
            overlap = f'((tlb_{i}_vpn >> (9 * (tlb_{i}_level > walk_level ? tlb_{i}_level : walk_level))) == (virtual_address[38:12] >> (9 * (tlb_{i}_level > walk_level ? tlb_{i}_level : walk_level))))'
            body += f'''
        if ($past(cache_fill)) begin
          assert(tlbValid[{i}] == ($past(replacement) == {i} || $past(tlbValid[{i}] && !{overlap})));
          if ($past(replacement) == {i}) begin
            assert(tlb_{i}_vpn == $past(virtual_address[38:12]) && tlb_{i}_pte == $past(memory_response_bits_data));
            assert(tlb_{i}_level == $past(walk_level));
          end else assert($stable({{tlb_{i}_vpn, tlb_{i}_pte, tlb_{i}_level}}));
        end else assert($stable({{tlb_{i}_vpn, tlb_{i}_pte, tlb_{i}_level}}));
'''
        body += '''      end
      cover(state == 5 && cached_hit && !cached_denied && !cancel_now);
      cover(state == 5 && cached_hit && cached_denied && write_access && !cancel_now);
      cover(cache_leaf && cache_refill_allowed && invalidate);
      cover(any_response && !cache_refill_allowed && !fault);
    end
  end
'''
        for i in range(count):
            body += f'''
  always @* if (translation_past && tlbValid[{i}]) begin
    assert(tlb_{i}_level <= 2 && tlb_{i}_pte[63:54] == 0 && tlb_{i}_pte[0] && tlb_{i}_pte[6]);
    assert((tlb_{i}_pte[1] || tlb_{i}_pte[3]) && (tlb_{i}_pte[1] || !tlb_{i}_pte[2]));
    assert(tlb_{i}_level != 2 || tlb_{i}_pte[27:10] == 0);
    assert(tlb_{i}_level != 1 || tlb_{i}_pte[18:10] == 0);
  end
'''
    body = re.sub(r'\bpte\b', 'formal_pte', body)
    return ('Translation', body, 'assign memory_request_bits_size = 3\'h3;', "assign memory_request_bits_size = 3'h2;")


def synchronization_case(parameters):
    body = r'''
  reg sync_past = 0, sync_memory_owned, sync_bus_owned, sync_sent, sync_replied;
  reg sync_barrier_owned, sync_prior_memory, sync_after_fence;
  reg [63:0] sync_memory_pc, sync_barrier_pc;
  reg [7:0] sync_memory_tag, sync_barrier_tag;
  function sync_encoding(input [31:0] word);
    sync_encoding = word[6:0] == 7'h0f && word[14:12] <= 1;
  endfunction
  wire sync_decoded = decodedValid && !decodedPacket_instruction_fault &&
    sync_encoding(decodedPacket_instruction_instruction);
  wire sync_retired = commit_output_valid_layerCapture &&
    sync_encoding(commitPacket_instruction_instruction);
  wire sync_memory_retired = commit_output_valid_layerCapture && (commitPacket_load || commitPacket_store);
  wire [63:0] sync_sequential = commitPacket_instruction_pc + commitPacket_instruction_length;
  wire [2:0] sync_barriers =
    {2'b0, issuedValid && !issuedPacket_decoded_instruction_fault && sync_encoding(issuedPacket_decoded_instruction_instruction)} +
    {2'b0, resultValid && !resultPacket_instruction_fault && sync_encoding(resultPacket_instruction_instruction)} +
    {2'b0, memoryValid && !memoryPacket_instruction_fault && sync_encoding(memoryPacket_instruction_instruction)} +
    {2'b0, commitValid && !commitPacket_instruction_fault && sync_encoding(commitPacket_instruction_instruction)};
  always @(posedge clock) begin
    sync_past <= 1;
    if (!sync_past) assume(reset); else assume(!reset);
    if (reset) begin
      sync_memory_owned <= 0; sync_bus_owned <= 0; sync_sent <= 0; sync_replied <= 0;
      sync_barrier_owned <= 0; sync_prior_memory <= 0; sync_after_fence <= 0;
    end else begin
      assert(memoryPending == (data_request_valid || data_response_ready || _lsu_output_valid));
      assert(data_response_ready == sync_bus_owned);
      assert(!sync_replied || sync_sent);
      if (sync_bus_owned) assert(sync_sent && !sync_replied);
      if (data_request_valid) assert(sync_memory_owned && !sync_sent && !sync_replied);
      if (memoryPending) assert(sync_memory_owned);
      if (lsu_input_valid && _lsu_input_ready) begin
        assert(!sync_memory_owned && !sync_barrier_owned);
        sync_memory_owned <= 1; sync_sent <= 0; sync_replied <= 0;
        sync_memory_pc <= resultPacket_instruction_pc;
        sync_memory_tag <= resultPacket_instruction_tag;
      end
      if (data_request_valid && data_request_ready) begin
        assert(sync_memory_owned && !sync_bus_owned && !sync_barrier_owned);
        sync_bus_owned <= 1; sync_sent <= 1;
      end
      if (data_response_valid && data_response_ready) begin
        assert(sync_memory_owned && sync_bus_owned);
        sync_bus_owned <= 0; sync_replied <= 1;
      end
      if (sync_memory_retired && sync_memory_owned) begin
        assert(!sync_bus_owned && (!sync_sent || sync_replied));
        assert(commitPacket_instruction_pc == sync_memory_pc && commitPacket_instruction_tag == sync_memory_tag);
        assert(sync_sent || commitPacket_instruction_fault);
        sync_memory_owned <= 0; sync_prior_memory <= 1;
      end
      if (sync_memory_owned) begin
        assert(memoryPending || (commitValid && (commitPacket_load || commitPacket_store)));
        if (memoryPending) begin
          assert(memoryValid && memoryPacket_instruction_pc == sync_memory_pc && memoryPacket_instruction_tag == sync_memory_tag);
          assert(!commitValid);
          assert(_lsu_output_bits_load || _lsu_output_bits_store);
          assert(_lsu_output_bits_instruction_pc == sync_memory_pc && _lsu_output_bits_instruction_tag == sync_memory_tag);
        end
        if (sync_sent) assert(sync_replied != sync_bus_owned);
      end
      if (sync_bus_owned) assert(sync_memory_owned && memoryPending);
      if (decodedValid) assert((decodedPacket_operation == 17) ==
        (sync_encoding(decodedPacket_instruction_instruction) && decodedPacket_instruction_instruction[12]));
      if (issuedValid) assert((issuedPacket_decoded_operation == 17) ==
        (sync_encoding(issuedPacket_decoded_instruction_instruction) && issuedPacket_decoded_instruction_instruction[12]));
      if (resultValid) assert(resultPacket_fenceI ==
        (sync_encoding(resultPacket_instruction_instruction) && resultPacket_instruction_instruction[12]));
      if (memoryValid) assert(memoryPacket_fenceI ==
        (sync_encoding(memoryPacket_instruction_instruction) && memoryPacket_instruction_instruction[12]));
      if (commitValid) assert(commitPacket_fenceI ==
        (sync_encoding(commitPacket_instruction_instruction) && commitPacket_instruction_instruction[12]));
      if (memoryPending) assert(!_lsu_output_bits_fenceI);
      if (sync_decoded) begin
        assert(decodedPacket_operation == (decodedPacket_instruction_instruction[12] ? 17 : 16));
        assert(decodedPacket_serializing && !decodedPacket_usesRs1 && !decodedPacket_usesRs2 && !decodedPacket_writesRd);
        if (issued) begin
          assert(!sync_memory_owned && !sync_bus_owned && !issuedValid && !resultValid && !memoryValid && !commitValid);
          assert(!sync_barrier_owned);
          sync_barrier_owned <= 1;
          sync_barrier_pc <= decodedPacket_instruction_pc;
          sync_barrier_tag <= decodedPacket_instruction_tag;
        end
      end
      if (issuedValid && !issuedPacket_decoded_instruction_fault && sync_encoding(issuedPacket_decoded_instruction_instruction)) begin
        assert(sync_barrier_owned);
        assert(issuedPacket_decoded_operation == (issuedPacket_decoded_instruction_instruction[12] ? 17 : 16));
        assert(!issuedPacket_decoded_writesRd);
      end
      if (resultValid && !resultPacket_instruction_fault && sync_encoding(resultPacket_instruction_instruction)) begin
        assert(sync_barrier_owned && !resultPacket_load && !resultPacket_store && !resultPacket_rdWrite && !resultPacket_csrWrite && !resultPacket_mret);
        assert(resultPacket_fenceI == resultPacket_instruction_instruction[12]);
        assert(resultPacket_nextPc == resultPacket_instruction_pc + resultPacket_instruction_length);
      end
      if (commitValid && !commitPacket_instruction_fault && sync_encoding(commitPacket_instruction_instruction)) begin
        assert(sync_barrier_owned && !commitPacket_load && !commitPacket_store && !commitPacket_rdWrite && !commitPacket_csrWrite && !commitPacket_mret);
        assert(commitPacket_fenceI == commitPacket_instruction_instruction[12]);
        assert(commitPacket_nextPc == sync_sequential);
      end
      if (memoryValid && !memoryPacket_instruction_fault && sync_encoding(memoryPacket_instruction_instruction)) begin
        assert(sync_barrier_owned && !memoryPacket_load && !memoryPacket_store && !memoryPacket_rdWrite && !memoryPacket_csrWrite && !memoryPacket_mret && !memoryPacket_sret);
        assert(memoryPacket_instruction_pc == sync_barrier_pc && memoryPacket_instruction_tag == sync_barrier_tag);
        assert(memoryPacket_nextPc == memoryPacket_instruction_pc + memoryPacket_instruction_length);
      end
      if (memoryPending) assert(!sync_encoding(_lsu_output_bits_instruction_instruction));
      if (sync_barrier_owned) begin
        assert(sync_barriers == 1);
        assert(!sync_memory_owned && !sync_bus_owned && !data_request_valid && !lsu_input_valid);
        assert((issuedValid && sync_encoding(issuedPacket_decoded_instruction_instruction) && !issuedPacket_decoded_instruction_fault) ||
          (resultValid && sync_encoding(resultPacket_instruction_instruction) && !resultPacket_instruction_fault) ||
          (memoryValid && sync_encoding(memoryPacket_instruction_instruction) && !memoryPacket_instruction_fault) ||
          (commitValid && sync_encoding(commitPacket_instruction_instruction) && !commitPacket_instruction_fault));
        if (issuedValid && sync_encoding(issuedPacket_decoded_instruction_instruction) && !issuedPacket_decoded_instruction_fault)
          assert(issuedPacket_decoded_instruction_pc == sync_barrier_pc && issuedPacket_decoded_instruction_tag == sync_barrier_tag);
        if (resultValid && sync_encoding(resultPacket_instruction_instruction) && !resultPacket_instruction_fault)
          assert(resultPacket_instruction_pc == sync_barrier_pc && resultPacket_instruction_tag == sync_barrier_tag);
        if (commit_output_valid_layerCapture) begin
          assert(sync_retired && !commitPacket_instruction_fault);
          assert(commitPacket_instruction_pc == sync_barrier_pc && commitPacket_instruction_tag == sync_barrier_tag);
        end
      end
      if (sync_retired) begin
        assert(!sync_memory_owned && !sync_bus_owned);
        assert(!commit_output_bits_rdWrite_layerCapture && !_commit_output_bits_csrWrite && !_commit_output_bits_mret);
        if (!commitPacket_instruction_fault) begin
          assert(sync_barrier_owned);
          assert(commit_output_bits_nextPc_layerCapture == sync_sequential);
          assert(_commit_output_bits_fenceI == commitPacket_instruction_instruction[12]);
          if (commitPacket_instruction_instruction[12])
            assert(redirect_0 && redirectPc == sync_sequential && !data_request_valid && !issued && !executed);
          else begin
            assert(!redirect_0);
            sync_after_fence <= 1;
          end
        end else assert(!_commit_output_bits_fenceI);
        sync_barrier_owned <= 0;
      end
      if (redirect_0) sync_barrier_owned <= 0;
      if (sync_past && $past(!reset && sync_retired && !commitPacket_instruction_fault &&
          commitPacket_instruction_instruction[12]))
        assert(!instructionValid && !decodedValid && !issuedValid && !resultValid && !memoryValid && !commitValid);
      cover(sync_decoded && sync_memory_owned && data_request_valid && !data_request_ready);
      cover(sync_decoded && sync_bus_owned && !data_response_valid);
      cover(sync_prior_memory && sync_retired && !commitPacket_instruction_fault && !commitPacket_instruction_instruction[12]);
      cover(sync_prior_memory && sync_retired && !commitPacket_instruction_fault && commitPacket_instruction_instruction[12]);
      cover(sync_barrier_owned && issuedValid && issuedPacket_decoded_instruction_instruction[6:0] == 7'h23);
      cover(sync_after_fence && data_request_valid && data_request_ready);
      cover(sync_retired && commitPacket_instruction_fault && commitPacket_instruction_instruction[12]);
    end
  end
'''
    if parameters.get('enableInterrupts'):
        body += '''  always @(posedge clock) if (!reset) begin
    if (takeInterrupt_layerCapture) assert(!sync_memory_owned && !sync_bus_owned);
  end
'''
    if parameters.get('iCacheBytes'):
        body += '''  always @(posedge clock) if (!reset) begin
    assert(invalidate == (commit_output_valid_layerCapture &&
      ((sync_retired && !commitPacket_instruction_fault && commitPacket_instruction_instruction[12]) || PMP_UPDATE)));
    if (invalidate) assert(redirect_0);
  end
'''.replace('PMP_UPDATE', 'pmpUpdate' if parameters['pmpEntries'] else "1'h0")
    for lane in range(1, parameters['issueWidth']):
        p = f'decodedPackets_{lane}'
        body += f'''  always @(posedge clock) if (!reset && decodedCount > {lane}) begin
    assert(({p}_operation == 17) == (sync_encoding({p}_instruction_instruction) && {p}_instruction_instruction[12]));
    if (sync_encoding({p}_instruction_instruction) && !{p}_instruction_fault)
      assert({p}_operation == ({p}_instruction_instruction[12] ? 17 : 16) &&
        {p}_serializing && !{p}_usesRs1 && !{p}_usesRs2 && !{p}_writesRd);
  end
'''
    return ('SynchronizationBackend', body, '| _commit_output_bits_fenceI', "| 1'h0 & _commit_output_bits_fenceI")


def wfi_cases(parameters):
    backend = r'''
  reg wfi_past = 0, wfi_wait = 0, wfi_slept = 0;
  reg [63:0] wfi_pc;
  wire wfi_retired = commit_output_valid_layerCapture &&
    commitPacket_instruction_instruction == 32'h10500073 && !commitPacket_instruction_fault;
  always @(posedge clock) begin
    wfi_past <= 1;
    if (!wfi_past) assume(reset); else assume(!reset);
    if (reset) begin wfi_wait <= 0; wfi_slept <= 0; end
    else begin
      assert(status_sleep == wfi_wait);
      if (decodedValid) assert((decodedPacket_operation == 29) == (decodedPacket_instruction_instruction == 32'h10500073));
      if (decodedValid && decodedPacket_operation == 29) assert(!decodedPacket_writesRd && decodedPacket_serializing == !decodedPacket_instruction_fault);
      if (issuedValid) begin
        assert((issuedPacket_decoded_operation == 29) == (issuedPacket_decoded_instruction_instruction == 32'h10500073));
        if (issuedPacket_decoded_operation == 29) assert(!issuedPacket_decoded_writesRd && issuedCount == 1);
      end
      if (decodedValid && decodedPacket_instruction_instruction == 32'h10500073 && !decodedPacket_instruction_fault) begin
        assert(decodedPacket_operation == 29 && decodedPacket_serializing && !decodedPacket_writesRd);
        if (issued) assert(!issuedValid && !resultValid && !memoryValid && !commitValid && !memoryPending);
      end
      if (resultValid) assert(resultPacket_wfi == (resultPacket_instruction_instruction == 32'h10500073));
      if (resultValid && resultPacket_wfi) assert(!resultPacket_load && !resultPacket_store && !resultPacket_csrWrite && !resultPacket_rdWrite && !resultPacket_mret);
      if (memoryPending) assert(!_lsu_output_bits_wfi && _lsu_output_bits_instruction_instruction != 32'h10500073);
      if (commitValid) begin
        assert(commitPacket_wfi == (commitPacket_instruction_instruction == 32'h10500073));
        assert(_commit_output_bits_wfi == (commitPacket_wfi && !commitPacket_instruction_fault));
      end
      if (wfi_retired) begin
        assert(redirect_0 && redirectPc == commitPacket_instruction_pc + commitPacket_instruction_length);
        assert(!memoryPending && !data_request_valid && !lsu_input_valid && !issued && !executed);
        assert(!commit_output_bits_rdWrite_layerCapture && !_commit_output_bits_csrWrite && !_commit_output_bits_mret);
        wfi_wait <= IRQ_ENABLED;
        wfi_pc <= commitPacket_instruction_pc + commitPacket_instruction_length;
      end
      if (WAKE || status_trap) wfi_wait <= 0;
      if (wfi_wait) begin
        wfi_slept <= 1;
        assert(!instructionValid && !decodedValid && !issuedValid && !resultValid && !memoryValid && !commitValid);
        assert(!instruction_ready && !data_request_valid && !memoryPending);
        assert(!issued && !executed && !multiply_input_valid);
        PC_ASSERT
      end
      if (wfi_past && $past(!reset && wfi_retired)) begin
        assert(!instructionValid && !decodedValid && !issuedValid && !resultValid && !memoryValid && !commitValid);
        RESUME_ASSERT
      end
      assert(!memoryPending || (memoryValid && !commitValid && !memoryPacket_instruction_fault && (memoryPacket_load || memoryPacket_store)));
      assert(memoryPending == (data_request_valid || data_response_ready || _lsu_output_valid));
      cover(wfi_retired && !WAKE);
      cover(wfi_retired && WAKE);
      cover(wfi_wait && !WAKE && executePending);
      cover(wfi_wait && WAKE);
      cover(wfi_slept && !wfi_wait && instruction_valid && instruction_ready);
    end
  end
'''
    for stage in ('result', 'memory', 'commit'):
        packet = stage + 'Packet'
        backend += f'''  always @(posedge clock) if (!reset && {stage}Valid) begin
    assert({packet}_wfi == ({packet}_instruction_instruction == 32'h10500073));
    if ({packet}_wfi) assert({stage}Count == 1 && !{packet}_load && !{packet}_store && !{packet}_rdWrite && !{packet}_csrWrite &&
      !{packet}_mret && !{packet}_sret && {packet}_nextPc == {packet}_instruction_pc + {packet}_instruction_length);
  end
'''
    for lane in range(1, parameters['issueWidth']):
        p = f'decodedPackets_{lane}'
        backend += f'''  always @(posedge clock) if (!reset && decodedCount > {lane}) begin
    assert(({p}_operation == 29) == ({p}_instruction_instruction == 32'h10500073));
    if ({p}_operation == 29) assert(!{p}_writesRd && {p}_serializing == !{p}_instruction_fault);
  end
'''
    interrupts = parameters.get('enableInterrupts')
    for key, value in (('IRQ_ENABLED', "1'b1" if interrupts else "1'b0"),
                       ('WAKE', '_csr_wakeup' if interrupts else "1'b0"),
                       ('PC_ASSERT', 'assert(resumePc == wfi_pc);' if interrupts else ''),
                       ('RESUME_ASSERT', 'assert(resumePc == $past(commit_output_bits_nextPc_layerCapture));' if interrupts else '')):
        backend = backend.replace(key, value)
    if not interrupts:
        backend = '\n'.join(line for line in backend.splitlines() if 'cover(' not in line) + '\n'
        backend += '  always @(posedge clock) if (!reset) cover(wfi_retired);\n'
    frontend = frontend_case(parameters)
    return [('WfiBackend', backend, 'assign status_sleep =', "assign status_sleep = 1'h0 &"),
            ('WfiFrontend', frontend, '~halt', "1'h1")]


def gpr_case(parameters):
    body = '''
  reg gpr_past = 0;
  (* anyconst *) reg [4:0] gpr_address;
  (* anyconst *) reg [5:0] gpr_bit;
  reg gpr_value;
  always @* assume(gpr_address != 0);
  always @(posedge clock) begin
    gpr_past <= 1;
    if (!gpr_past) assume(reset); else assume(!reset);
    if (reset) gpr_value <= 0;
    else begin
'''
    for lane in range(parameters['issueWidth']):
        body += f'      if (we_{lane} && waddr_{lane} == gpr_address) gpr_value <= wdata_{lane}[gpr_bit];\n'
        for operand in (1, 2):
            body += f'''      if (raddr{operand}_{lane} == 0) assert(rdata{operand}_{lane} == 0);
      if (raddr{operand}_{lane} == gpr_address) assert(rdata{operand}_{lane}[gpr_bit] == gpr_value);
'''
        body += f'      cover(we_{lane} && waddr_{lane} == gpr_address && gpr_value != wdata_{lane}[gpr_bit]);\n'
        if lane:
            body += f'      cover(we_0 && we_{lane} && waddr_0 == waddr_{lane} && waddr_0 != 0 && wdata_0 != wdata_{lane});\n'
    for register in range(1, 32):
        body += f'      if (gpr_address == {register}) assert(FORMAL_GPR_REGISTER_{register}[gpr_bit] == gpr_value);\n'
    return ('Gpr', body + '    end\n  end\n', '', '')


def frontend_case(parameters):
    width = parameters['issueWidth']
    words = 1 << (width - 1).bit_length() if parameters.get('iCacheBytes') else 1
    capacity = 2 * max(1, words - 1) if parameters.get('iCacheBytes') else width
    index_bits = (capacity + words).bit_length()
    fields = ('pc', 'tag', 'instruction', 'length', 'fault', 'cause', 'tval')
    packed = lambda prefix: '{' + ', '.join(prefix + field for field in fields) + '}'
    count = '_fetch_output_bits_count' if words > 1 else '1'
    reserved = 'reserved' if words > 1 else '1'
    expected = f"{words} - pc[{words.bit_length()}:2]" if words > 1 else '1'
    flush = 'redirect || invalidate' if parameters.get('iCacheBytes') else 'redirect'
    pending_pc = 'pendingPc' if parameters.get('iCacheBytes') else 'front_pc'
    body = f'''
  reg front_past = 0;
  (* anyconst *) reg [7:0] front_bit;
  always @* assume(front_bit < 236);
  reg [{index_bits-1}:0] front_owned = 0, front_reserved;
  reg [63:0] front_pc;
  wire formal_fetch_pending;
  wire [2:0] formal_fetch_count;
  wire [63:0] formal_fetch_pc;
  wire front_flush = {flush};
  wire front_accept = fetch_request_valid && _fetch_request_ready;
  wire front_return = _fetch_output_valid && !front_flush;
  wire front_deliver = output_valid && output_ready;
  wire [{index_bits-1}:0] front_take = front_deliver ? output_bits_count : 0;
  wire [{index_bits-1}:0] front_count = front_return ? {count} : 0;
  wire [{index_bits-1}:0] front_expected = {expected};
  wire [{index_bits-1}:0] front_buffered = front_owned - (formal_fetch_pending ? front_reserved : 0);
  reg front_reference [0:{capacity-1}];
  wire front_sequence [0:{capacity+words-1}];
  wire [235:0] front_input [0:{words-1}], front_buffer [0:{capacity-1}], front_output [0:{width-1}];
'''
    for lane in range(words):
        instruction = '_fetch_output_bits_instruction' if lane == 0 else f'_fetch_output_bits_following_{lane-1}'
        body += f"  assign front_input[{lane}] = {{_fetch_output_bits_pc + 64'd{4*lane}, _fetch_output_bits_tag + 8'd{lane}, {instruction}, 3'd4, " + (
            "_fetch_output_bits_fault, _fetch_output_bits_cause, _fetch_output_bits_tval};\n" if lane == 0 else "1'b0, 64'd0, 64'd0};\n")
    for lane in range(capacity):
        body += f'  assign front_buffer[{lane}] = {packed(f"buffer_{lane}_")};\n'
    for lane in range(width):
        body += f'  assign front_output[{lane}] = {packed(f"output_bits_packets_{lane}_")};\n'
    for slot in range(capacity + words):
        prior = f'front_reference[{slot}]' if slot < capacity else "1'b0"
        for lane in range(min(words, slot + 1)):
            prior = f'(front_buffered == {slot-lane} ? front_input[{lane}][front_bit] : {prior})'
        body += f'  assign front_sequence[{slot}] = {prior};\n'
    body += f'''
  always @(posedge clock) begin
    front_past <= 1;
    if (!front_past) assume(reset); else assume(!reset);
    if (reset || front_flush) front_owned <= 0;
    else begin
      front_owned <= front_owned + (front_accept ? front_expected : 0) -
        (front_return ? front_reserved - front_count : 0) - front_take;
      if (front_accept) begin front_reserved <= front_expected; front_pc <= pc; end
    end
    if (!reset) begin
      assert(front_owned <= {capacity} && front_owned == queued + (pending ? {reserved} : 0));
      assert(queued <= {capacity} && held <= {width} && held <= queued);
      assert(pending == formal_fetch_pending && front_buffered == queued);
      if (pending) assert({reserved} == front_reserved && {pending_pc} == front_pc && formal_fetch_count == front_reserved && formal_fetch_pc == front_pc);
      if (pending) assert(front_reserved == {expected.replace('pc[', 'front_pc[')});
      if (front_return) assert(pending && front_count >= 1 && front_count <= front_reserved);
      assert(front_buffered + front_count <= {capacity} && front_take <= front_buffered + front_count);
      if (front_flush || halt || faultPending) assert(!fetch_request_valid);
      assert(output_valid == (!front_flush && queued + front_count != 0));
      if (output_valid) assert(output_bits_count >= 1 && output_bits_count <= {width} && output_bits_count <= queued + front_count);
      if (front_past && $past(!reset)) begin
        if ($past(redirect)) assert(pc == $past(redirectPc));
        else if ($past(front_flush)) assert(pc == $past(queued ? buffer_0_pc : pending ? {pending_pc} : pc));
        else if ($past(front_accept)) assert(pc == $past(pc + 64'd4 * front_expected));
        else if ($past(front_return && front_count < front_reserved))
          assert(pc == $past(_fetch_output_bits_pc + 64'd4 * front_count));
        else assert($stable(pc));
        if ($past(output_valid && !output_ready) && !front_flush) begin
          assert(output_valid && $stable(output_bits_count));
        end
      end
      cover(front_owned == {capacity} && output_valid);
      cover(front_return && front_deliver);
      cover(front_buffered != 0 && {"front_return" if capacity > 1 else "front_accept"} && front_deliver);
      cover(halt && pending);
      cover(front_past && $past(halt) && !halt && front_accept);
'''
    if words > 1:
        body += f'      cover(front_return && front_count < front_reserved);\n      cover(output_valid && output_bits_count == {width});\n'
    if parameters.get('iCacheBytes'):
        body += '      cover(queued != 0 && invalidate && !redirect);\n      cover(queued == 0 && pending && invalidate && !redirect);\n'
    for slot in range(capacity):
        following = "1'b0"
        for take in range(min(width + 1, capacity + words - slot)):
            following = f'(front_take == {take} ? front_sequence[{slot+take}] : {following})'
        body += f'''
      if ({slot} < front_buffered) assert(front_buffer[{slot}][front_bit] == front_reference[{slot}]);
      if (!front_flush && {slot} < front_buffered + front_count - front_take)
        front_reference[{slot}] <= {following};
'''
    for lane in range(width):
        body += f'''
      if (output_valid && {lane} < output_bits_count) assert(front_output[{lane}][front_bit] == front_sequence[{lane}]);
      if (front_past && $past(!reset && output_valid && !output_ready && {lane} < output_bits_count) && !front_flush)
        assert($stable(front_output[{lane}][front_bit]));
'''
    return body + '    end\n  end\n'


def frontend_fetch_model(source, parameters):
    words = 1 << (parameters['issueWidth'] - 1).bit_length() if parameters.get('iCacheBytes') else 1
    count = 'output_bits_count' if words > 1 else '1'
    expected = f"{words} - request_bits_pc[{words.bit_length()}:2]" if words > 1 else '1'
    flush = 'cancel || invalidate' if parameters.get('iCacheBytes') else 'cancel'
    body, payload = '', []
    declaration = header(source)
    for direction, width, name in module_ports(source):
        if direction == 'output':
            if name.startswith(('request_', 'output_')):
                body += f'  (* anyseq *) reg {width} {name};\n'
                if name.startswith('output_bits_'):
                    payload.append(name)
            else:
                body += f'  assign {name} = 0;\n'
    return declaration.replace(');', ', output formal_pending, output [2:0] formal_count, output [63:0] formal_pc);') + body + f'''
  reg busy = 0, killed = 0, model_past = 0;
  reg [63:0] accepted_pc;
  reg [7:0] accepted_tag;
  reg [2:0] accepted_count;
  (* anyseq *) reg drained;
  wire model_flush = {flush};
  assign formal_pending = busy && !killed;
  assign formal_count = accepted_count;
  assign formal_pc = accepted_pc;
  always @* begin
    assume(!request_ready || (!model_flush && (!busy || (output_valid && output_ready && !output_bits_fault && {count} == accepted_count))));
    if (output_valid) begin
      assume(busy && !killed && !model_flush);
      assume(output_bits_pc == accepted_pc && output_bits_tag == accepted_tag && output_bits_length == 4);
      assume({count} >= 1 && {count} <= accepted_count && (!output_bits_fault || {count} == 1));
    end
  end
  always @(posedge clock) begin
    model_past <= 1;
    if (reset) begin busy <= 0; killed <= 0; end
    else begin
      if (model_flush) killed <= 1;
      if ((output_valid && output_ready) || (killed && drained)) busy <= 0;
      if (request_valid && request_ready) begin
        busy <= 1; killed <= 0; accepted_pc <= request_bits_pc;
        accepted_tag <= request_bits_tag; accepted_count <= {expected};
      end
      if (model_past && $past(!reset && output_valid && !output_ready) && !model_flush) begin
        assume(output_valid); assume($stable({{{', '.join(payload)}}}));
      end
    end
  end
endmodule
'''


def wfi_witness(parameters, mode):
    body = r'''
  (* anyconst *) reg [1:0] wfi_scenario;
  reg [6:0] age = 0;
  always @(posedge clock) if (reset) age <= 0; else if (age != 127) age <= age + 1;
  always @* assume(wfi_scenario < 3);
'''
    values = dict(instruction_valid='age == 0 || age == 8 || age >= 16',
                  instruction_bits_count=1, instruction_bits_packets_0_length=4,
                  instruction_bits_packets_0_pc=f"64'h{int(parameters['resetVector']):x}",
                  instruction_bits_packets_0_cause=1,
                  instruction_bits_packets_0_fault='wfi_scenario == 2 && age == 16',
                  instruction_bits_packets_0_instruction="age == 0 ? 32'h00800093 : age == 8 ? 32'h30409073 : age == 16 ? 32'h10500073 : age == 17 ? 32'h02108133 : 32'h13",
                  data_request_ready=1, data_response_bits_last=1,
                  interrupts_software='wfi_scenario == 1 ? age >= 17 : age >= 24')
    scenario = {'mutation': 0, 'mutation-priority': 1, 'mutation-fault': 2}.get(mode)
    if scenario is not None:
        body += f'  always @* assume(wfi_scenario == {scenario});\n'
    return body, values


def word_cases(parameters):
    decode = r'''
  wire [31:0] word = input_bits_instruction;
  wire load = word[6:0] == 7'h03 && (word[14:12] == 2 || word[14:12] == 3 || word[14:12] == 6);
  wire store = word[6:0] == 7'h23 && (word[14:12] == 2 || word[14:12] == 3);
  always @* begin
    assert(input_ready == output_ready && output_valid == input_valid);
    if (load || store) begin
      assert(output_bits_operation == (store ? (word[12] ? 9 : 20) :
        word[14:12] == 2 ? 18 : word[14:12] == 6 ? 19 : 8));
      assert(output_bits_usesRs1 == !input_bits_fault);
      assert(output_bits_usesRs2 == (store && !input_bits_fault));
      assert(output_bits_writesRd == (load && !input_bits_fault));
      assert(!output_bits_serializing);
      assert(output_bits_immediate == (store ? {{52{word[31]}}, word[31:25], word[11:7]} :
        {{52{word[31]}}, word[31:20]}));
    end
    cover(input_valid && load && word[14:12] == 2 && !input_bits_fault);
    cover(input_valid && load && word[14:12] == 6 && !input_bits_fault);
    cover(input_valid && store && word[14:12] == 2 && !input_bits_fault);
  end
'''
    execute = r'''
  wire [4:0] op = input_bits_decoded_operation;
  wire load = op == 8 || op == 15 || op == 18 || op == 19;
  wire store = op == 9 || op == 15 || op == 20;
  always @* begin
    assert(input_ready == output_ready && output_valid == input_valid);
    if (op <= 20) begin
      assert(output_bits_load == load && output_bits_store == store);
      assert(output_bits_memorySize == (op == 18 || op == 19 || op == 20 ? 2 : 3));
      assert(output_bits_unsignedLoad == (op == 19));
    end
    if (load || store) begin
      assert(output_bits_address == input_bits_operand1 + input_bits_decoded_immediate);
      assert(output_bits_storeData == input_bits_operand2);
      assert(output_bits_nextPc == input_bits_decoded_instruction_pc + input_bits_decoded_instruction_length);
      assert(output_bits_instruction_fault == input_bits_decoded_instruction_fault);
      assert(!output_bits_csrWrite && !output_bits_mret && !output_bits_fenceI);
    end
    cover(input_valid && op == 18);
    cover(input_valid && op == 19);
    cover(input_valid && op == 20);
    cover(input_valid && op == 15);
  end
'''
    lsu = r'''
  reg word_past = 0, word_owned, word_sent, word_replied, word_done, word_fault;
  reg word_load, word_store, word_unsigned, word_atomic, word_pair, word_reservation;
  reg [4:0] word_operation;
  reg [63:0] word_reserved_address;
  reg [2:0] word_size;
  reg [63:0] word_address, word_data, word_value, word_cause, word_tval, word_pc;
  reg [7:0] word_tag;
  wire word_aligned = (input_bits_address & ((64'd1 << input_bits_memorySize) - 1)) == 0;
  wire word_permitted = PERMITTED;
  wire word_valid_size = word_size <= 3;
  reg [63:0] word_extended;
  always @* case (word_size)
    0: word_extended = {{56{!word_unsigned && memory_response_bits_data[7]}}, memory_response_bits_data[7:0]};
    1: word_extended = {{48{!word_unsigned && memory_response_bits_data[15]}}, memory_response_bits_data[15:0]};
    2: word_extended = {{32{!word_unsigned && memory_response_bits_data[31]}}, memory_response_bits_data[31:0]};
    default: word_extended = memory_response_bits_data;
  endcase
  always @(posedge clock) begin
    word_past <= 1;
    if (!word_past) assume(reset); else assume(!reset);
    if (reset) begin word_owned <= 0; word_sent <= 0; word_replied <= 0; word_done <= 0; word_reservation <= 0; end
    else begin
      assert(word_owned == (state != 0));
      assert(word_reservation == reserved);
      if (word_reservation) assert(word_reserved_address == {PAD_RESERVED, reservedWord, 3'd0});
      if (word_owned) begin
        assert(packet_address == word_address && packet_atomic == word_atomic && packet_instruction_instruction[31:27] == word_operation);
        assert(packet_memorySize == word_size && packet_instruction_tag == word_tag);
        assert(scEligible == word_pair);
      end
      assert(memory_response_ready == (word_sent && !word_replied));
      if (input_valid && input_ready) begin
        assert(!word_owned);
        word_owned <= 1; word_sent <= 0; word_replied <= 0;
        word_done <= input_bits_instruction_fault || !word_aligned || !word_permitted;
        word_size <= input_bits_memorySize; word_unsigned <= input_bits_unsignedLoad;
        word_load <= input_bits_load; word_store <= input_bits_store;
        word_atomic <= input_bits_atomic; word_operation <= input_bits_instruction_instruction[31:27];
        word_pair <= input_bits_atomic && input_bits_instruction_instruction[31:27] == 3 && word_reservation &&
          input_bits_address == word_reserved_address && input_bits_memorySize == 3;
        if (input_bits_atomic) word_reservation <= 0;
        word_address <= input_bits_address; word_data <= input_bits_storeData;
        word_value <= input_bits_value; word_tag <= input_bits_instruction_tag;
        word_pc <= input_bits_instruction_pc;
        word_fault <= input_bits_instruction_fault || !word_aligned || !word_permitted;
        word_cause <= input_bits_instruction_fault ? input_bits_instruction_cause :
          !word_aligned ? (input_bits_store ? 6 : 4) : input_bits_store ? 7 : 5;
        word_tval <= input_bits_instruction_fault ? input_bits_instruction_tval : input_bits_address;
      end
      if (memory_request_valid) begin
        assert(word_owned && !word_sent && !word_replied);
        assert(memory_request_bits_address == word_address && memory_request_bits_data == word_data);
        assert(memory_request_bits_size == word_size && memory_request_bits_tag == word_tag);
        if (word_valid_size) assert(memory_request_bits_mask == (word_store ? (9'd1 << (1 << word_size)) - 1 : 0));
        assert(memory_request_bits_write == word_store && !memory_request_bits_fetch);
        assert(memory_request_bits_atomic == word_atomic && memory_request_bits_atomicOperation == (word_atomic ? word_operation : 0));
        assert(memory_request_bits_scEligible == word_pair);
        if (word_valid_size) assert(!word_fault);
      end
      if (memory_request_valid && memory_request_ready) word_sent <= 1;
      if (memory_response_valid && memory_response_ready) begin
        assert(word_owned && word_sent && !word_replied);
        word_replied <= 1; word_done <= 1;
        if (word_load || word_atomic) word_value <= word_extended;
        if (word_atomic && word_operation == 2 && word_size == 3 && !memory_response_bits_fault && memory_response_bits_tag == word_tag) begin
          word_reservation <= 1; word_reserved_address <= word_address & MASK_RESERVED;
        end
        if (memory_response_bits_fault || memory_response_bits_tag != word_tag) begin
          word_fault <= 1; word_cause <= word_store ? 7 : 5; word_tval <= word_address;
        end
      end
      if (word_owned && word_valid_size) assert(output_valid == word_done);
      if (output_valid) begin
        assert(word_owned && (!word_sent || word_replied));
        assert(output_bits_memorySize == word_size && output_bits_unsignedLoad == word_unsigned);
        assert(output_bits_instruction_pc == word_pc && output_bits_instruction_tag == word_tag);
        assert(output_bits_address == word_address && output_bits_storeData == word_data);
        assert(output_bits_load == word_load && output_bits_store == word_store && output_bits_atomic == word_atomic);
        if (word_valid_size) begin
          assert(output_bits_instruction_fault == word_fault && output_bits_value == word_value);
          if (word_fault) assert(output_bits_instruction_cause == word_cause && output_bits_instruction_tval == word_tval);
        end
        if (output_ready) word_owned <= 0;
      end
      if (word_past && $past(!reset && memory_request_valid && !memory_request_ready)) begin
        assert(memory_request_valid);
        assert($stable({memory_request_bits_address, memory_request_bits_data, memory_request_bits_size,
          memory_request_bits_mask, memory_request_bits_tag, memory_request_bits_write, memory_request_bits_atomic,
          memory_request_bits_atomicOperation, memory_request_bits_scEligible}));
      end
      if (word_past && $past(!reset && output_valid && !output_ready)) begin
        assert(output_valid);
        assert($stable({output_bits_value, output_bits_instruction_fault, output_bits_instruction_cause,
          output_bits_instruction_tval, output_bits_memorySize, output_bits_unsignedLoad}));
      end
      cover(output_valid && word_size == 2 && word_load && !word_store && !word_unsigned && word_value[63] && !word_fault);
      cover(output_valid && word_size == 2 && word_load && word_unsigned && word_value[31] && !word_fault);
      cover(memory_request_valid && word_size == 2 && word_store && word_address[2] && !memory_request_ready);
      cover(output_valid && word_size == 2 && word_fault && !word_sent);
      cover(output_valid && word_fault && !word_sent && !output_ready);
      cover(output_valid && word_size == 3 && word_load && word_store && word_atomic && word_operation == 0 && !word_fault);
      cover(output_valid && word_size == 0 && word_load && !word_store && word_value[63] && !word_fault);
      cover(output_valid && word_size == 1 && word_load && !word_store && word_unsigned && word_value[15] && !word_fault);
      cover(memory_request_valid && word_size == 0 && word_store && word_address[2:0] == 7);
      cover(memory_request_valid && word_atomic && word_operation == 3 && word_pair);
      cover(memory_request_valid && word_atomic && word_operation == 3 && !word_pair);
      cover(output_valid && word_atomic && word_operation == 2 && !word_fault && word_reservation);
      cover(output_valid && word_atomic && word_operation == 3 && word_fault && !word_sent);
    end
  end
'''.replace('PERMITTED', '_pmp_allowed' if parameters['pmpEntries'] else "1'b1").replace(
        'PAD_RESERVED', f"{64 - parameters['physicalAddressBits']}'d0").replace(
        'MASK_RESERVED', f"64'h{((1 << parameters['physicalAddressBits']) - 1) & ~7:x}")
    return [('WordDecode', decode, 'assign output_bits_usesRs2 =', "assign output_bits_usesRs2 = 1'h0 &"),
            ('WordExecute', execute, 'assign output_bits_unsignedLoad =', "assign output_bits_unsignedLoad = 1'h0 &"),
            ('Lsu', lsu, 'assign memory_request_bits_size =', "assign memory_request_bits_size = 3'h3 |")]


def integer_cases(parameters):
    decode = r'''
  wire [31:0] i_word = input_bits_instruction;
  wire [6:0] i_opcode = i_word[6:0], i_funct7 = i_word[31:25];
  wire [2:0] i_funct3 = i_word[14:12];
  reg [4:0] i_operation;
  reg i_checked, i_registers, i_store, i_branch, i_csr;
  reg [63:0] i_immediate;
  always @* begin
    i_operation = 0; i_checked = 1; i_registers = 0; i_store = 0; i_branch = 0; i_csr = 0;
    i_immediate = {{52{i_word[31]}}, i_word[31:20]};
    case (i_opcode)
      7'h13: begin
        if (i_funct3 == 0) i_operation = 3;
        else if ((i_funct3 == 1 && i_word[31:26] == 0) ||
          (i_funct3 == 5 && (i_word[31:26] == 0 || i_word[31:26] == 16)) ||
          (i_funct3 != 1 && i_funct3 != 5)) i_operation = 21;
      end
      7'h33: begin
        i_registers = 1;
        if (i_funct7 == 0) i_operation = i_funct3 == 0 ? 4 : 22;
        else if (i_funct7 == 32 && (i_funct3 == 0 || i_funct3 == 5)) i_operation = 22;
        else if (i_funct7 == 1 && i_funct3 == 0) i_operation = 14;
      end
      7'h1b: if (i_funct3 == 0 || (i_funct3 == 1 && i_funct7 == 0) ||
        (i_funct3 == 5 && (i_funct7 == 0 || i_funct7 == 32))) i_operation = 23;
      7'h3b: begin
        i_registers = 1;
        if (((i_funct3 == 0 || i_funct3 == 5) && (i_funct7 == 0 || i_funct7 == 32)) ||
          (i_funct3 == 1 && i_funct7 == 0)) i_operation = 24;
      end
      7'h63: begin
        i_registers = 1; i_branch = 1;
        i_immediate = {{51{i_word[31]}}, i_word[31], i_word[7], i_word[30:25], i_word[11:8], 1'b0};
        if (i_funct3 == 0) i_operation = 5;
        else if (i_funct3 == 1 || i_funct3 >= 4) i_operation = 25;
      end
      7'h03: if (i_funct3 < 7) i_operation = i_funct3 == 2 ? 18 : i_funct3 == 3 ? 8 : i_funct3 == 6 ? 19 : 26;
      7'h23: begin
        i_registers = 1; i_store = 1;
        i_immediate = {{52{i_word[31]}}, i_word[31:25], i_word[11:7]};
        if (i_funct3 < 4) i_operation = i_funct3 == 2 ? 20 : i_funct3 == 3 ? 9 : 27;
      end
      7'h2f: begin
        i_registers = i_word[31:27] != 2; i_immediate = 0;
        if (i_funct3 == 3) begin
          if (i_word[31:27] == 0) i_operation = 15;
          else if (i_word[31:27] == 1 || i_word[31:27] == 3 || i_word[31:27] == 8 ||
            (i_word[31:27] == 2 && i_word[24:20] == 0)) i_operation = 30;
        end
      end
      7'h73: begin
        i_csr = 1;
        if (i_funct3 == 1) i_operation = 10;
        else if (i_funct3 == 2) i_operation = 11;
        else if (i_funct3 == 3 || i_funct3 >= 5) i_operation = 28;
        else i_checked = i_funct3 != 0;
      end
      default: i_checked = 0;
    endcase
    if (i_opcode == 7'h73 && i_funct3 == 0 && i_word != 32'h00000073 && i_word != 32'h30200073) begin
      assert(output_bits_operation == (i_word == 32'h10500073 ? 29 : 0));
      assert(!output_bits_usesRs1 && !output_bits_usesRs2 && !output_bits_writesRd);
      assert(output_bits_serializing == (!input_bits_fault && i_word == 32'h10500073));
    end
    if (i_checked) begin
      assert(output_bits_operation == i_operation);
      assert(output_bits_rs1 == i_word[19:15] && output_bits_rs2 == i_word[24:20] && output_bits_rd == i_word[11:7]);
      assert(output_bits_usesRs1 == (!input_bits_fault && i_operation != 0 && !(i_csr && i_funct3[2])));
      assert(output_bits_usesRs2 == (!input_bits_fault && i_operation != 0 && i_registers));
      assert(output_bits_writesRd == (!input_bits_fault && i_operation != 0 && !i_store && !i_branch));
      assert(output_bits_serializing == (!input_bits_fault && i_operation != 0 && i_csr));
      if (i_operation != 0 && ((!i_csr && !i_registers) || i_store || i_branch || i_opcode == 7'h2f)) assert(output_bits_immediate == i_immediate);
    end
    cover(input_valid && !input_bits_fault && i_checked && i_operation == 0 && i_funct7 == 1);
    cover(input_valid && i_operation == 21 && i_word[25] && i_funct3 == 5);
    cover(input_valid && i_operation == 23 && i_funct3 == 5);
    cover(input_valid && i_operation == 28 && i_word[19:15] == 0);
    cover(input_valid && i_operation == 30 && i_word[31:27] == 2 && i_word[26:25] == 3);
    cover(input_valid && i_opcode == 7'h2f && i_funct3 == 2 && i_operation == 0);
  end
'''
    if parameters.get('enableSupervisorMode'):
        decode = decode.replace("i_word == 32'h10500073 ? 29 : 0", "i_word == 32'h10500073 ? 29 : i_word == 32'h10200073 ? 31 : 0")
        decode = decode.replace("!input_bits_fault && i_word == 32'h10500073", "!input_bits_fault && (i_word == 32'h10500073 || i_word == 32'h10200073)")
    if parameters.get('virtualAddressBits') == 39:
        decode = decode.replace("i_word == 32'h10200073 ? 31 : 0", "i_word == 32'h10200073 ? 31 : (i_word & 32'hfe007fff) == 32'h12000073 ? 16 : 0")
        decode = decode.replace("i_word == 32'h10200073)", "i_word == 32'h10200073 || (i_word & 32'hfe007fff) == 32'h12000073)")
    execute = r'''
  wire [4:0] i_op = input_bits_decoded_operation;
  wire [31:0] i_word = input_bits_decoded_instruction_instruction;
  wire [2:0] i_function = i_word[14:12];
  wire [63:0] i_a = input_bits_operand1, i_b = input_bits_operand2, i_imm = input_bits_decoded_immediate;
  wire i_small = i_op == 23 || i_op == 24;
  wire i_immediate = i_op == 21 || i_op == 23;
  wire [63:0] i_rhs = i_immediate ? i_imm : i_b;
  wire [5:0] i_shift = i_small ? {1'b0, i_rhs[4:0]} : i_rhs[5:0];
  wire signed [63:0] i_signed_a = i_small ? {{32{i_a[31]}}, i_a[31:0]} : i_a;
  wire [63:0] i_arithmetic_shift = i_signed_a >>> i_shift;
  reg [63:0] i_result, i_expected, i_csr_value;
  reg i_taken, i_write;
  wire [63:0] i_target = input_bits_decoded_instruction_pc + i_imm;
  wire [63:0] i_sequential = input_bits_decoded_instruction_pc + input_bits_decoded_instruction_length;
  wire [63:0] i_csr_source = i_function[2] ? {59'd0, i_word[19:15]} : i_a;
  always @* begin
    case (i_function)
      0: i_result = !i_immediate && i_word[30] ? i_a - i_rhs : i_a + i_rhs;
      1: i_result = i_a << i_shift;
      2: i_result = {63'd0, $signed(i_a) < $signed(i_rhs)};
      3: i_result = {63'd0, i_a < i_rhs};
      4: i_result = i_a ^ i_rhs;
      5: i_result = i_word[30] ? i_arithmetic_shift :
        (i_small ? {32'd0, i_a[31:0]} : i_a) >> i_shift;
      6: i_result = i_a | i_rhs;
      7: i_result = i_a & i_rhs;
    endcase
    i_expected = i_small ? {{32{i_result[31]}}, i_result[31:0]} : i_result;
    assert(output_bits_wfi == (i_op == 29));
    assert(output_bits_atomic == (i_op == 15 || i_op == 30));
    if (i_op == 30) begin
      assert(output_bits_load == (i_word[31:27] != 3) && output_bits_store == (i_word[31:27] != 2));
      assert(output_bits_memorySize == 3 && !output_bits_unsignedLoad);
      assert(output_bits_address == i_a + i_imm && output_bits_storeData == i_b && output_bits_nextPc == i_sequential);
      assert(output_bits_instruction_fault == input_bits_decoded_instruction_fault);
      assert(!output_bits_csrWrite && !output_bits_mret && !output_bits_fenceI && !output_bits_wfi);
    end
    if (i_op == 29) begin
      assert(output_bits_nextPc == i_sequential && output_bits_instruction_fault == input_bits_decoded_instruction_fault);
      assert(!output_bits_load && !output_bits_store && !output_bits_csrWrite && !output_bits_mret);
    end
    case (i_function)
      0: i_taken = i_a == i_b;
      1: i_taken = i_a != i_b;
      4: i_taken = $signed(i_a) < $signed(i_b);
      5: i_taken = $signed(i_a) >= $signed(i_b);
      6: i_taken = i_a < i_b;
      7: i_taken = i_a >= i_b;
      default: i_taken = 0;
    endcase
    i_write = i_function[1:0] == 1 || input_bits_decoded_rs1 != 0;
    case (i_function[1:0])
      1: i_csr_value = i_csr_source;
      2: i_csr_value = csrValue | i_csr_source;
      default: i_csr_value = csrValue & ~i_csr_source;
    endcase
    if (i_op >= 21 && i_op <= 24 && (!i_small || i_function == 0 || i_function == 1 || i_function == 5)) begin
      assert(output_bits_value == i_expected && output_bits_nextPc == i_sequential);
      assert(output_bits_instruction_fault == input_bits_decoded_instruction_fault);
      assert(!output_bits_load && !output_bits_store && !output_bits_csrWrite);
    end
    if (i_op == 25 && (i_function == 1 || i_function >= 4)) begin
      assert(output_bits_nextPc == (i_taken ? i_target : i_sequential));
      assert(output_bits_instruction_fault == (input_bits_decoded_instruction_fault || (i_taken && i_target[1:0] != 0)));
      if (!input_bits_decoded_instruction_fault && i_taken && i_target[1:0] != 0)
        assert(output_bits_instruction_cause == 0 && output_bits_instruction_tval == i_target);
      assert(!output_bits_load && !output_bits_store && !output_bits_csrWrite);
    end
    if (i_op == 26 || i_op == 27) begin
      assert(output_bits_load == (i_op == 26) && output_bits_store == (i_op == 27));
      assert(output_bits_address == i_a + i_imm && output_bits_storeData == i_b);
      assert(output_bits_memorySize == {1'b0, i_function[1:0]});
      assert(output_bits_unsignedLoad == (i_op == 26 && i_function[2]));
    end
    if ((i_op == 28 || i_op == 10 || i_op == 11) && i_function != 0 && i_function != 4 &&
        input_bits_decoded_rs1 == i_word[19:15] &&
        (i_op == 28 ? (i_function == 3 || i_function >= 5) : i_function == (i_op == 10 ? 1 : 2))) begin
      assert(output_bits_value == csrValue && output_bits_csrData == i_csr_value && output_bits_csrWrite == i_write);
      assert(csrAddress == i_word[31:20] && output_bits_csrAddress == i_word[31:20]);
      assert(output_bits_instruction_fault == (input_bits_decoded_instruction_fault || !csrLegal || (i_write && i_word[31:30] == 3)));
      if (!input_bits_decoded_instruction_fault && (!csrLegal || (i_write && i_word[31:30] == 3)))
        assert(output_bits_instruction_cause == 2 && output_bits_instruction_tval == {32'd0, i_word});
    end
    cover(input_valid && i_op == 21 && i_function == 1 && i_rhs[5]);
    cover(input_valid && i_op == 24 && i_function == 5 && i_a[63] != i_a[31] && i_word[30]);
    cover(input_valid && i_op == 25 && i_taken && i_target[1:0] != 0);
    cover(input_valid && !input_bits_decoded_instruction_fault && i_op == 28 && i_function == 7 &&
      !i_write && csrLegal && input_bits_decoded_rs1 == i_word[19:15]);
  end
'''
    if parameters.get('enableUserMode'):
        execute = execute.replace('i_sequential && output_bits_instruction_fault == input_bits_decoded_instruction_fault',
                                  'i_sequential && output_bits_instruction_fault == (input_bits_decoded_instruction_fault || !wfiLegal)')
    return [('IntegerDecode', decode, 'assign output_bits_usesRs1 =', "assign output_bits_usesRs1 = 1'h0 &"),
            ('IntegerExecute', execute, 'assign output_bits_csrData =', "assign output_bits_csrData = 64'h0 &")]


def local_interrupt_case(parameters):
    base = int(parameters['localInterruptBase'])
    count = parameters['hartCount']
    body = r'''
  reg local_past = 0, local_pending, local_fault;
  reg [63:0] local_time, local_data;
  reg [7:0] local_tag;
  reg local_legal;
  reg [63:0] local_read;
  wire local_accept = memory_request_valid && memory_request_ready;
  wire local_access = !memory_request_bits_fetch && !memory_request_bits_atomic;
  wire local_word = memory_request_bits_size == 2 && (!memory_request_bits_write || memory_request_bits_mask == 15);
  wire local_double = memory_request_bits_size == 3 && (!memory_request_bits_write || memory_request_bits_mask == 255);
'''
    for hart in range(count):
        body += f'  reg local_software_{hart};\n  reg [63:0] local_compare_{hart};\n'
    body += '  always @* begin\n    local_legal = 0; local_read = 0;\n'
    for hart in range(count):
        for offset, width, value in ((4 * hart, 'local_word', f"{{63'd0, local_software_{hart}}}"),
                                     (0x4000 + 8 * hart, 'local_double', f'local_compare_{hart}')):
            body += f"    if (memory_request_bits_address == 64'h{base + offset:x} && {width}) begin local_legal = local_access; local_read = {value}; end\n"
    body += f"    if (memory_request_bits_address == 64'h{base + 0xbff8:x} && local_double) begin local_legal = local_access; local_read = local_time; end\n"
    body += r'''  end
  always @(posedge clock) begin
    local_past <= 1;
    if (!local_past) assume(reset); else assume(!reset);
    if (reset) begin
      local_pending <= 0; local_time <= 0;
'''
    for hart in range(count):
        body += f"      local_software_{hart} <= 0; local_compare_{hart} <= 64'hffffffffffffffff;\n"
    body += r'''    end else begin
      assert(local_time == time_0);
      assert(memory_request_ready == !local_pending && memory_response_valid == local_pending);
      if (local_pending) begin
        assert(memory_response_bits_tag == local_tag && memory_response_bits_fault == local_fault);
        assert(memory_response_bits_data == local_data);
        if (memory_response_ready) local_pending <= 0;
      end
      if (timeTick) local_time <= local_time + 1;
      if (local_accept) begin
        assert(!local_pending);
        local_pending <= 1; local_tag <= memory_request_bits_tag; local_fault <= !local_legal;
        local_data <= local_legal && !memory_request_bits_write ? local_read : 0;
        if (local_legal && memory_request_bits_write) begin
'''
    for hart in range(count):
        body += f"          if (memory_request_bits_address == 64'h{base + 4 * hart:x}) local_software_{hart} <= memory_request_bits_data[0];\n"
        body += f"          if (memory_request_bits_address == 64'h{base + 0x4000 + 8 * hart:x}) local_compare_{hart} <= memory_request_bits_data;\n"
    body += f"          if (memory_request_bits_address == 64'h{base + 0xbff8:x}) local_time <= memory_request_bits_data;\n"
    body += '        end\n      end\n'
    for hart in range(count):
        compare = 'compare' if hart == 0 else f'compare_{hart - 1}'
        body += f'''      assert(local_compare_{hart} == {compare});
      assert(interrupts_{hart}_software == local_software_{hart});
      assert(interrupts_{hart}_timer == (local_time >= local_compare_{hart}));
      assert(!interrupts_{hart}_external);
      cover(interrupts_{hart}_software && interrupts_{hart}_timer);
'''
    body += r'''      if (local_past && $past(!reset && memory_response_valid && !memory_response_ready)) begin
        assert(memory_response_valid);
        assert($stable({memory_response_bits_tag, memory_response_bits_fault, memory_response_bits_data}));
      end
      cover(local_pending && local_fault && !memory_response_ready);
      cover(local_pending && !local_fault && !memory_response_ready && timeTick);
      cover(local_accept && local_legal && memory_request_bits_write && timeTick);
      cover(local_accept && memory_request_bits_fetch);
      cover(local_accept && memory_request_bits_atomic);
    end
  end
'''
    return ('LocalInterrupts', body, 'assign memory_response_bits_fault =',
            "assign memory_response_bits_fault = 1'h0 &")


def instance_ports(source, pattern=r'instructions_\d+x32'):
    arrays = re.findall(pattern + r'\s+\w+\s*\((.*?)\n  \);', source, re.S)
    return [(array, dict(re.findall(r'\.(\w+)\s*\((.*?)\)(?=\s*,|\s*$)', array, re.S))) for array in arrays]


def wide_fetch_case(parameters):
    banks = 1 << (parameters['issueWidth'] - 1).bit_length()
    bits = banks.bit_length()-1
    translated = parameters.get('virtualAddressBits') == 39
    enabled = parameters['pmpEntries'] != 0
    permission = '_pmp_allowed' if enabled else "1'b1"
    def ordinary(address, size):
        return ' || '.join(f"(({address}) >= 64'h{int(r['base']):x} && ({address}) <= 64'h{int(r['base'])+int(r['size'])-size:x})"
                          for r in parameters['memoryRegions'] if r['executable'] and not r['device'] and int(r['size']) >= size) or "1'b0"
    body = re.sub(r'\bcancel\b', '(cancel || invalidate)', FETCH)
    body = re.sub(r'\bkilled\b', 'observed_killed', body)
    body = body.replace('reg outstanding;', 'reg outstanding; reg local_denied, translation_failed;')
    body = body.replace('PRIVILEGED', "privilege != 0" if parameters.get('enableUserMode') else "1'b1")
    body = body.replace('memory_request_bits_privileged == accepted_privileged',
                        "memory_request_bits_privileged == (accepting ? (privilege != 0) : accepted_privileged)" if parameters.get('enableUserMode') else 'memory_request_bits_privileged')
    body = body.replace('assert(response_seen || accepted_pc[1:0] != 0);',
                        'assert(memory_response_valid || response_seen || accepted_pc[1:0] != 0 || local_denied || translation_failed);')
    body = body.replace('output_bits_fault && response_seen', 'output_bits_fault && (response_seen || memory_response_valid)')
    body = body.replace('assume(!memory_response_valid || outstanding);', 'assert(!memory_response_valid || outstanding);')
    body = body.replace('assume(memory_response_valid);', 'assert(memory_response_valid);').replace('assume($stable({memory_response_', 'assert($stable({memory_response_')
    body = re.sub(r'      cover\(past_valid && \$past\(!reset && memory_request_valid && !memory_request_ready\)\n\s+&&[^;]+;', '', body)
    body = re.sub(r'      cover\(observed_killed && outstanding && memory_response_valid && memory_response_ready && memory_response_bits_fault\);', '', body)
    held = 'wide_physical' if translated else 'accepted_pc'
    candidate = 'translation_response_bits_address' if translated else 'request_bits_pc'
    aligned = f'{{{candidate}[63:{bits+2}], {bits+2}\'b0}}'
    full = f"({permission} && ({ordinary(aligned, 4*banks)}))"
    scalar = f"({permission} && ({ordinary(held, 4)}))"
    start = 'translation_response_valid && translation_response_ready' if translated else 'request_valid && request_ready'
    body += f'''
  reg wide_granted, wide_scalar;
  reg [63:0] wide_physical;
  reg [1:0] wide_privilege;
  wire formal_fetch_cache_owned, formal_fetch_cache_cancelled, formal_fetch_physical_owned, formal_fetch_physical_line;
  wire [63:0] formal_fetch_cache_address;
  wire [2:0] formal_fetch_cache_count;
  always @(posedge clock) if (reset) begin wide_granted <= 0; wide_scalar <= 0; local_denied <= 0; translation_failed <= 0; end
  else begin
    assert(outstanding == (state == 2));
    assert(outstanding == formal_fetch_cache_owned);
    assert(fetch_physical_owned == formal_fetch_physical_owned);
    if (fetch_physical_owned) assert(fetch_physical_line == formal_fetch_physical_line);
    if (formal_fetch_cache_owned) begin
      assert(formal_fetch_cache_address == {held});
      assert(formal_fetch_cache_count >= 1 && formal_fetch_cache_count <= {banks} - formal_fetch_cache_address[{bits+1}:2]);
      assert(memory_response_bits_count >= 1 && memory_response_bits_count <= {banks} - formal_fetch_cache_address[{bits+1}:2]);
    end
    if (formal_fetch_cache_owned && formal_fetch_cache_cancelled) assert(observed_killed);
    if (state == 0) assert(!have_request || observed_killed);
    if (state != 0) assert(have_request && packet_pc == accepted_pc && packet_tag == accepted_tag);
    if (state != 0) assert(killed == observed_killed && accepted_privileged == {'(wide_privilege != 0)' if parameters.get('enableUserMode') else '1'});
    if (state != 0) assert({'privilege_0' if parameters.get('enableUserMode') else '3'} == wide_privilege);
    if (state == 1 || state == 2) assert(wide_granted && wholeBlock == !wide_scalar);
    if (state != 0 && local_denied) assert(state == 3 && packet_fault && packet_cause == 1 && packet_tval == accepted_pc);
    if (request_valid && request_ready) begin wide_privilege <= {'privilege' if parameters.get('enableUserMode') else '3'}; wide_granted <= 0; wide_scalar <= 0; local_denied <= 0; translation_failed <= 0; end
    if ({start}) begin
      wide_granted <= {full}{' && !translation_response_bits_fault' if translated else ''};
      wide_scalar <= 0; wide_physical <= {candidate};
      {'translation_failed <= translation_response_bits_fault;' if translated else ''}
    end
    if (state == 6) begin
      wide_granted <= {scalar}; wide_scalar <= 1;
      if (!{scalar}) local_denied <= 1;
    end
    if (memory_request_valid) begin
      if (accepting) begin
        assert({int(not translated)} && request_valid && {full});
        assert(memory_request_bits_address == request_bits_pc && memory_request_bits_tag == request_bits_tag && memory_request_bits_size == {bits+2});
      end else begin
        assert(wide_granted && memory_request_bits_address == {held} && memory_request_bits_tag == accepted_tag);
        assert(memory_request_bits_size == (wide_scalar ? 2 : {bits+2}));
      end
    end
    if (output_valid) begin
      assert(output_bits_count >= 1 && output_bits_count <= {banks} - accepted_pc[{bits+1}:2]);
      if (output_bits_fault) assert(output_bits_count == 1);
      if (local_denied) assert(output_bits_fault && output_bits_cause == 1 && output_bits_tval == accepted_pc);
      if (output_bits_count < {banks} - output_bits_pc[{bits+1}:2]) assert(!request_ready && !memory_request_valid);
    end
    if ($past(!reset && output_valid && !output_ready) && !cancel && !invalidate) begin
      assert(output_valid);
      assert($stable({{output_bits_pc, output_bits_instruction, output_bits_tag, output_bits_fault,
        output_bits_cause, output_bits_tval, output_bits_count, {', '.join(f'output_bits_following_{i}' for i in range(banks-1))}}}));
    end
    cover(state == 6 && {scalar}); cover(state == 6 && !{scalar});
    cover(state == 6 && (cancel || invalidate));
    cover(output_valid && output_bits_count == {banks});
    cover(output_valid && !output_bits_fault && output_bits_count == 1);
  end
'''
    if enabled:
        body += f'''  wire [63:0] formal_fetch_pmp_address = FORMAL_FETCH_PMP_address;
  wire [2:0] formal_fetch_pmp_size = FORMAL_FETCH_PMP_size;
  wire [1:0] formal_fetch_pmp_privilege = FORMAL_FETCH_PMP_privilege;
  always @* if (!reset) begin
    if ({start}) begin
      assert(formal_fetch_pmp_address == {aligned} && formal_fetch_pmp_size == {bits+2});
      assert(formal_fetch_pmp_privilege == {'wide_privilege' if translated else 'privilege'});
    end
    if (state == 6) assert(formal_fetch_pmp_address == {held} && formal_fetch_pmp_size == 2 && formal_fetch_pmp_privilege == wide_privilege);
  end
'''
    if translated:
        body += '''  reg translation_owned;
  always @(posedge clock) if (reset) translation_owned <= 0;
  else begin
    assert(translation_owned == (state == 5));
    if (state == 4 || state == 5) assert(wholeBlock && !wide_scalar);
    if (state == 1 || state == 2 || state == 6) assert(physicalAddress == wide_physical && wide_physical[11:0] == accepted_pc[11:0]);
    if (translation_response_valid && !translation_response_bits_fault) assume(translation_response_bits_address[11:0] == accepted_pc[11:0]);
    assume(!translation_response_valid || translation_owned);
    if ($past(!reset && translation_response_valid && !translation_response_ready)) begin
      assume(translation_response_valid); assume($stable({translation_response_bits_address, translation_response_bits_fault, translation_response_bits_cause}));
    end
    if (translation_request_valid && translation_request_ready) begin assert(!translation_owned); translation_owned <= 1; end
    if (translation_response_valid && translation_response_ready) translation_owned <= 0;
  end
'''
    body = re.sub(r'\bmemory_(request|response)(?:_bits_\w+|_valid|_ready)\b', lambda m: 'FORMAL_FETCH_CACHE_' + m[0].replace('memory_', 'upstream_', 1), body)
    if translated:
        body = re.sub(r'\baccepting\b', '(state == 0)', body)
    return ('WideFetch', body + FETCH_PHYSICAL, '', '')


def instruction_cache_case(parameters):
    index_bits = (parameters['iCacheBytes'] // 64 - 1).bit_length()
    if parameters.get('enableBurstRefill'):
        body = r'''
  reg cache_past = 0, cache_owned, cache_bus, cache_killed, cache_authorized, cache_sent, cache_fault;
  reg [63:0] cache_address, cache_permission;
  reg [7:0] cache_tag;
  reg [15:0] cache_filled;
  reg [3:0] cache_word;
  reg [31:0] cache_upper;
  reg cache_terminal;
  (* anyconst *) reg [INDEX-1:0] cache_watched;
  wire cache_reply = downstream_response_valid && downstream_response_ready;
  wire cache_error = downstream_response_bits_fault || downstream_response_bits_tag != cache_tag;
  wire cache_abort = cache_killed || cancel || invalidate;
  wire cache_line_error = cache_fault || cache_error || downstream_response_bits_last != (cache_word == 14);
  wire cache_write = !bypass && !cache_abort && ((state == 6 && !cache_fault) || (cache_reply && !cache_line_error));
  always @(posedge clock) begin
    cache_past <= 1;
    if (!cache_past) assume(reset); else assume(!reset);
    if (upstream_request_valid) assume(upstream_request_bits_address[1:0] == 0);
    if (reset) begin cache_owned <= 0; cache_bus <= 0; cache_killed <= 0; cache_authorized <= 0; cache_filled <= 0; cache_sent <= 0; cache_fault <= 0; cache_word <= 0; end
    else begin
      assume(!downstream_response_valid || cache_bus);
      if ($past(!reset && downstream_response_valid && !downstream_response_ready)) begin assume(downstream_response_valid); assume($stable({downstream_response_bits_data, downstream_response_bits_fault, downstream_response_bits_tag, downstream_response_bits_last})); end
      assert(state <= 6 && cache_owned == (state != 0));
      assert(downstream_response_ready == (cache_bus && state == 4));
      if (cache_bus) assert(cache_owned && (state == 4 || state == 6));
      if (state == 6) assert(cache_bus == !cache_terminal);
      if (cache_owned) assert(address == cache_address && tag == cache_tag && killed == cache_killed && word == cache_word && fault == cache_fault);
      assert(filling_0 == cache_write);
      if (filling_0) assert(formal_cache_write_data == (state == 6 ? cache_upper : downstream_response_bits_data[31:0]));
      if (cache_owned && (cancel || invalidate)) cache_killed <= 1;
      if (state == 2 && allowed && !cache_abort) begin cache_authorized <= 1; cache_permission <= checkAddress; end
      assert(checkSize == (bypass ? 2 : 6));
      if (!bypass && (state == 2 || state == 3)) assert(cache_word == 0 && cache_filled == 0);
      if (!bypass && !cache_fault && (state == 4 || state == 6)) assert(cache_word[0] == (state == 6));
      if (downstream_request_valid) begin
        assert(cache_owned && cache_authorized && !cache_bus);
        assert(downstream_request_bits_address == cache_permission && downstream_request_bits_address == (bypass ? cache_address : {cache_address[63:6], 6'b0}) && downstream_request_bits_tag == cache_tag);
        assert(downstream_request_bits_fetch && !downstream_request_bits_write && !downstream_request_bits_atomic && !downstream_request_bits_atomicOperation && !downstream_request_bits_scEligible);
        assert(downstream_request_bits_size == (bypass ? 2 : 6) && downstream_request_bits_mask == 0 && downstream_request_bits_data == 0);
      end
      if (downstream_request_valid && downstream_request_ready) begin cache_bus <= 1; cache_sent <= 1; cache_authorized <= 0; end
      if (cache_reply) begin
        assert(cache_owned && cache_bus);
        if (downstream_response_bits_last || bypass) cache_bus <= 0;
        if (!bypass) begin cache_fault <= cache_line_error; cache_upper <= downstream_response_bits_data[63:32]; cache_terminal <= downstream_response_bits_last; if (cache_word != 15) cache_word <= cache_word + 1; end
        else if (!cache_abort && cache_error) cache_fault <= 1;
      end
      if (state == 6) begin
        if (cache_terminal && cache_fault && !cache_abort) cache_fault <= 0;
        assert(upperWord == cache_upper && terminal == cache_terminal);
        if (cache_word != 15) cache_word <= cache_word + 1;
      end
      if (!bypass && !cache_fault && !cache_killed && (state == 2 || state == 3 || state == 4 || state == 6)) assert(cache_filled == ((16'h1 << cache_word) - 1));
      if (cache_write) cache_filled[cache_word] <= 1;
      if (state == 2 && !allowed && bypass && !cache_abort) cache_fault <= 1;
      if (upstream_response_valid) begin
        assert(cache_owned && !cache_bus && !downstream_request_valid && upstream_response_bits_last);
        assert(upstream_response_bits_tag == cache_tag && upstream_response_bits_fault == cache_fault);
        if (upstream_response_ready) cache_owned <= 0;
      end
      if (upstream_request_valid && upstream_request_ready) begin
        assert(!cache_bus && (!cache_owned || (upstream_response_valid && upstream_response_ready)));
        cache_owned <= 1; cache_address <= upstream_request_bits_address; cache_tag <= upstream_request_bits_tag;
        cache_killed <= 0; cache_authorized <= 0; cache_filled <= 0; cache_sent <= 0; cache_fault <= 0; cache_word <= 0;
      end
      if ($past(!reset)) begin
        if ($past(invalidate)) assert(valid == 0);
        if ($past(state == 1 && !cache_abort && !hit_0)) assert(!valid[cache_address[INDEX+5:6]]);
        if (valid[cache_watched] && !$past(valid[cache_watched])) assert($past(state == 6 && cache_terminal && !fault && !cache_abort && !bypass && cache_filled == 16'h7fff && cache_word == 15 && cache_address[INDEX+5:6] == cache_watched));
        if ($past(downstream_request_valid && !downstream_request_ready)) begin assert(downstream_request_valid); assert($stable({downstream_request_bits_address, downstream_request_bits_tag, downstream_request_bits_size, downstream_request_bits_privileged})); end
        if ($past(upstream_response_valid && !upstream_response_ready)) begin assert(upstream_response_valid); assert($stable({upstream_response_bits_data, upstream_response_bits_fault, upstream_response_bits_tag, upstream_response_bits_last})); end
        if ($past(state == 6 && cache_terminal && fault && !cache_abort)) assert(bypass && state == 2 && checkAddress == cache_address && !upstream_response_valid);
        if ($past(state == 2 && !allowed && !bypass && !cache_abort)) assert(bypass && state == 2 && checkAddress == cache_address && !downstream_request_valid);
      end
      cover(upstream_response_valid && !cache_fault && cache_filled == 16'hffff);
      cover(upstream_response_valid && !cache_fault && !cache_sent && !cache_killed);
      cover(downstream_request_valid && !downstream_request_ready && cancel);
      cover(cache_bus && cancel && !downstream_response_valid);
      cover(state == 6 && cache_terminal && invalidate && !fault);
      cover(bypass && state == 2 && !allowed);
      cover(upstream_response_valid && cache_fault && cache_sent);
      cover(upstream_response_valid && cache_killed && !upstream_response_ready);
    end
  end
'''.replace('INDEX', str(index_bits))
        return ('InstructionCache', body, '~(filling & terminal & ~abort)', '~(filling & terminal)')
    body = r'''
  reg cache_past = 0, cache_owned, cache_bus, cache_killed, cache_authorized, cache_sent, cache_fault;
  reg [63:0] cache_address, cache_permission, cache_beat;
  reg [7:0] cache_tag;
  reg [15:0] cache_filled;
  (* anyconst *) reg [INDEX-1:0] cache_watched;
  wire cache_reply = downstream_response_valid && downstream_response_ready;
  wire cache_error = downstream_response_bits_fault || downstream_response_bits_tag != cache_tag;
  wire cache_abort = cache_killed || cancel || invalidate;
  always @(posedge clock) begin
    cache_past <= 1;
    if (!cache_past) assume(reset); else assume(!reset);
    if (upstream_request_valid) assume(upstream_request_bits_address[1:0] == 0);
    if (reset) begin
      cache_owned <= 0; cache_bus <= 0; cache_killed <= 0; cache_authorized <= 0;
      cache_filled <= 0; cache_sent <= 0; cache_fault <= 0;
    end else begin
      assert(state <= 5 && cache_owned == (state != 0) && cache_bus == downstream_response_ready);
      if (cache_owned) assert(address == cache_address && tag == cache_tag && killed == cache_killed &&
        fault == cache_fault && cache_address[1:0] == 0);
      if (cache_bus) assert(cache_beat == (bypass ? cache_address : {cache_address[63:6], word, 2'b0}));
      assert(filling_0 == (cache_reply && !cache_error && !bypass && !cache_abort));
      if (cache_owned && (cancel || invalidate)) cache_killed <= 1;
      if (state == 2 && allowed && !cache_abort) begin
        cache_authorized <= 1; cache_permission <= checkAddress;
      end
      if (downstream_request_valid) begin
        assert(cache_owned && cache_authorized && !cache_bus);
        assert(downstream_request_bits_address == cache_permission && downstream_request_bits_tag == cache_tag);
        assert(downstream_request_bits_fetch && !downstream_request_bits_write && !downstream_request_bits_atomic &&
          !downstream_request_bits_atomicOperation && !downstream_request_bits_scEligible);
        assert(downstream_request_bits_size == 2 && downstream_request_bits_mask == 0 && downstream_request_bits_data == 0);
      end
      if (downstream_request_valid && downstream_request_ready) begin
        cache_bus <= 1; cache_sent <= 1; cache_authorized <= 0;
        cache_beat <= downstream_request_bits_address;
      end
      if (cache_reply) begin
        assert(cache_owned && cache_bus);
        cache_bus <= 0;
        if (!cache_abort && !cache_error && !bypass) cache_filled[cache_beat[5:2]] <= 1;
        if (!cache_abort && cache_error && cache_beat == cache_address) cache_fault <= 1;
      end
      if (state == 2 && !allowed && !cache_abort && checkAddress == cache_address) cache_fault <= 1;
      if (state >= 2 && state <= 4 && !bypass && !cache_killed)
        assert(cache_filled == ((16'h1 << word) - 1));
      if (upstream_response_valid) begin
        assert(cache_owned && !cache_bus && !downstream_request_valid && upstream_response_bits_last);
        assert(upstream_response_bits_tag == cache_tag && upstream_response_bits_fault == cache_fault);
        if (upstream_response_ready) cache_owned <= 0;
      end
      if (upstream_request_valid && upstream_request_ready) begin
        assert(!cache_bus && (!cache_owned || (upstream_response_valid && upstream_response_ready)));
        cache_owned <= 1; cache_address <= upstream_request_bits_address; cache_tag <= upstream_request_bits_tag;
        cache_killed <= 0; cache_authorized <= 0;
        cache_filled <= 0; cache_sent <= 0; cache_fault <= 0;
      end
      if (cache_past && $past(!reset)) begin
        if ($past(invalidate)) assert(valid == 0);
        if (valid[cache_watched] && !$past(valid[cache_watched]))
          assert($past(cache_reply && !cache_error && !cache_abort && !bypass &&
            cache_beat[INDEX+5:6] == cache_watched && cache_filled == 16'h7fff && word == 15));
        if ($past(downstream_request_valid && !downstream_request_ready)) begin
          assert(downstream_request_valid);
          assert($stable({downstream_request_bits_address, downstream_request_bits_tag, downstream_request_bits_size,
            downstream_request_bits_data, downstream_request_bits_mask, downstream_request_bits_fetch,
            downstream_request_bits_write, downstream_request_bits_atomic,
            downstream_request_bits_atomicOperation, downstream_request_bits_scEligible}));
        end
        if ($past(upstream_response_valid && !upstream_response_ready)) begin
          assert(upstream_response_valid);
          assert($stable({upstream_response_bits_data, upstream_response_bits_fault, upstream_response_bits_tag}));
        end
        if ($past(cache_reply && !cache_abort && cache_error && cache_beat != cache_address))
          assert(bypass && state == 2 && checkAddress == cache_address && !upstream_response_valid);
        if ($past(state == 2 && !cache_abort && !allowed && checkAddress != cache_address))
          assert(bypass && state == 2 && checkAddress == cache_address && !downstream_request_valid);
      end
      cover(upstream_response_valid && !cache_fault && cache_filled == 16'hffff);
      cover(upstream_response_valid && !cache_fault && !cache_sent && !cache_killed);
      cover(downstream_request_valid && !downstream_request_ready && cancel);
      cover(cache_bus && cancel && !downstream_response_valid);
      cover(cache_reply && word == 15 && invalidate && !cache_error);
      cover(bypass && state == 2 && !allowed);
      cover(upstream_response_valid && cache_fault && cache_sent);
      cover(upstream_response_valid && cache_killed && !upstream_response_ready);
    end
  end
'''.replace('INDEX', str(index_bits))
    return ('InstructionCache', body, ': ~filling | abort | responseFault | bypass | ~complete',
            ': ~filling | responseFault | bypass | ~complete')


def data_cache_case(parameters):
    index = (parameters['dCacheBytes'] // 64 - 1).bit_length()
    sector = index + 3
    fields = ('address', 'data', 'size', 'mask', 'tag', 'write', 'fetch', 'privileged', 'atomic', 'atomicOperation', 'scEligible')
    payload = lambda prefix: '{' + ', '.join(prefix + '_' + field for field in fields) + '}'
    ranges = ' || '.join(f"(upstream_request_bits_address >= 64'h{int(r['base']):x} && upstream_request_bits_address <= 64'h{int(r['base'])+int(r['size'])-8:x})"
                         for r in parameters['memoryRegions'] if r.get('dataCacheable') and r['readable'] and not r['device'] and int(r['size']) >= 8)
    body = f'''
  reg cache_past = 0, cache_owned, cache_bus, cache_sent, cache_finished, cache_killed, cache_eligible;
  reg [156:0] cache_request;
  reg [63:0] cache_address, cache_result;
  reg [7:0] cache_tag;
  reg cache_fault, cache_same_tag;
  (* anyconst *) reg [{sector-1}:0] cache_watched;
  wire cache_accept = upstream_request_valid && upstream_request_ready;
  wire cache_reply = downstream_response_valid && downstream_response_ready;
  wire cache_sample = state == 1 && eligible_layerCapture && hit_layerCapture;
  wire cache_invalidate = invalidate_valid && invalidate_ready;
  wire cache_collision = cache_invalidate && invalidate_bits[{index+5}:6] == cache_address[{index+5}:6];
  wire cache_error = downstream_response_bits_fault || downstream_response_bits_tag != cache_tag;
  wire cache_clear_watched = cache_invalidate && invalidate_bits[{index+5}:6] == cache_watched[{sector-1}:3];
  wire cache_expected_valid = !cache_clear_watched &&
    ((filling_0 && cache_address[{index+5}:3] == cache_watched) ||
      (valid[cache_watched] && !(filling_0 && !cache_same_tag && cache_address[{index+5}:6] == cache_watched[{sector-1}:3])));
  wire cache_input_eligible = !upstream_request_bits_write && !upstream_request_bits_fetch && !upstream_request_bits_atomic &&
    upstream_request_bits_size == 3 && upstream_request_bits_address[2:0] == 0 && ({ranges or '0'});
  always @(posedge clock) begin
    cache_past <= 1;
    if (!cache_past) assume(reset); else assume(!reset);
    if (reset) begin
      cache_owned <= 0; cache_bus <= 0; cache_sent <= 0; cache_finished <= 0; cache_killed <= 0;
    end else begin
      assume(!downstream_response_valid || cache_bus);
      if ($past(!reset && downstream_response_valid && !downstream_response_ready)) begin
        assume(downstream_response_valid);
        assume($stable({{downstream_response_bits_data, downstream_response_bits_fault, downstream_response_bits_tag, downstream_response_bits_last}}));
      end
      assert(state <= 4 && cache_owned == (state != 0) && cache_bus == (state == 3));
      assert(cache_finished == (state == 4));
      assert(invalidate_ready);
      if (cache_accept) begin
        assert(!cache_owned);
        cache_owned <= 1; cache_request <= {payload('upstream_request_bits')};
        cache_address <= upstream_request_bits_address; cache_tag <= upstream_request_bits_tag;
        cache_eligible <= cache_input_eligible;
        cache_bus <= 0; cache_sent <= 0; cache_finished <= 0;
        cache_killed <= cache_invalidate && invalidate_bits[{index+5}:6] == upstream_request_bits_address[{index+5}:6];
      end
      if (cache_owned) begin
        assert({payload('request')} == cache_request);
        assert(request_address == cache_address && request_tag == cache_tag);
        assert(eligible_layerCapture == cache_eligible && invalidated == cache_killed);
        if (cache_collision) cache_killed <= 1;
      end
      if (state == 1) cache_same_tag <= _dataTags_ext_R0_data == cache_address[{parameters['physicalAddressBits']-1}:{index+6}];
      if (state >= 2) assert(sameTag == cache_same_tag);
      if (downstream_request_valid) begin
        assert(cache_owned && !cache_bus && !cache_sent);
        assert({payload('downstream_request_bits')} == cache_request);
      end
      if (downstream_request_valid && downstream_request_ready) begin cache_bus <= 1; cache_sent <= 1; end
      if (cache_reply) begin
        assert(cache_owned && cache_bus);
        cache_bus <= 0; cache_finished <= 1;
        cache_result <= downstream_response_bits_data; cache_fault <= cache_error;
      end
      if (cache_sample) begin
        assert(cache_owned && cache_eligible && !cache_bus && !cache_sent && !cache_killed && !cache_collision);
        assert(valid[cache_address[{index+5}:3]] && _dataTags_ext_R0_data == cache_address[{parameters['physicalAddressBits']-1}:{index+6}]);
        cache_finished <= 1; cache_result <= output_layerCapture; cache_fault <= 0;
      end
      assert(filling_0 == (cache_reply && cache_eligible && !cache_killed && !cache_collision && !cache_error));
      if (upstream_response_valid) begin
        assert(cache_owned && cache_finished && !cache_bus && !downstream_request_valid);
        assert(upstream_response_bits_tag == cache_tag && upstream_response_bits_fault == cache_fault);
        if (!cache_fault) assert(upstream_response_bits_data == cache_result);
        if (upstream_response_ready) begin cache_owned <= 0; cache_finished <= 0; end
      end
      if ($past(!reset)) begin
        assert(valid[cache_watched] == $past(cache_expected_valid));
        if ($past(cache_invalidate && invalidate_bits[{index+5}:6] == cache_watched[{sector-1}:3])) assert(!valid[cache_watched]);
        if (valid[cache_watched] && !$past(valid[cache_watched]))
          assert($past(filling_0 && cache_address[{index+5}:3] == cache_watched));
        if ($past(downstream_request_valid && !downstream_request_ready)) begin
          assert(downstream_request_valid); assert($stable({payload('downstream_request_bits')}));
        end
        if ($past(upstream_response_valid && !upstream_response_ready)) begin
          assert(upstream_response_valid);
          assert($stable({{upstream_response_bits_data, upstream_response_bits_fault, upstream_response_bits_tag}}));
        end
      end
      cover(cache_sample);
      cover(cache_reply && cache_collision && !cache_error);
      cover(cache_bus && cache_invalidate && !downstream_response_valid);
      cover(downstream_request_valid && !downstream_request_ready && cache_invalidate);
      cover(upstream_response_valid && !upstream_response_ready && cache_invalidate);
      cover(upstream_response_valid && cache_fault);
      cover(cache_reply && !cache_eligible && request_atomic);
    end
  end
'''
    return ('DataCache', body, 'assign invalidate_ready =', "assign invalidate_ready = 1'h0 &")


def coherence_case(parameters):
    count = parameters['hartCount']
    fields = ('address', 'data', 'size', 'mask', 'tag', 'write', 'fetch', 'privileged', 'atomic', 'atomicOperation', 'scEligible')
    payload = lambda prefix: '{' + ', '.join(prefix + '_bits_' + field for field in fields) + '}'
    vector = lambda suffix: '{' + ', '.join(f'invalidate_{i}_{suffix}' for i in reversed(range(count))) + '}'
    ranges = ' || '.join(f"(upstream_request_bits_address >= 64'h{int(r['base']):x} && upstream_request_bits_address < 64'h{int(r['base'])+int(r['size']):x})"
                         for r in parameters['memoryRegions'] if r.get('dataCacheable'))
    body = f'''
  reg coherent_past = 0, coherent_started, coherent_bus;
  reg [{count-1}:0] coherent_completed;
  wire [{count-1}:0] coherent_valid = {vector('valid')};
  wire [{count-1}:0] coherent_ready = {vector('ready')};
  wire coherent_write = upstream_request_bits_write && ({ranges or '0'});
  always @(posedge clock) begin
    coherent_past <= 1;
    if (!coherent_past) assume(reset); else assume(!reset);
    if (reset) begin coherent_started <= 0; coherent_completed <= 0; coherent_bus <= 0; end
    else begin
      if ($past(!reset && upstream_request_valid && !upstream_request_ready)) begin
        assume(upstream_request_valid); assume($stable({payload('upstream_request')}));
      end
      assume(!downstream_response_valid || coherent_bus);
      assume(!upstream_request_valid || !coherent_bus);
      assert(busy == coherent_started);
      if (busy) assert(pending == ~coherent_completed);
      if (coherent_started) assert(upstream_request_valid && coherent_write && !coherent_bus);
      if (coherent_started) assert(coherent_valid == ~coherent_completed);
      else assert(coherent_valid == 0);
      if (upstream_request_valid && coherent_write && !coherent_started && !coherent_bus) begin
        coherent_started <= 1; coherent_completed <= 0;
      end
      coherent_completed <= coherent_completed | (coherent_valid & coherent_ready);
      assert((upstream_request_valid && upstream_request_ready) == (downstream_request_valid && downstream_request_ready));
      if (downstream_request_valid) begin
        assert(upstream_request_valid && !coherent_bus);
        assert({payload('downstream_request')} == {payload('upstream_request')});
        if (coherent_write) assert(coherent_started && &coherent_completed);
      end
      if (downstream_request_valid && downstream_request_ready) begin
        assert(upstream_request_ready); coherent_bus <= 1;
        coherent_started <= 0; coherent_completed <= 0;
      end
      assert(upstream_response_valid == downstream_response_valid);
      assert(downstream_response_ready == upstream_response_ready);
      if (upstream_response_valid) assert({{upstream_response_bits_data, upstream_response_bits_fault, upstream_response_bits_tag, upstream_response_bits_last}} ==
        {{downstream_response_bits_data, downstream_response_bits_fault, downstream_response_bits_tag, downstream_response_bits_last}});
      if (downstream_response_valid && downstream_response_ready && downstream_response_bits_last) coherent_bus <= 0;
      cover(coherent_started && |coherent_completed && !(&coherent_completed));
      cover(downstream_request_valid && coherent_write && !downstream_request_ready);
      cover(downstream_request_valid && !coherent_write);
      cover(downstream_response_valid && !upstream_response_ready);
'''
    for hart in range(count):
        body += f'''      if (invalidate_{hart}_valid) assert(invalidate_{hart}_bits == upstream_request_bits_address);
      if ($past(!reset && invalidate_{hart}_valid && !invalidate_{hart}_ready)) begin
        assert(invalidate_{hart}_valid && $stable(invalidate_{hart}_bits));
      end
'''
    body += '    end\n  end\n'
    if count == 1:
        body = body.replace('      cover(coherent_started && |coherent_completed && !(&coherent_completed));\n', '')
    return ('Coherence', body, 'assign downstream_request_valid =', "assign downstream_request_valid = upstream_request_valid |")


def synchronization_witness(parameters, mode):
    body = r'''
  (* anyconst *) reg [2:0] sync_scenario;
  reg [1:0] sync_packet = 0;
  reg sync_stalled = 0, sync_waited = 0, pending = 0;
  always @(posedge clock) if (!reset) begin
    if (instruction_valid && instruction_ready && sync_packet != 3) sync_packet <= sync_packet + 1;
    if (data_request_valid && !data_request_ready) sync_stalled <= 1;
    if (data_request_valid && data_request_ready) pending <= 1;
    if (data_response_valid && data_response_ready) pending <= 0;
    sync_waited <= pending;
  end
'''
    body += '  always @* assume(sync_scenario < 4);\n'
    values = dict(instruction_valid=1, instruction_bits_count=1,
                  instruction_bits_packets_0_length=4,
                  instruction_bits_packets_0_pc=f"64'h{int(parameters['resetVector']):x}",
                  instruction_bits_packets_0_cause=1,
                  instruction_bits_packets_0_fault='sync_scenario == 2 && sync_packet == 0',
                  instruction_bits_packets_0_instruction="sync_packet == 0 ? (sync_scenario >= 2 ? 32'h0000100f : 32'h00003023) : sync_packet == 1 ? (sync_scenario == 0 ? 32'h0000000f : 32'h0000100f) : 32'h00003023",
                  data_request_ready='sync_scenario != 0 || sync_stalled',
                  data_response_valid='pending && (sync_scenario != 0 || sync_waited)',
                  data_response_bits_last=1)
    scenario = {'mutation': 3, 'mutation-serialization': 0, 'mutation-flag': 3,
                'mutation-fault': 2, 'mutation-order': 0}.get(mode)
    if scenario is not None:
        body += f'  always @* assume(sync_scenario == {scenario});\n'
    return body, values


def interrupt_witness(parameters, mode):
    body = r'''
  (* anyconst *) reg [2:0] irq_scenario;
  (* anyconst *) reg irq_delay;
  reg [6:0] age = 0;
  reg [1:0] irq_packet = 0;
  reg irq_stalled = 0, irq_latched = 0, irq_redirected = 0;
  wire irq_initializing = age < 24;
  wire [1:0] irq_limit = irq_scenario == 3 || irq_scenario == 4 ? 2 : 1;
  always @(posedge clock) if (reset) age <= 0; else if (age != 127) age <= age + 1;
  always @(posedge clock) if (!reset) begin
    if (instruction_valid && instruction_ready && !irq_initializing && irq_packet != 3) irq_packet <= irq_packet + 1;
    if (data_request_valid && !data_request_ready) irq_stalled <= 1;
    if (formal_events[2]) irq_latched <= 1;
    if (formal_events[3]) begin irq_latched <= 0; irq_redirected <= 1; end
  end
  always @* assume(irq_scenario <= 5);
'''
    values = dict(instruction_valid='age == 0 || age == 8 || age == 16 || (!irq_initializing && (irq_packet < irq_limit || irq_redirected))',
                  instruction_bits_count=1, instruction_bits_packets_0_length=4,
                  instruction_bits_packets_0_pc=f"64'h{int(parameters['resetVector']):x}",
                  instruction_bits_packets_0_instruction="""irq_initializing ?
      (age < 8 ? 32'h00800093 : age < 16 ? 32'h30409073 : 32'h30009073) :
      irq_redirected ? 32'h13 : irq_packet == 0 ?
      (irq_scenario == 1 ? 32'h0010302f : irq_scenario == 2 ? 32'h02108133 : irq_scenario == 5 ? 32'h0000100f : 32'h00103023) :
      irq_scenario == 3 ? 32'h02108133 : 32'h0000100f""",
                  data_request_ready='irq_stalled || (irq_scenario != 0 && irq_scenario != 4)',
                  data_response_valid='data_response_ready && (irq_scenario != 3 || formal_events[1])',
                  data_response_bits_last=1,
                  interrupts_software='formal_events[2] || irq_latched || (formal_events[0] && (!irq_delay || formal_events[1])) || (irq_scenario == 5 && formal_events[4])')
    if mode.startswith('mutation'):
        body += f"  always @* assume(irq_scenario == {0 if mode == 'mutation' else 2});\n"
    return body, values


def arbiter_case(parameters):
    count = 2 * parameters['hartCount']
    bits = (count - 1).bit_length()
    fields = dict(address=64, data=64, size=3, mask=8, tag=8, write=1, fetch=1, privileged=1, atomic=1, atomicOperation=5, scEligible=1)
    payload = lambda prefix: '{' + ', '.join(prefix + '_bits_' + field for field in fields) + '}'
    vector = lambda suffix: '{' + ', '.join(f'ports_{i}_{suffix}' for i in reversed(range(count))) + '}'
    body = f'''
  reg past_valid = 0;
  reg pending, sent, wrapped;
  reg [{bits-1}:0] expected_owner;
  reg [{sum(fields.values())-1}:0] captured;
  (* anyconst *) reg [{bits-1}:0] watched;
  reg [{bits}:0] bypassed;
  wire [{count-1}:0] requests = {vector('request_valid')};
  wire [{count-1}:0] ready = {vector('request_ready')};
  wire [{count-1}:0] responses = {vector('response_valid')};
  wire [{count-1}:0] consumers = {vector('response_ready')};
  wire [{count-1}:0] accepted = requests & ready;
  wire completed = downstream_response_valid && downstream_response_ready && downstream_response_bits_last;
  wire [{bits}:0] distance = watched >= next ? watched - next : {count} + watched - next;
  always @(posedge clock) begin
    past_valid <= 1;
    assume(watched < {count});
    if (!past_valid) assume(reset);
    else assume(!reset);
    if (reset) begin pending <= 0; sent <= 0; bypassed <= 0; wrapped <= 0; end
    else begin
      assume(!downstream_response_valid || sent);
      if ($past(!reset && downstream_response_valid && !downstream_response_ready)) begin
        assume(downstream_response_valid);
        assume($stable({{downstream_response_bits_data, downstream_response_bits_fault, downstream_response_bits_tag, downstream_response_bits_last}}));
      end
      assert($onehot0(accepted) && $onehot0(responses));
      assert(pending == (state != 0) && sent == (state == 2));
      assert(next < {count});
      if (!pending && |requests) assert(|accepted);
      if (pending) begin
        assert(ready == 0 && expected_owner == owner);
        assert(hartId == (expected_owner >> 1));
        assert(downstream_request_valid == !sent);
      end
      if (downstream_request_valid) assert(pending && !sent && {payload('downstream_request')} == captured);
      if (downstream_request_valid && downstream_request_ready) sent <= 1;
      assert(downstream_response_ready == (sent && consumers[expected_owner]));
      assert(responses == ((sent && downstream_response_valid) ? ({count}'d1 << expected_owner) : 0));
      if (completed) begin
        assert(pending && sent);
        pending <= 0; sent <= 0;
        if (expected_owner == {count-1}) wrapped <= 1;
      end
      if (!requests[watched] || accepted[watched]) bypassed <= 0;
      else if (completed && expected_owner != watched) bypassed <= bypassed + 1;
      assert(bypassed < {count});
      if (requests[watched]) assert({{1'b0, bypassed}} + {{1'b0, distance}} < {count});
      cover(&requests && |accepted);
      cover(downstream_request_valid && !downstream_request_ready);
      cover(downstream_response_valid && !downstream_response_ready);
      cover(completed && expected_owner == {count-1});
      cover(wrapped && accepted[0]);
      cover(bypassed == {count-1} && accepted[watched]);
'''
    for i in range(count):
        prefix = f'ports_{i}_request'
        body += f'''
      if ($past(!reset && {prefix}_valid && !{prefix}_ready)) begin
        assume({prefix}_valid);
      end
      if (accepted[{i}]) begin
        assert(!pending); pending <= 1; expected_owner <= {i}; captured <= {payload(prefix)};
      end
      if (ports_{i}_response_valid) assert({{ports_{i}_response_bits_data, ports_{i}_response_bits_fault, ports_{i}_response_bits_tag, ports_{i}_response_bits_last}} ==
        {{downstream_response_bits_data, downstream_response_bits_fault, downstream_response_bits_tag, downstream_response_bits_last}});
'''
    body += '    end\n  end\n'
    return ('MemoryArbiter', body, 'assign ports_0_response_valid =',
            "assign ports_0_response_valid = downstream_response_valid |")


def memory_case(parameters):
    fields = ('address', 'data', 'size', 'mask', 'tag', 'write', 'fetch', 'privileged', 'atomic', 'atomicOperation', 'scEligible')
    payload = lambda prefix: '{' + ', '.join(prefix + '_bits_' + field for field in fields) + '}'
    body = r'''
  reg memory_past = 0, memory_owned, memory_denied;
  reg [7:0] memory_tag;
  wire m_atomic = upstream_request_bits_atomic, m_write = upstream_request_bits_write;
  wire m_fetch = upstream_request_bits_fetch;
  wire [4:0] m_operation = upstream_request_bits_atomicOperation;
  wire [63:0] m_address = upstream_request_bits_address;
  wire [7:0] m_mask = upstream_request_bits_mask;
  wire m_shape = !m_atomic || (!m_fetch && upstream_request_bits_size == 3 &&
    (m_operation == 2 ? !m_write : (m_operation == 0 || m_operation == 1 || m_operation == 3 || m_operation == 8) && m_write && m_mask == 255));
  reg m_allowed;
  always @* begin
    m_allowed = 0;
    case (upstream_request_bits_size)
'''
    for size in (*range(4), *((6,) if parameters.get('enableBurstRefill') else ())):
        count = 1 << size
        line_shape = 'm_fetch && !m_write && !m_atomic && ' if size == 6 else ''
        body += f"      {size}: if ({line_shape}m_shape && (m_address & 64'd{count-1}) == 0 && (!m_write || (m_mask != 0 && (m_mask & 8'h{(255 ^ ((1 << count) - 1)) if size != 6 else 0:x}) == 0))) begin\n"
        for region in parameters['memoryRegions']:
            rights = {key: int(region[key]) for key in ('readable', 'writable', 'executable', 'device', 'atomic')}
            if int(region['size']) >= count:
                body += f"        if (m_address >= 64'h{int(region['base']):x} && m_address <= 64'h{int(region['base'])+int(region['size'])-count:x} &&\n"
                body += f"          (m_fetch ? {int(rights['executable'] and not rights['device'])} && !m_write && !m_atomic : m_atomic ? {int(rights['atomic'] and not rights['device'])} &&\n"
                body += f"          (m_operation == 2 ? {rights['readable']} : m_operation == 3 ? {rights['writable']} : {rights['readable'] and rights['writable']}) : m_write ? {rights['writable']} : {rights['readable']})) m_allowed = 1;\n"
        body += '      end\n'
    body += r'''    endcase
  end
  always @(posedge clock) begin
    memory_past <= 1;
    if (!memory_past) assume(reset); else assume(!reset);
    if (reset) begin memory_owned <= 0; memory_denied <= 0; end
    else begin
      assert(pending == memory_owned);
      if (memory_owned) assert(localFault == memory_denied && tag == memory_tag);
      assert(upstream_request_ready == (!memory_owned && (!m_allowed || downstream_request_ready)));
      assert(downstream_request_valid == (upstream_request_valid && !memory_owned && m_allowed));
      if (downstream_request_valid) assert(DOWNSTREAM_PAYLOAD == UPSTREAM_PAYLOAD);
      assert(upstream_response_valid == (memory_owned && (memory_denied || downstream_response_valid)));
      assert(downstream_response_ready == (memory_owned && !memory_denied && upstream_response_ready));
      if (upstream_request_valid && upstream_request_ready) begin
        memory_owned <= 1; memory_denied <= !m_allowed; memory_tag <= upstream_request_bits_tag;
      end
      if (upstream_response_valid) begin
        assert(upstream_response_bits_data == (memory_denied ? 0 : downstream_response_bits_data));
        assert(upstream_response_bits_tag == (memory_denied ? memory_tag : downstream_response_bits_tag));
        assert(upstream_response_bits_fault == (memory_denied || downstream_response_bits_fault));
        assert(upstream_response_bits_last == (memory_denied || downstream_response_bits_last));
        if (upstream_response_ready && upstream_response_bits_last) memory_owned <= 0;
      end
      cover(memory_owned && memory_denied && !upstream_response_ready);
      cover(upstream_request_valid && m_atomic && !m_shape && upstream_request_ready);
      cover(upstream_request_valid && m_atomic && m_operation == 3 && !upstream_request_bits_scEligible && !m_allowed && upstream_request_ready);
    end
  end
'''.replace('DOWNSTREAM_PAYLOAD', payload('downstream_request')).replace('UPSTREAM_PAYLOAD', payload('upstream_request'))
    if any(region['atomic'] for region in parameters['memoryRegions']):
        body += '''  always @(posedge clock) if (!reset) begin
    cover(downstream_request_valid && m_atomic && m_operation == 2 && m_mask != 0);
    cover(downstream_request_valid && m_atomic && m_operation == 3 && !upstream_request_bits_scEligible);
  end
'''
    return ('Memory', body, 'assign downstream_request_valid =', "assign downstream_request_valid = 1'h1 |")


def axi_case(parameters):
    width = parameters['axiDataBits']
    lane_bits = (width // 8 - 1).bit_length()
    body = r'''
  reg checked_past = 0;
  reg held, can_read, can_write, read_owned, address_sent, data_sent;
  reg complete, expected_fault, is_atomic, retried;
  reg [63:0] accepted_address, addend, old_value;
  reg [2:0] accepted_size;
  reg [7:0] accepted_mask, accepted_tag;
  reg [4:0] accepted_operation;
  reg [ID-1:0] accepted_id;
  reg accepted_eligible, accepted_write;
  reg [2:0] accepted_protection;
  wire is_lr = is_atomic && accepted_operation == 2;
  wire is_sc = is_atomic && accepted_operation == 3;
  wire is_rmw = is_atomic && !is_lr && !is_sc;
  wire input_sc = memory_request_bits_atomic && memory_request_bits_atomicOperation == 3;
  wire input_write = memory_request_bits_write && (!memory_request_bits_atomic || input_sc);
  wire input_rejected = input_sc && !memory_request_bits_scEligible;
  wire read_fire = axi_ar_valid && axi_ar_ready;
  wire write_address_fire = axi_aw_valid && axi_aw_ready;
  wire write_data_fire = axi_w_valid && axi_w_ready;
  wire read_reply = axi_r_valid && axi_r_ready;
  wire write_reply = axi_b_valid && axi_b_ready;
  wire [63:0] shifted_value = axi_r_bits_data >> (accepted_address[LANE:0] * 8);
  wire [63:0] loaded_value = accepted_size == 0 ? {56'd0, shifted_value[7:0]} :
    accepted_size == 1 ? {48'd0, shifted_value[15:0]} :
    accepted_size == 2 ? {32'd0, shifted_value[31:0]} : accepted_size == 3 ? shifted_value : 0;
  wire read_bad = expected_fault || axi_r_bits_id != accepted_id || !axi_r_bits_last ||
    axi_r_bits_resp != (is_atomic ? 1 : 0);
  wire [63:0] update_value = accepted_operation == 1 ? addend : accepted_operation == 8 ? old_value | addend : old_value + addend;
  wire [63:0] stored_value = is_rmw ? update_value : addend;
  wire [WIDTH-1:0] stored_lanes = {{PAD{1'b0}}, stored_value};
  wire [BYTES-1:0] stored_mask = {{MASKPAD{1'b0}}, accepted_mask};
  always @(posedge clock) begin
    checked_past <= 1;
    if (!checked_past) assume(reset); else assume(!reset);
    if (reset) begin
      held <= 0; can_read <= 0; can_write <= 0; read_owned <= 0;
      address_sent <= 0; data_sent <= 0; complete <= 0; expected_fault <= 0; retried <= 0;
    end else begin
      assume(!axi_r_valid || read_owned);
      assume(!axi_b_valid || (address_sent && data_sent));
      if ($past(!reset && axi_r_valid && !axi_r_ready)) begin
        assume(axi_r_valid);
        assume($stable({axi_r_bits_data, axi_r_bits_resp, axi_r_bits_id, axi_r_bits_last}));
      end
      if ($past(!reset && axi_b_valid && !axi_b_ready)) begin
        assume(axi_b_valid);
        assume($stable({axi_b_bits_resp, axi_b_bits_id}));
      end
      if (memory_request_valid && memory_request_ready) begin
        assert(!held);
        held <= 1; complete <= input_rejected; expected_fault <= 0; old_value <= input_rejected ? 1 : 0; retried <= 0;
        is_atomic <= memory_request_bits_atomic; accepted_address <= memory_request_bits_address;
        accepted_operation <= memory_request_bits_atomicOperation; accepted_eligible <= memory_request_bits_scEligible;
        accepted_write <= memory_request_bits_write;
        accepted_protection <= {memory_request_bits_fetch, 1'b0, PRIVILEGED};
        accepted_id <= hartId[ID-1:0];
        addend <= memory_request_bits_data; accepted_size <= memory_request_bits_size;
        accepted_mask <= memory_request_bits_mask; accepted_tag <= memory_request_bits_tag;
        can_read <= !input_rejected && !input_write;
        can_write <= !input_rejected && input_write;
      end
      assert(memory_request_ready == !held && memory_response_valid == complete);
      assert(held == (can_read || can_write || complete));
      assert(!(can_read && can_write) && (!read_owned || can_read));
      assert(!(address_sent || data_sent) || can_write);
      if (held) begin
        assert(request_address == accepted_address && request_data == addend && request_size == accepted_size &&
          request_mask == accepted_mask && request_tag == accepted_tag && request_atomic == is_atomic);
        assert({request_fetch, 1'b0, STORED_PRIVILEGED} == accepted_protection);
        assert(request_atomicOperation == accepted_operation);
        assert(hartId_0 == accepted_id);
        assert(data == old_value && fault == expected_fault);
      end
      if (held && !complete)
        assert(awDone == address_sent && wDone == data_sent && request_write == can_write);
      assert(axi_ar_valid == (can_read && !read_owned));
      assert(axi_aw_valid == (can_write && !address_sent));
      assert(axi_w_valid == (can_write && !data_sent));
      assert(axi_r_ready == read_owned && axi_b_ready == (address_sent && data_sent));
      if (held && is_lr) assert(!axi_aw_valid && !axi_w_valid && !can_write);
      if (held && is_sc && accepted_write) assert(!axi_ar_valid && !can_read && !retried);
      if (held && is_sc && !accepted_eligible) assert(complete && old_value == 1 && !expected_fault);
      if (axi_ar_valid) begin
        assert(held && !complete && !can_write);
        assert(axi_ar_bits_prot == accepted_protection);
        assert(axi_ar_bits_addr == accepted_address[PHYSICAL:0] && axi_ar_bits_id == accepted_id &&
          axi_ar_bits_len == 0 && axi_ar_bits_size == accepted_size && axi_ar_bits_lock == is_atomic);
      end
      if (axi_aw_valid) begin
        assert(held && !complete && !can_read);
        assert(axi_aw_bits_prot == accepted_protection);
        assert(axi_aw_bits_addr == accepted_address[PHYSICAL:0] && axi_aw_bits_id == accepted_id &&
          axi_aw_bits_len == 0 && axi_aw_bits_size == accepted_size && axi_aw_bits_lock == is_atomic);
      end
      if (axi_w_valid) begin
        assert(axi_w_bits_last);
        assert(axi_w_bits_data == (stored_lanes << (accepted_address[LANE:0] * 8)));
        assert(axi_w_bits_strb == (stored_mask << accepted_address[LANE:0]));
      end
      if (read_fire) begin assert(!read_owned); read_owned <= 1; end
      if (write_address_fire) begin assert(!address_sent); address_sent <= 1; end
      if (write_data_fire) begin assert(!data_sent); data_sent <= 1; end
      if (read_reply) begin
        assert(held && read_owned && !can_write);
        old_value <= loaded_value; expected_fault <= read_bad;
        if (axi_r_bits_last) begin
          read_owned <= 0; can_read <= 0;
          if (is_rmw && !read_bad) can_write <= 1;
          else complete <= 1;
        end
      end
      if (write_reply) begin
        assert(held && can_write && address_sent && data_sent);
        can_write <= 0; address_sent <= 0; data_sent <= 0;
        if (is_rmw && axi_b_bits_resp == 0 && axi_b_bits_id == accepted_id) begin
          can_read <= 1; retried <= 1;
        end else begin
          complete <= 1;
          expected_fault <= axi_b_bits_id != accepted_id || (is_sc ? axi_b_bits_resp[1] : axi_b_bits_resp != (is_atomic ? 1 : 0));
          if (is_sc) old_value <= axi_b_bits_resp == 0 ? 1 : 0;
        end
      end
      if (memory_response_valid) begin
        assert(held && complete && !can_read && !can_write && !read_owned && !address_sent && !data_sent);
        assert(memory_response_bits_tag == accepted_tag && memory_response_bits_data == old_value);
        assert(memory_response_bits_fault == expected_fault && memory_response_bits_last);
        if (memory_response_ready) begin held <= 0; complete <= 0; end
      end
      if ($past(!reset && memory_response_valid && !memory_response_ready)) begin
        assert(memory_response_valid);
        assert($stable({memory_response_bits_data, memory_response_bits_fault, memory_response_bits_tag, memory_response_bits_last}));
      end
      cover(is_atomic && complete && !expected_fault && retried);
      cover(is_atomic && read_reply && axi_r_bits_resp == 0 && axi_r_bits_last);
      cover(is_atomic && read_reply && !axi_r_bits_last);
      cover(is_atomic && write_reply && axi_b_bits_resp[1]);
      cover(is_atomic && retried && read_reply && loaded_value != old_value);
      cover(is_atomic && complete && expected_fault && !can_write);
      cover(is_atomic && address_sent && !data_sent);
      cover(is_atomic && data_sent && !address_sent);
      cover(is_atomic && complete && !memory_response_ready && retried);
      cover(is_lr && complete && !expected_fault);
      cover(is_sc && complete && !accepted_eligible && old_value == 1 && !expected_fault);
      cover(is_sc && complete && accepted_eligible && old_value == 1 && !expected_fault);
      cover(is_sc && complete && accepted_eligible && old_value == 0 && !expected_fault);
      cover(is_rmw && accepted_operation == 8 && write_data_fire);
      cover(is_rmw && accepted_operation == 1 && write_data_fire);
      cover(held && accepted_id != 0 && axi_ar_valid && !axi_ar_ready);
    end
  end
'''
    if parameters.get('enableBurstRefill'):
        body = body.replace('reg checked_past = 0;', '''
  wire input_line = memory_request_bits_fetch && !memory_request_bits_write && !memory_request_bits_atomic && memory_request_bits_size == 6;
  reg line_owned = 0;
  reg line_address_sent, line_buffered, line_draining, line_done, line_fault, line_terminal, line_last_seen;
  reg [2:0] line_beat, line_slice;
  reg [WIDTH-1:0] line_block;
  wire [63:0] line_value = line_block >> (line_slice * 64);
  reg [63:0] line_address;
  reg [7:0] line_tag;
  reg [ID-1:0] line_id;
  reg [2:0] line_protection;
  reg checked_past = 0;''')
        body = body.replace('    end else begin\n      assume(!axi_r_valid', '    end else if (!line_owned) begin\n      assert(state <= 4); if (held) assert(!line);\n      assume(!axi_r_valid', 1)
        body = body.replace('if (memory_request_valid && memory_request_ready) begin', 'if (memory_request_valid && memory_request_ready && !input_line) begin', 1)
        body += r'''
  always @(posedge clock) begin
    if (!reset) begin assert(!(held && line_owned)); assert((held || line_owned) == (state != 0)); end
    if (reset) begin line_owned <= 0; line_buffered <= 0; line_address_sent <= 0; line_draining <= 0; line_done <= 0; line_fault <= 0; line_last_seen <= 0; end
    else begin
      if (memory_request_valid && memory_request_ready && input_line) begin
        assert(!held && !line_owned);
        line_owned <= 1; line_address_sent <= 0; line_buffered <= 0; line_draining <= 0; line_done <= 0; line_fault <= 0; line_last_seen <= 0;
        line_address <= memory_request_bits_address; line_tag <= memory_request_bits_tag; line_id <= hartId;
        line_protection <= {memory_request_bits_fetch, 1'b0, PRIVILEGED}; line_beat <= 0; line_slice <= 0;
      end
      if (line_owned) begin
        assume(!axi_r_valid || (line_address_sent && !line_last_seen)); assume(!axi_b_valid);
        if ($past(!reset && axi_r_valid && !axi_r_ready)) begin assume(axi_r_valid); assume($stable({axi_r_bits_data, axi_r_bits_resp, axi_r_bits_id, axi_r_bits_last})); end
        assert(state == (!line_address_sent ? 1 : line_done ? 4 : line_buffered ? 5 : line_draining ? 6 : 2));
        assert(line && !(can_read || can_write || complete || read_owned || address_sent || data_sent));
        assert(line_slice < SLICES);
        if (!line_address_sent) assert(!line_buffered && !line_draining && !line_done && !line_last_seen && line_beat == 0);
        if (line_buffered) assert(line_address_sent && terminal == line_terminal);
        if (line_draining) assert(line_address_sent && !line_buffered && line_beat == BEATS-1);
        if (line_done) assert(line_draining && line_last_seen);
        assert(line_last_seen == (line_done || (line_buffered && line_terminal)));
        if (!line_draining && !line_done) assert(beat == line_beat);
        assert(!memory_request_ready && !axi_aw_valid && !axi_w_valid && !axi_b_ready);
        assert(request_address == line_address && request_tag == line_tag && hartId_0 == line_id);
        assert(axi_ar_valid == !line_address_sent && axi_r_ready == (line_address_sent && !line_buffered && !line_done));
        assert(memory_response_valid == (line_buffered || line_done));
        assert(fault == line_fault);
        if (axi_ar_valid) assert(axi_ar_bits_addr == line_address[PHYSICAL:0] && axi_ar_bits_id == line_id && axi_ar_bits_len == BEATS-1 && axi_ar_bits_size == BUSSIZE && axi_ar_bits_burst == 1 && !axi_ar_bits_lock && axi_ar_bits_prot == line_protection);
        if (read_fire) line_address_sent <= 1;
        if (read_reply) begin
          if (axi_r_bits_last) line_last_seen <= 1;
          if (line_draining) begin line_fault <= 1; if (axi_r_bits_last) line_done <= 1; end
          else begin
            line_block <= axi_r_bits_data; line_buffered <= 1; line_slice <= 0; line_terminal <= axi_r_bits_last;
            line_fault <= line_fault || axi_r_bits_resp != 0 || axi_r_bits_id != line_id || axi_r_bits_last != (line_beat == BEATS-1);
          end
        end
        if (memory_response_valid) begin
          assert(memory_response_bits_tag == line_tag && memory_response_bits_fault == line_fault);
          assert(memory_response_bits_last == (line_done || (line_terminal && line_slice == SLICES-1)));
          assert(memory_response_bits_data == (line_done ? 0 : line_value));
          if (memory_response_ready) begin
            if (memory_response_bits_last) line_owned <= 0;
            else if (line_slice == SLICES-1) begin
              line_buffered <= 0;
              if (line_beat == BEATS-1) line_draining <= 1;
              else line_beat <= line_beat + 1;
            end else line_slice <= line_slice + 1;
          end
        end
        if ($past(!reset && memory_response_valid && !memory_response_ready)) begin assert(memory_response_valid); assert($stable({memory_response_bits_data, memory_response_bits_fault, memory_response_bits_tag, memory_response_bits_last})); end
        cover(memory_response_valid && memory_response_ready && memory_response_bits_last && !line_fault && line_beat == BEATS-1);
        cover(line_buffered && !memory_response_ready);
        cover(line_draining && line_done && memory_response_valid && memory_response_bits_fault);
        if (BEATS > 1) cover(line_terminal && line_beat != BEATS-1 && memory_response_valid && memory_response_bits_last && memory_response_bits_fault);
      end
    end
  end
'''
        if width > 64:
            body += '  always @(posedge clock) if (!reset && line_owned && line_buffered) assert(slice == line_slice && block == line_block);\n'
        for token, value in (('BEATS', 512 // width), ('SLICES', width // 64), ('BUSSIZE', lane_bits)):
            body = body.replace(token, str(value))
    for channel, fields in (('ar', ('addr', 'id', 'len', 'size', 'burst', 'lock', 'cache', 'prot', 'qos')),
                            ('aw', ('addr', 'id', 'len', 'size', 'burst', 'lock', 'cache', 'prot', 'qos')),
                            ('w', ('data', 'strb', 'last'))):
        payload = ', '.join(f'axi_{channel}_bits_{field}' for field in fields)
        body += f'''  always @(posedge clock) if (checked_past && $past(!reset && axi_{channel}_valid && !axi_{channel}_ready)) begin
    assert(axi_{channel}_valid); assert($stable({{{payload}}}));
  end
'''
    for token, value in (('LANE', lane_bits - 1), ('PHYSICAL', parameters['physicalAddressBits'] - 1),
                         ('WIDTH', width), ('BYTES', width // 8), ('MASKPAD', width // 8 - 8), ('PAD', width - 64),
                         ('ID', max(1, (parameters['hartCount'] - 1).bit_length()))):
        body = body.replace(token, str(value))
    body = body.replace('STORED_PRIVILEGED', 'request_privileged' if parameters.get('enableUserMode') else "1'b1")
    body = body.replace('PRIVILEGED', 'memory_request_bits_privileged' if parameters.get('enableUserMode') else "1'b1")
    return ('Axi', body, 'request_atomic <= memory_request_bits_atomic;', 'request_atomic <= 0;')


def verify(rtl, directory, modules=None):
    directory.mkdir(parents=True, exist_ok=True)
    summary = directory / 'summary.json'
    summary.unlink(missing_ok=True)
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in manifest['sourceHashes'].items())
    sources = {p.name: p.read_text() for p in rtl.glob('*.sv') if 'DV' not in p.name and not p.name.startswith('ref_')}
    backend_dv = rtl / 'DitDahA1Backend_DV.sv'
    observation_sources = {backend_dv.name: backend_dv.read_text()} if backend_dv.exists() else {}
    license = '\n'.join(line.replace('#', '//', 1) for line in Path(__file__).read_text().splitlines()[:2]) + '\n'
    reports = []
    checker_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    tools = {name: subprocess.check_output(command, text=True).strip() for name, command in (
        ('yosys', ['yosys', '-V']), ('sby', ['sby', '--version']), ('z3', ['z3', '--version']))}
    proof_env = dict(os.environ, PYTHONPATH=str(Path(click.__file__).parent.parent)
                     + os.pathsep + os.environ.get('PYTHONPATH', ''))
    enabled = manifest['parameters']['pmpEntries'] != 0
    cases = protection_cases(manifest['parameters']) if enabled else (
            ('Fetch', FETCH, '& ~killed & ~cancel', '& ~cancel'),
            ('Multiply', MULTIPLY, '~busy & ~valid', '~valid'),
            ('Backend', BACKEND, '(~issuedValid | executed) & ~executePending & ~redirect_0', '(~issuedValid | executed) & ~redirect_0'))
    cases = [*cases, gpr_case(manifest['parameters']), *word_cases(manifest['parameters']), *integer_cases(manifest['parameters']), *wfi_cases(manifest['parameters']), synchronization_case(manifest['parameters']),
             arbiter_case(manifest['parameters']), memory_case(manifest['parameters']), axi_case(manifest['parameters'])]
    if 'DitDahA1Backend.sv' in sources:
        cases.append(pipeline_case(sources['DitDahA1Backend.sv'], manifest['parameters']))
    if manifest['parameters'].get('localInterruptBase') is not None:
        cases.append(local_interrupt_case(manifest['parameters']))
    if manifest['parameters'].get('iCacheBytes'):
        cases.append(instruction_cache_case(manifest['parameters']))
    if manifest['parameters'].get('dCacheBytes'):
        cases += [data_cache_case(manifest['parameters']), coherence_case(manifest['parameters'])]
    if manifest['parameters'].get('enableInterrupts'):
        cases = [*cases, *(case for case in interrupt_cases(manifest['parameters'])
                          if case[0] != 'InterruptCsr' or not manifest['parameters'].get('enableSupervisorMode'))]
    if manifest['parameters'].get('enableSupervisorMode'):
        cases += [case for case in supervisor_cases(manifest['parameters']) if case[0] != 'SupervisorFetch' or enabled]
    elif manifest['parameters'].get('enableUserMode'):
        cases += user_cases()
    if manifest['parameters'].get('virtualAddressBits') == 39:
        cases.append(translation_case(manifest['parameters']))
    if manifest['parameters'].get('iCacheBytes') and manifest['parameters']['issueWidth'] > 1:
        cases = [wide_fetch_case(manifest['parameters']) if case[0] == 'Fetch' else case for case in cases]
    assert not modules or set(modules) <= {case[0] for case in cases}, 'Unsupported proof selection'
    for name, body, before, after in cases:
        if name == 'MemoryArbiter' and not modules and (enabled or manifest['parameters']['enableInterrupts']):
            continue
        if modules and name not in modules and not (name.startswith('Pmp') and 'Pmp' in modules):
            continue
        unit = name.removeprefix('Interrupt').removeprefix('Synchronization').removeprefix('Pipeline').removeprefix('Word').removeprefix('Integer').removeprefix('Wfi').removeprefix('User').removeprefix('Supervisor').removeprefix('Wide')
        machine = 'privilege != 0' if manifest['parameters'].get('enableUserMode') else "1'b1"
        if name in ('Pmp', 'PmpDecode') and (manifest['parameters'].get('enableBurstRefill') or manifest['parameters'].get('iCacheBytes') and manifest['parameters']['issueWidth'] == 3):
            span = re.search(r'&\s+(\w+\[size\]) > base', sources['DitDahA1Pmp.sv']).group(1)
            body = body.replace('end_0', span)
        if unit == 'Fetch' and name != 'WideFetch':
            body = body.replace('PRIVILEGED', machine)
            if manifest['parameters'].get('iCacheBytes'):
                body = re.sub(r'\bcancel\b', '(cancel || invalidate)', body)
                body = re.sub(r'\bkilled\b', 'observed_killed', body)
                if name == 'Fetch':
                    original = sources['DitDahA1Fetch.sv']
                    body = body.replace('assert(response_seen ||', 'assert(memory_response_valid || response_seen ||')
                    body = body.replace('output_bits_fault && response_seen', 'output_bits_fault && (response_seen || memory_response_valid)')
                    ordinary = ' || '.join(f"(request_bits_pc >= 64'h{int(region['base']):x} && request_bits_pc <= 64'h{int(region['base']) + int(region['size']) - 4:x})" for region in manifest['parameters']['memoryRegions'] if region['executable'] and not region['device'] and int(region['size']) >= 4) or "1'b0"
                    if manifest['parameters'].get('virtualAddressBits') != 39:
                        body = body.replace('memory_request_bits_privileged == accepted_privileged', 'memory_request_bits_privileged == (' + machine + ')')
                        body = body.replace('have_request && local_denied)', 'have_request && local_denied && !observed_killed)')
                        permission = '_pmp_allowed' if enabled else "1'b1"
                        body += f'\n  always @(posedge clock) if (!reset && memory_request_valid) assert({permission} && ({ordinary}));\n'
                    if enabled:
                        body = body.replace('local_denied <= !_pmp_allowed;', f'local_denied <= !(_pmp_allowed && ({ordinary}));')
                    else:
                        body = body.replace('reg outstanding;', 'reg outstanding; reg local_denied;')
                        body = body.replace('accepted_pc <= request_bits_pc;', f'local_denied <= !({ordinary}); accepted_pc <= request_bits_pc;')
                        body = body.replace('response_seen || accepted_pc[1:0] != 0', 'response_seen || accepted_pc[1:0] != 0 || local_denied')
                    body = body.replace('assume(!memory_response_valid || outstanding);', 'assert(!memory_response_valid || outstanding);')
                    body = body.replace('assume(memory_response_valid);', 'assert(memory_response_valid);').replace('assume($stable({memory_response_', 'assert($stable({memory_response_')
                    body = re.sub(r'      cover\(past_valid && \$past\(!reset && memory_request_valid && !memory_request_ready\)\n\s+&&[^;]+;', '', body)
                    body = re.sub(r'      cover\(observed_killed && outstanding && memory_response_valid && memory_response_ready && memory_response_bits_fault\);', '', body)
                    bindings = {}
                    for token in set(re.findall(r'\bmemory_(?:request|response)(?:_bits_\w+|_valid|_ready)\b', body)):
                        port = token.replace('memory_', 'upstream_', 1)
                        connection = re.findall(rf'\.{port}\s*\(([^()]*)\)', original)
                        assert len(connection) == 1, (port, connection)
                        bindings[token] = "1'b1" if 'unused' in connection[0] else connection[0]
                    body = re.sub(r'\bmemory_(?:request|response)(?:_bits_\w+|_valid|_ready)\b', lambda match: '(' + bindings[match[0]] + ')', body)
                    body += FETCH_PHYSICAL
        if unit == 'InstructionCache':
            arrays, ports = zip(*instance_ports(sources['DitDahA1InstructionCache.sv']))
            banks = 1 << (manifest['parameters']['issueWidth'] - 1).bit_length()
            assert len(arrays) == banks
            address_bits = (manifest['parameters']['iCacheBytes'] // (4 * banks) - 1).bit_length()
            for bank, port in enumerate(ports):
                for pin, width in (('R0_en', 1), ('W0_en', 1), ('R0_addr', address_bits), ('W0_addr', address_bits), ('W0_data', 32)):
                    alias = f'formal_cache_pin_{bank}_{pin}'
                    body += f'\n  wire [{width-1}:0] {alias} = FORMAL_CACHE_PIN_{bank}_{pin};\n'
                    port[pin] = alias
            body = body.replace('filling_0', 'formal_cache_filling')
            body += '\n  wire formal_cache_filling = ' + ' | '.join(f"({port['W0_en']})" for port in ports) + ';\n'
            if banks > 1:
                bits = banks.bit_length() - 1
                index_bits = (manifest['parameters']['iCacheBytes'] // 64 - 1).bit_length()
                for bank, port in enumerate(ports):
                    body += f'''  always @* if (!reset) begin
    assert(({port['R0_en']}) == (reading && (upstream_request_bits_size == {bits+2} || upstream_request_bits_address[{bits+1}:2] == {bank})));
    assert(({port['R0_addr']}) == upstream_request_bits_address[{index_bits+5}:{bits+2}]);
    assert(({port['W0_en']}) == (formal_cache_filling && word[{bits-1}:0] == {bank}));
    if ({port['W0_en']}) assert(({port['W0_addr']}) == {{cache_address[{index_bits+5}:6], word[3:{bits}]}});
    if ({port['W0_en']}) assert({port['W0_data']} == {"(state == 6 ? cache_upper : downstream_response_bits_data[31:0])" if manifest['parameters'].get('enableBurstRefill') else 'downstream_response_bits_data[31:0]'});
  end
'''
                body += f'''  reg cache_full;
  reg [{bits}:0] cache_count;
  wire [{bits}:0] cache_suffix = cache_full ? {banks} - cache_address[{bits+1}:2] : 1;
  always @(posedge clock) if (!reset) begin
    if (cache_owned) assert(wide == cache_full && count == cache_count && cache_count >= 1 && cache_count <= {banks} - cache_address[{bits+1}:2]);
    if (state == 1 && hit_0 && !cache_abort) cache_count <= cache_suffix;
    if (upstream_request_valid && upstream_request_ready) begin
      cache_full <= upstream_request_bits_size == {bits+2}; cache_count <= 1;
    end
    if (upstream_response_valid) begin
      assert(upstream_response_bits_count == ((state == 1 && hit_0 && !cache_abort) ? cache_suffix : cache_count));
      assert(upstream_response_bits_count >= 1 && upstream_response_bits_count <= {banks} - cache_address[{bits+1}:2]);
    end
    if ($past(!reset && upstream_response_valid && !upstream_response_ready)) assert($stable(upstream_response_bits_count));
    cover(upstream_response_valid && upstream_response_bits_count == {banks});
    cover(upstream_response_valid && upstream_response_bits_count == 1 && cache_full && cache_sent);
  end
'''
        if unit == 'InstructionCache' and manifest['parameters'].get('enableBurstRefill'):
            write = ports[0]['W0_data']
            body += f'\n  wire [31:0] formal_cache_write_data = {write};\n'
        if unit in ('Lsu', 'InstructionCache'):
            request = 'input' if unit == 'Lsu' else 'upstream_request'
            output = 'memory_request' if unit == 'Lsu' else 'downstream_request'
            if manifest['parameters'].get('enableUserMode'):
                expected = machine if unit == 'Lsu' else 'upstream_request_bits_privileged'
                body += f'''\n  reg access_privileged;
  always @(posedge clock) if (!reset) begin
    if ({request}_valid && {request}_ready) access_privileged <= {expected};
    if ({output}_valid) assert({output}_bits_privileged == access_privileged);
  end
'''
                if unit == 'InstructionCache':
                    body += '  always @(posedge clock) if (!reset && state != 0) assert(privileged == access_privileged);\n'
            else:
                body += f'  always @(posedge clock) if (!reset && {output}_valid) assert({output}_bits_privileged);\n'
        if unit == 'Gpr':
            registers = dict(re.findall(r"if \(we_0 & waddr_0 == 5'h([0-9A-Fa-f]+)\)\s+(\w+) <= wdata_0;", sources['DitDahA1Gpr.sv']))
            registers['1f'] = re.search(r'if \(we_0 & \(&waddr_0\)\)\s+(\w+) <= wdata_0;', sources['DitDahA1Gpr.sv']).group(1)
            assert {int(address, 16) for address in registers} == set(range(1, 32))
            bindings = {int(address, 16): value for address, value in registers.items()}
            body = re.sub(r'FORMAL_GPR_REGISTER_(\d+)', lambda match: bindings[int(match[1])], body)
        if unit == 'Csr':
            machine = 'privilege == 3 && ' if manifest['parameters'].get('enableUserMode') else ''
            body += f"\n  always @* if ({machine}readAddress == 12'hf14) assert(legal && readData == {{60'd0, hartId}});\n"
            for address in (0x306, 0x30a, 0xf15):
                legal = 'privilege == 3' if manifest['parameters'].get('enableUserMode') else str(int(address == 0xf15))
                body += f"  always @* if (!reset && readAddress == 12'h{address:x}) assert(legal == ({legal}) && readData == 0);\n"
            if manifest['parameters'].get('enableUserMode') and not manifest['parameters'].get('enableSupervisorMode'):
                body += '\n  always @* begin assume(!mret || privilege == 3); assume(!write || privilege == 3); end\n'
            if not manifest['parameters'].get('enableSupervisorMode'):
                body += '\n  always @* assume(!sret);\n'
        module = 'DitDahA1' + ('Pmp' if name == 'PmpDecode' else unit)
        if name == 'PmpInterval':
            module = 'formal_interval'
            files = {module + '.sv': license + 'module formal_interval(input [64:0] low, high, input [63:0] address, input [2:0] size);\nendmodule\n'}
        else:
            files = dict(sources) if unit in ('Backend', 'Frontend', 'InstructionCache', 'DataCache') or unit == 'Fetch' and manifest['parameters'].get('iCacheBytes') else {module + '.sv': sources[module + '.sv']}
        if unit == 'Backend':
            body = backend_names(body, sources[module + '.sv'])
            if name == 'InterruptBackend':
                next_pc = 'commit_output_bits_nextPc_layerCapture'
                for lane in range(1, manifest['parameters']['issueWidth']):
                    next_pc = f'(commitCount == {lane+1} ? commitPackets_{lane}_nextPc : {next_pc})'
                body = body.replace('$past(commit_output_bits_nextPc_layerCapture)', '$past(' + next_pc + ')')
            if name == 'PipelineBackend' and observation_sources:
                observation = observation_sources[backend_dv.name].split('();', 1)[1].rsplit('endmodule', 1)[0]
                observation = observation.replace('DitDahA1Backend.', '')
                files[module + '.sv'] = files[module + '.sv'].replace('endmodule', observation + '\nendmodule', 1)
        if name == 'WfiFrontend':
            files['DitDahA1Fetch.sv'] = license + frontend_fetch_model(sources['DitDahA1Fetch.sv'], manifest['parameters'])
            files[module + '.sv'], count = re.subn(r'(DitDahA1Fetch\s+\w+\s*\()', r'\1\n.formal_pending(formal_fetch_pending), .formal_count(formal_fetch_count), .formal_pc(formal_fetch_pc),', files[module + '.sv'])
            assert count == 1
        if name == 'WideFetch':
            cache = files['DitDahA1InstructionCache.sv'].replace(');', ', output formal_owned, formal_cancelled, formal_physical_owned, formal_physical_line, output [63:0] formal_address, output [2:0] formal_count\n);', 1)
            bus_owned = 'state == 4 || (state == 6 && !terminal)' if manifest['parameters'].get('enableBurstRefill') else 'state == 4'
            bus_line = '!bypass' if manifest['parameters'].get('enableBurstRefill') else "1'b0"
            files['DitDahA1InstructionCache.sv'] = cache.replace('endmodule', f'assign formal_address = address;\nassign formal_count = count;\nassign formal_owned = state != 0;\nassign formal_cancelled = killed;\nassign formal_physical_owned = {bus_owned};\nassign formal_physical_line = {bus_line};\nendmodule', 1)
            observed, count = re.subn(r'(DitDahA1InstructionCache\s+\w+\s*\()',
                r'\1\n.formal_address(formal_fetch_cache_address), .formal_count(formal_fetch_cache_count), .formal_owned(formal_fetch_cache_owned), .formal_cancelled(formal_fetch_cache_cancelled), .formal_physical_owned(formal_fetch_physical_owned), .formal_physical_line(formal_fetch_physical_line),', files[module + '.sv'])
            assert count == 1
            files[module + '.sv'] = observed
        if unit in ('InstructionCache', 'Frontend', 'DataCache') or unit == 'Fetch' and manifest['parameters'].get('iCacheBytes'):
            for filename in files:
                match = re.fullmatch(r'(?:instructions|tags|data|dataTags|mem)_\d+x(\d+)\.sv', filename)
                if match:
                    files[filename] = license + header(sources[filename]) + f'\n(* anyseq *) reg [{int(match[1])-1}:0] arbitrary_read;\nassign R0_data = arbitrary_read;\nendmodule\n'
        if enabled and unit in ('Fetch', 'Lsu', 'Backend', 'Frontend'):
            files['DitDahA1Pmp.sv'] = license + header(sources['DitDahA1Pmp.sv']) + '\n(* anyseq *) reg permit;\nassign allowed = permit;\nendmodule\n'
            if name == 'SupervisorFetch':
                pattern = r'\.privilege\s*\(([^()]*)\)'
                connections = re.findall(pattern, files[module + '.sv'])
                assert len(connections) == 1, connections
                files[module + '.sv'] = re.sub(pattern, '.privilege(formal_fetch_mode)', files[module + '.sv'])
                body += f'\n  wire [1:0] formal_fetch_mode = ({connections[0]});\n'
                if manifest['parameters'].get('iCacheBytes'):
                    connections = [re.findall(rf'\.{port}\s*\(([^()]*)\)', files[module + '.sv']) for port in
                                   ('upstream_request_valid', 'upstream_request_bits_privileged')]
                    assert all(len(port) == 1 for port in connections), connections
                    request_valid, request_privileged = (port[0] for port in connections)
                else:
                    request_valid, request_privileged = 'memory_request_valid', 'memory_request_bits_privileged'
                body += f'  wire formal_fetch_request_valid = {request_valid};\n  wire formal_fetch_privileged = {request_privileged};\n'
            if unit == 'Lsu':
                for port, width, expected in (('address', 64, 'input_bits_address'), ('size', 3, 'input_bits_memorySize'),
                                              ('write', 1, 'input_bits_store'), ('fetch', 1, "1'b0"),
                                              ('atomic', 1, 'input_bits_load && input_bits_store'), ('privilege', 2, 'privilege')):
                    pattern = rf'\.{port}\s*\(([^()]*)\)'
                    observed = files[module + '.sv']
                    connections = re.findall(pattern, observed)
                    assert len(connections) == 1, (port, connections)
                    files[module + '.sv'] = re.sub(pattern, f'.{port}(formal_pmp_{port})', observed)
                    body += f'\n  wire [{width-1}:0] formal_pmp_{port} = {connections[0]};\n  always @* if (!reset && input_valid && input_ready) assert(formal_pmp_{port} == ({expected}));\n'
        if enabled and unit == 'Translation':
            files['DitDahA1Pmp.sv'] = license + header(sources['DitDahA1Pmp.sv']) + '\n(* anyseq *) reg permit;\nassign allowed = permit;\nendmodule\n'
            for port, width, expected in (('address', 64, 'walk_address'), ('size', 3, "3'd3"), ('write', 1, "1'b0"),
                                          ('fetch', 1, "1'b0"), ('atomic', 1, "1'b0"), ('privilege', 2, "2'd1")):
                pattern = rf'\.{port}\s*\(([^()]*)\)'
                connections = re.findall(pattern, files[module + '.sv'])
                assert len(connections) == 1, (port, connections)
                files[module + '.sv'] = re.sub(pattern, f'.{port}(formal_pmp_{port})', files[module + '.sv'])
                body += f'\n  wire [{width-1}:0] formal_pmp_{port} = {connections[0]};\n  always @(posedge clock) if (!reset && memory_request_valid && !offered) assert($past(formal_pmp_{port} == ({expected})));\n'
        if unit in ('Backend', 'Frontend', 'Gpr', 'Multiply', 'Csr', 'MemoryArbiter', 'Memory', 'Axi', 'InstructionCache', 'DataCache', 'Coherence', 'Lsu', 'LocalInterrupts', 'Translation') or (enabled and unit not in ('Decode', 'Execute')) or unit == 'Fetch' and manifest['parameters'].get('iCacheBytes'):
            if unit == 'Backend':
                files['DitDahA1Multiply.sv'] = license + header(sources['DitDahA1Multiply.sv']) + RESOURCE + 'endmodule\n'
            if name == 'InterruptBackend':
                observed = files[module + '.sv']
                writes = [f'we_{lane}' for lane in range(manifest['parameters']['issueWidth'])]
                for port in ('trapPc', 'trapCause', 'trapValue', 'write', *writes):
                    pattern = rf'\.{port}\s*\((.*?)\)(?=\s*,|\s*\n\s*\);)'
                    connections = re.findall(pattern, observed, re.S)
                    assert len(connections) == 1, (port, connections)
                    observed = re.sub(pattern, f'.{port}(formal_{port})', observed, flags=re.S)
                    body += f'\n  wire {"[63:0] " if port.startswith("trap") else ""}formal_{port} = {connections[0]};\n'
                body += '  wire formal_we = ' + ' | '.join('formal_' + name for name in writes) + ';\n'
                files[module + '.sv'] = observed
            files[module + '.sv'] = files[module + '.sv'].replace('endmodule', body + '\nendmodule', 1)
            top = module
        else:
            top = 'formal_top'
            files['wrapper.sv'] = license + header(files[module + '.sv']).replace(module, top, 1) + f'\n  {module} dut (.*);\n' + body + 'endmodule\n'
        if unit == 'Gpr':
            before = re.search(r'assign rdata1_0\s*=[^;]+;', sources[module + '.sv']).group()
            after = "assign rdata1_0 = 64'h0;"
        if name == 'Backend' and enabled:
            before = re.search(r"_commit_output_bits_csrWrite\s*&\s*\([^()]*12'h3F0\)", sources[module + '.sv']).group()
            after = "1'h0"
        elif name == 'Backend':
            before = re.search(r'wire\s+available\s*=[^;]+;', sources[module + '.sv']).group()
            after = before.replace(' & ~executePending', '')
            assert before != after
        if name == 'PmpDecode':
            before = re.search(r"mask = (\w+) \^ \1 \+ 62'h1;", sources[module + '.sv']).group()
            after = before.replace("62'h1", "62'h3")
        if name in ('Fetch', 'WideFetch') and manifest['parameters'].get('iCacheBytes'):
            assignments = re.findall(r'(?:assign|wire)\s+output_valid(?:_\d+)?\s*=\s*[^;]+;', sources[module + '.sv'])
            matches = [assignment for assignment in assignments if '~flush' in assignment or '~cancel' in assignment]
            assert len(matches) == 1, matches
            before = matches[0]
            after = before.replace('~flush', "1'h1").replace('~cancel', "1'h1")
            assert before != after, before
        if unit == 'InstructionCache' and not manifest['parameters'].get('enableBurstRefill'):
            before = re.search(r': ~\w+ \| abort \| responseFault \| bypass \| ~complete', sources[module + '.sv']).group()
            after = before.replace(' | abort', '')
        checks = [('prove', before, after), ('cover', before, after), ('mutation', before, after)]
        if unit == 'Gpr':
            lane = manifest['parameters']['issueWidth'] - 1
            write = re.search(rf"if \(we_{lane} & waddr_{lane} == 5'h1\)", sources[module + '.sv']).group()
            checks += [('mutation-write', write, "if (1'h0)")]
        if name == 'PipelineBackend':
            bindings = re.findall(r'\.rdata1\s*\([^()]*\)', sources[module + '.sv'])
            assert len(bindings) == manifest['parameters']['issueWidth'], bindings
            checks += [('mutation-forward', bindings[-1], f'.rdata1(_gpr_rdata1_{len(bindings)-1})')]
            if manifest['parameters']['issueWidth'] > 1:
                prefix = re.search(r'wire\s+prefix_1\s*=[^;]+;', sources[module + '.sv']).group()
                assert 'decodedPackets_0_writesRd' in prefix
                checks += [('mutation-dependency', prefix, prefix.replace('decodedPackets_0_writesRd', "1'h0"))]
        if name == 'WfiFrontend':
            original = sources[module + '.sv']
            output = re.search(r'assign output_valid\s*=\s*([^;]+);', original)
            credit = re.search(r'wire\s+fetch_request_valid\s*=[^;]+;', original).group()
            no_credit, count = re.subn(r'&\s*\{[^;]*<[^;]*;', ';', credit)
            assert count == 1
            checks += [('mutation-buffer-stage', output[0], 'assign output_valid = (queued != 0) & (' + output[1] + ');'),
                       ('mutation-credit', credit, no_credit),
                       ('mutation-order', 'buffer_0_instruction <=', "buffer_0_instruction <= 32'h0 &")]
            if manifest['parameters'].get('iCacheBytes'):
                checks += [('mutation-restart', 'pc <= buffer_0_pc;', 'pc <= pendingPc;')]
            if manifest['parameters'].get('iCacheBytes') and manifest['parameters']['issueWidth'] > 1:
                repair = re.search(r'pc <= _fetch_output_bits_pc[^;]+;', original).group()
                checks += [('mutation-short-return', repair, 'pc <= pc;')]
        if name in ('Fetch', 'WideFetch') and manifest['parameters'].get('iCacheBytes'):
            checks += [('mutation-invalidate', before, before.replace('~flush', '~cancel'))]
            if manifest['parameters'].get('virtualAddressBits') != 39:
                permission = 'demandPermitted' if '& demandPermitted' in sources[module + '.sv'] else 'ordinaryDemand'
                checks += [('mutation-permission', '& ' + permission, '')]
        if name == 'WideFetch':
            original = sources[module + '.sv']
            if manifest['parameters'].get('virtualAddressBits') != 39:
                barrier = re.search(r'& ~\(output_valid\w* & [^;]+\);', original).group()
                checks += [('mutation-short-return', barrier, ';')]
            fallback = re.search(r'wire\s+\w+ = rechecking & ~\w+;', original).group()
            checks += [('mutation-fallback-permission', fallback, re.sub(r'~\w+', "1'h0", fallback))]
            if enabled:
                pmp_ports = instance_ports(original, 'DitDahA1Pmp')[0][0]
                size = re.search(r'\.size\s*\(.*?\)(?=\s*,)', pmp_ports, re.S).group()
                checks += [('mutation-fetch-size', size, ".size (3'h2)")]
        if name == 'WfiBackend' and not manifest['parameters'].get('enableInterrupts'):
            checks[2] = ('mutation', before, "assign status_sleep = 1'h1 |")
        if name == 'WordDecode':
            assignment = re.search(r'assign output_bits_usesRs2\s*=\s*[^;]+;', sources[module + '.sv']).group()
            checks[2] = ('mutation', assignment, 'assign output_bits_usesRs2 = 0;')
        if name in ('IntegerDecode', 'IntegerExecute'):
            field = 'usesRs1' if unit == 'Decode' else 'csrData'
            assignment = re.search(rf'assign output_bits_{field}\s*=\s*[^;]+;', sources[module + '.sv']).group(0)
            checks[2] = ('mutation', assignment, f'assign output_bits_{field} = 0;')
            checks += [('mutation-wfi', "input_bits_instruction == 32'h10500073", "input_bits_instruction[31:20] == 12'h105")] if unit == 'Decode' else [
                ('mutation-wfi', re.search(r'assign output_bits_wfi\s*=\s*[^;]+;', sources[module + '.sv']).group(), 'assign output_bits_wfi = 0;')]
            if unit == 'Decode':
                checks += [('mutation-atomic-width', "input_bits_instruction[14:12] == 3'h3", "input_bits_instruction[14:13] == 2'h1"),
                           ('mutation-lr-source', "input_bits_instruction[24:20] == 5'h0", "1'h1"),
                           ('mutation-atomic-operation', "input_bits_instruction[31:27] == 5'h8", "1'h1")]
            else:
                atomic_assignment = re.search(r'assign output_bits_atomic\s*=\s*[^;]+;', sources[module + '.sv']).group()
                checks += [('mutation-atomic', atomic_assignment, 'assign output_bits_atomic = 0;')]
        if name == 'IntegerExecute':
            value = re.search(r'assign output_bits_value\s*=\s*[^;]+;', sources[module + '.sv']).group(0)
            branch = re.search(r'assign output_bits_nextPc\s*=\s*[^;]+;', sources[module + '.sv']).group(0)
            checks += [('mutation-word', value, 'assign output_bits_value = (' + value.split('=', 1)[1].strip()[:-1] + ") & 64'hffffffff;"),
                       ('mutation-shift', value, 'assign output_bits_value = input_bits_operand1 << input_bits_decoded_immediate[4:0];'),
                       ('mutation-branch', branch, 'assign output_bits_nextPc = input_bits_decoded_instruction_pc + input_bits_decoded_instruction_length;')]
        if name == 'UserCsr':
            checks += [('mutation-data', 'assign dataPrivilege =', 'assign dataPrivilege = 3 |')]
        if name == 'SupervisorCsr':
            checks += [('mutation-data', 'assign dataPrivilege =', 'assign dataPrivilege = 3 |'),
                       ('mutation-return', 'assign returnPc = sret ? sepc : mepc;', 'assign returnPc = mepc;'),
                       ('mutation-supervisor-bank', 'scause <= trapCause;', "scause <= 64'h0;")]
            if manifest['parameters'].get('virtualAddressBits') == 39:
                checks += [('mutation-satp', 'assign translationState_satp = satp;', "assign translationState_satp = 64'h0;"),
                           ('mutation-sum', 'assign translationState_sum = status[18];', 'assign translationState_sum = status[19];'),
                           ('mutation-tvm', 'assign sfenceLegal =', "assign sfenceLegal = 1'h1 |"),
                           ('mutation-satp-mode', "writeData[63:60] == 4'h8", "writeData[63:60] != 4'h0"),
                           ('mutation-satp-asid', "satp <= {20'h80000, writeData[43:0]};", "satp <= {4'h8, writeData[59:0]};")]
                if manifest['parameters']['physicalAddressBits'] != 56:
                    root = re.search(r"writeData\[43:\d+\] == \d+'h0", sources[module + '.sv']).group()
                    checks += [('mutation-satp-root', root, "1'h1")]
        if unit == 'Translation':
            original = sources[module + '.sv']
            dirty = re.search(r'\|\s+request_write\s*&\s*~\(memory_response_bits_data\[7\]\)', original).group()
            checks += [('mutation-tag', '|{memory_response_bits_fault, memory_response_bits_tag}', 'memory_response_bits_fault'),
                       ('mutation-cancel', 'killed | cancelInstruction & ~owner', 'killed'),
                       ('mutation-dirty', dirty, ''),
                       ('mutation-alias', '{memory_response_bits_data[53:10], request_address[11:0]}',
                        "{24'h0, memory_response_bits_data[29:10], request_address[11:0]}"),
                       ('mutation-hold', 'assign memory_request_valid = memory_request_valid_0;',
                        'assign memory_request_valid = memory_request_valid_0 & ~cancelInstruction;'),
                       ('mutation-priority', 'next <= ~owner;', "next <= 1'h0;")]
            if enabled:
                checks += [('mutation-permission', re.search(r'&\s+_pmp_allowed', original).group(), "& 1'h1"),
                           ('mutation-privilege', "wire [1:0] formal_pmp_privilege = 2'h1;", "wire [1:0] formal_pmp_privilege = 2'h3;")]
            if manifest['parameters'].get('tlbEntries'):
                invalidate = re.search(r'(if \(invalidate\)(?: begin)?\s+)tlbValid <= [^;]+;', original)
                denied = re.search(r'wire\s+leafDenied\s*=\s*[^;]+;', original).group()
                checks += [('mutation-tlb-flush', invalidate.group(), invalidate[1] + 'tlbValid <= tlbValid;'),
                           ('mutation-tlb-refill', 'refillAllowed & ~invalidate', "1'h1"),
                           ('mutation-tlb-permission', denied, "wire leafDenied = 1'h0;"),
                           ('mutation-tlb-ppn', 'tlb_0_pte <= memory_response_bits_data;', "tlb_0_pte <= memory_response_bits_data & 64'hffffffff;"),
                           ('mutation-tlb-page', 'tlb_0_level <= level;', "tlb_0_level <= 2'h0;")]
        if name == 'UserExecute':
            checks += [('mutation-return', 'assign output_bits_instruction_fault =', 'assign output_bits_instruction_fault = 0 &')]
        if name == 'SupervisorExecute':
            checks += [('mutation-return', 'assign output_bits_instruction_fault =', 'assign output_bits_instruction_fault = 0 &')]
        if name == 'InterruptBackend':
            checks += [('mutation-pc', '? resumePc', "? 64'h0"),
                       ('mutation-write', 'formal_write =', 'formal_write = takeInterrupt_layerCapture |')]
        if name == 'InterruptCsr':
            pending = re.search(r'assign interruptPending\s*=\s*[^;]+;', sources[module + '.sv']).group()
            checks[2] = ('mutation', pending, 'assign interruptPending = wakeup;')
            checks += [('mutation-wakeup', 'assign wakeup =', 'assign wakeup = status[3] &')]
        if name == 'WfiBackend':
            redirect = '| enterWfi;' if manifest['parameters'].get('enableInterrupts') else re.search(
                r'\|\s*_commit_output_valid\s*&\s*_commit_output_bits_wfi\s*&\s*~commit_output_bits_instruction_fault_layerCapture;',
                sources[module + '.sv']).group()
            checks += [('mutation-fault', '~input_bits_instruction_fault & input_bits_wfi', 'input_bits_wfi', 'DitDahA1Commit.sv'),
                       ('mutation-redirect', redirect, ';')]
            if manifest['parameters'].get('enableInterrupts'):
                checks += [('mutation-priority', 'sleep <= (sleep | enterWfi) & ~_csr_wakeup & ~status_trap_0;',
                            'sleep <= (sleep & ~_csr_wakeup | enterWfi) & ~status_trap_0;')]
        if unit == 'MemoryArbiter':
            advance = re.findall(r'next <= [^;]+;', sources[module + '.sv'])[-1]
            ready = re.search(r'assign downstream_response_ready = (\w+);', sources[module + '.sv']).group(1)
            checks += [('mutation-release', 'downstream_response_valid & ' + ready, 'downstream_response_valid'),
                       ('mutation-terminal', ' & downstream_response_bits_last', ''),
                       ('mutation-priority', advance, "next <= '0;")]
            if manifest['parameters']['hartCount'] > 1:
                checks += [('mutation-identity', 'assign hartId =', "assign hartId = 4'h0 &")]
        if unit == 'Memory' and any(region['atomic'] for region in manifest['parameters']['memoryRegions']):
            shape = re.search(r'wire\s+atomicShape\w*\s*=\s*[^;]*upstream_request_bits_atomicOperation[^;]+;', sources[module + '.sv']).group()
            checks += [('mutation-shape', shape, shape.split('=', 1)[0] + "= 1'h1;")]
        if unit == 'Memory':
            original = sources[module + '.sv']
            terminal = re.search(r'& upstream_response_bits_last\w*', original).group()
            checks += [('mutation-terminal', terminal, '')]
        if name == 'PmpDecode' and manifest['parameters'].get('enableBurstRefill'):
            checks += [('mutation-line-range', "65'h40", "65'h8")]
        if name == 'PmpDecode' and manifest['parameters'].get('iCacheBytes') and manifest['parameters']['issueWidth'] == 3:
            checks += [('mutation-fetch-range', "+ 65'h10}", "+ 65'h8}")]
        if unit == 'Axi':
            original = sources[module + '.sv']
            retry_state = re.findall(r"state <= \w+ \? 3'h1 : 3'h4;", original)[0]
            read_fault = re.search(r'amo & ~\w+', original).group()
            response_data = re.search(r'assign memory_response_bits_data\s*=\s*([^;]+);', original).group()
            checks[2] = ('mutation', 'request_atomic <= memory_request_bits_atomic;', 'request_atomic <= 0;')
            read_update = re.search(r'if \((\w+)\)\n\s+data <=', original).group(0)
            checks += [('mutation-retry', retry_state, "state <= 3'h4;"),
                       ('mutation-stale', read_update, read_update.replace(')', ' && !retried)', 1)),
                       ('mutation-read-error', read_fault, 'amo'),
                       ('mutation-write-error', "axi_b_bits_resp == 2'h0", "axi_b_bits_resp != 2'h1"),
                       ('mutation-old-value', response_data, response_data.replace('=', '= request_atomic ? data + request_data :', 1)),
                       ('mutation-or', "request_atomicOperation == 5'h8", "1'h0"),
                       ('mutation-swap', "request_atomicOperation == 5'h1", "1'h0"),
                       ('mutation-lr-write', read_fault, read_fault.replace('amo', 'request_atomic', 1)),
                       ('mutation-sc-empty', 'inputSc & ~memory_request_bits_scEligible', "1'h0")]
            if manifest['parameters'].get('enableUserMode'):
                checks += [('mutation-privilege', 'assign axi_ar_bits_prot =', "assign axi_ar_bits_prot = 3'h1 |")]
            retry = re.search(r'wire\s+(\w+)\s*=\s*amo\s*&\s*[^;]*axi_b_bits_id[^;]+;', original).group()
            status = re.search(r'else\s+data <= \{63\x27h0, (\w+)\};', original).group()
            checks += [('mutation-sc-retry', retry, retry.replace('amo', '(amo | sc)', 1)),
                       ('mutation-sc-status', status, status.replace("{63'h0, ", "{63'h0, ~"))]
            if manifest['parameters']['hartCount'] > 1:
                checks += [('mutation-read-identity', re.search(r'assign axi_ar_bits_id\s*=\s*[^;]+;', original).group(),
                            f"assign axi_ar_bits_id = hartId[{max(1, (manifest['parameters']['hartCount'] - 1).bit_length())-1}:0];"),
                           ('mutation-write-identity', 'assign axi_aw_bits_id =', "assign axi_aw_bits_id = 1'h0 &")]
        if unit == 'Axi' and manifest['parameters'].get('enableBurstRefill'):
            last = re.search(r'assign memory_response_bits_last\s*=\s*[^;]+;', original).group()
            checks += [('mutation-line-last', last, 'assign memory_response_bits_last = 1;'),
                       ('mutation-line-data', response_data, response_data.replace('=', '= line ? 0 :', 1))]
            if manifest['parameters']['axiDataBits'] > 64:
                step = re.search(r"slice <= slice \+ \d+'h1;", original).group()
                checks += [('mutation-line-order', step, step.replace("'h1", "'h0"))]
        if name == 'Pmp':
            checks += [('mutation-atomic-read', 'state_config[0] & state_config[1]', 'state_config[1]'),
                       ('mutation-atomic-write', 'state_config[0] & state_config[1]', 'state_config[0]')]
        if unit == 'Lsu':
            mask_assignment = re.search(r'assign memory_request_bits_mask\s*=\s*[^;]+;', sources[module + '.sv']).group(0)
            checks += [('mutation-mask', mask_assignment,
                        "assign memory_request_bits_mask = 8'hff;"),
                       ('mutation-extension', 'assign output_bits_value = packet_value;',
                        "assign output_bits_value = {32'd0, packet_value[31:0]};")]
            if enabled:
                checks += [('mutation-permission', '~_pmp_allowed', "1'h0")]
                checks += [('mutation-pmp-direction', 'wire [0:0] formal_pmp_atomic =', "wire [0:0] formal_pmp_atomic = 1'h0 &")]
            original = sources[module + '.sv']
            update = re.search(r'reserved <= (\w+) \| ~\([^;]+;', original).group()
            pair = re.search(r'scEligible <=[^;]+;', original).group()
            success = re.search(r'wire\s+(\w+)\s*=\s*[^;]*packet_atomic[^;]*~memory_response_bits_fault[^;]+;', original).group()
            checks += [('mutation-consume', update, re.sub(r'~\([^;]+?\) & reserved', 'reserved', update)),
                       ('mutation-pair', pair, "scEligible <= 1'h0;"),
                       ('mutation-alias', pair, f"scEligible <= input_bits_atomic & input_bits_instruction_instruction[31:27] == 3 & reserved & input_bits_address[{manifest['parameters']['physicalAddressBits']-1}:3] == reservedWord & input_bits_memorySize == 3;"),
                       ('mutation-lr-fault', success, success.replace('~memory_response_bits_fault', "1'h1"))]
        if name == 'WordExecute':
            checks += [('mutation-size', 'assign output_bits_memorySize =',
                        "assign output_bits_memorySize = 3'h3 |")]
        if unit == 'LocalInterrupts':
            checks += [('mutation-tag', 'assign memory_response_bits_tag = response_tag;',
                        "assign memory_response_bits_tag = 8'h0;"),
                       ('mutation-software', 'assign interrupts_0_software =',
                        "assign interrupts_0_software = 1'h0 &"),
                       ('mutation-compare', 'assign interrupts_0_timer = time_0 >= compare;',
                        'assign interrupts_0_timer = time_0[31:0] >= compare[31:0];'),
                       ('mutation-tick', "time_0 <= time_0 + 64'h1;", 'time_0 <= time_0;'),
                       ('mutation-priority', 'if (write & timeAccess)', 'if (write & timeAccess & ~timeTick)'),
                       ('mutation-warl', 'software <= memory_request_bits_data[0];',
                        'software <= memory_request_bits_data[1];'),
                       ('mutation-accept', 'accepted & permitted & memory_request_bits_write',
                        'permitted & memory_request_bits_write')]
            if manifest['parameters']['hartCount'] > 1:
                checks += [('mutation-isolation', 'if (write & softwareAccess_0)',
                            'if (write & softwareAccess)')]
        if name == 'SynchronizationBackend':
            advance = re.search(r'wire\s+memoryAdvance\w*\s*=[^;]*~memoryCompletion[^;]+;', sources[module + '.sv']).group()
            checks += [('mutation-serialization', 'assign output_bits_serializing =',
                        "assign output_bits_serializing = 1'h0 &", 'DitDahA1Decode.sv'),
                       ('mutation-flag', 'assign output_bits_fenceI =',
                        "assign output_bits_fenceI = 1'h0 &", 'DitDahA1Execute.sv'),
                       ('mutation-fault', '~input_bits_instruction_fault & input_bits_fenceI',
                        'input_bits_fenceI', 'DitDahA1Commit.sv'),
                       ('mutation-order', advance, advance.replace('~memoryCompletion', "1'h1"))]
        if unit == 'InstructionCache' and not manifest['parameters'].get('enableBurstRefill'):
            checks += [('mutation-hold', 'assign downstream_request_valid = downstream_request_valid_0;',
                        'assign downstream_request_valid = downstream_request_valid_0 & ~cancel;'),
                       ('mutation-word', "word <= word + 4'h1;", "word <= word + 4'h2;"),
                       ('mutation-invalidate', 'invalidate\n          ?', "1'h0\n          ?"),
                       ('mutation-denied', 'else if (allowed)', 'else if (1)')]
        if unit == 'InstructionCache' and manifest['parameters'].get('enableBurstRefill'):
            original = sources[module + '.sv']
            step = re.search(r"if \(filling & ~\w+\)\n\s+word <= word \+ 4'h1;", original).group()
            checks += [('mutation-hold', 'assign downstream_request_valid = downstream_request_valid_0;', 'assign downstream_request_valid = downstream_request_valid_0 & ~cancel;'),
                       ('mutation-word', step, step.replace("4'h1", "4'h2")),
                       ('mutation-invalidate', 'invalidate\n          ?', "1'h0\n          ?"),
                       ('mutation-denied', 'else if (allowed)', 'else if (1)'),
                       ('mutation-line-fault', '? lineFault', "? 1'h0")]
        if unit == 'InstructionCache' and banks > 1:
            read = re.findall(r'\.R0_en\s*\(.*?\)(?=\s*,)', arrays[-1], re.S)[0]
            count = re.search(r'assign upstream_response_bits_count =[^;]+;', sources[module + '.sv']).group()
            checks += [('mutation-bank-read', read, read.replace('(', "(1'h0 & (", 1) + ')'),
                       ('mutation-count', count, 'assign upstream_response_bits_count = 1;')]
        if unit == 'DataCache':
            checks += [('mutation-hold', 'assign downstream_request_valid =',
                        'assign downstream_request_valid = ~invalidate_valid &'),
                       ('mutation-allocation', 'wire          filling_0 =', "wire          filling_0 = 1'h1 |"),
                       ('mutation-authorization', 'wire          eligible_layerCapture =', "wire          eligible_layerCapture = 1'h1 |"),
                       ('mutation-tag-lifetime', '{' + str(manifest['parameters']['dCacheBytes'] // 8) + '{sameTag}}',
                        '{' + str(manifest['parameters']['dCacheBytes'] // 8) + '{hit_0}}'),
                       ('mutation-valid-hit', 'hit[0] & hit_0', "1'h1 & hit_0")]
        if unit == 'Coherence':
            checks += [('mutation-acknowledgement', 'assign invalidate_0_valid =',
                        "assign invalidate_0_valid = 1'h0 &"),
                       ('mutation-read-acceptance', 'assign upstream_request_ready =',
                        'assign upstream_request_ready = ~upstream_request_bits_write |')]
        if name == 'PipelineBackend' and manifest['parameters']['issueWidth'] == 3:
            checks[:1] = [(f'prove-bits-{bit}', before, after) for bit in range(0, 96, 8)]
        proof_top = top
        for check in checks:
            top = proof_top
            files.pop('witness.sv', None)
            mode, before, after, *target = check
            mutated_file = target[0] if target else module + '.sv'
            mutating = mode.startswith('mutation')
            proving = mode.startswith('prove')
            witness = ({'WfiBackend': wfi_witness, 'SynchronizationBackend': synchronization_witness,
                        'InterruptBackend': interrupt_witness}.get(name) or
                       (pipeline_witness if name == 'PipelineBackend' and mode == 'cover' else None) or
                       (resource_witness if name == 'Backend' else None)) if not proving else None
            work = directory / f'{name.lower()}-{mode}'
            work.mkdir(exist_ok=True)
            for filename, text in files.items():
                if unit == 'Backend' and proving and filename == 'DitDahA1Gpr.sv':
                    text = license + header(text)
                    for lane in range(manifest['parameters']['issueWidth']):
                        for operand in (1, 2):
                            text += f'\n(* anyseq *) reg [63:0] arbitrary_{operand}_{lane};\nassign rdata{operand}_{lane} = raddr{operand}_{lane} == 0 ? 0 : arbitrary_{operand}_{lane};\n'
                    text += '\nendmodule\n'
                if mode.startswith('prove-bits-') and filename == module + '.sv':
                    declaration = '(* anyconst *) reg [6:0] pipeline_bit;'
                    assert text.count(declaration) == 1
                    text = text.replace(declaration, "(* anyconst *) reg [2:0] pipeline_offset; "
                                        f"wire [6:0] pipeline_bit = {{4'b0, pipeline_offset}} + 7'd{mode.rsplit('-', 1)[1]};")
                if name == 'PipelineBackend' and mutating and filename == module + '.sv':
                    width = manifest['parameters']['issueWidth']
                    guidance = f'''
  reg [63:0] witness_pc;
  always @(posedge clock) if (reset) witness_pc <= 64'h100;
    else if (instruction_valid && instruction_ready) witness_pc <= witness_pc + {4*width};
  always @* begin
    assume(instruction_valid && instruction_bits_count == {width});
    assume(data_request_ready && !data_response_valid);
'''
                    if manifest['parameters'].get('enableInterrupts'):
                        guidance += '    assume(!interrupts_software && !interrupts_timer && !interrupts_external);\n'
                    for lane in range(width):
                        rd = lane + 1
                        rs1 = rd if mode == 'mutation-forward' else 1 if mode == 'mutation-dependency' and lane == 1 else 0
                        word = (1 << 20) | (rs1 << 15) | (rd << 7) | 0x13
                        p = f'instruction_bits_packets_{lane}'
                        guidance += f"    assume({p}_pc == witness_pc + {4*lane} && {p}_instruction == 32'h{word:x} && {p}_length == 4 && !{p}_fault && {p}_tag == 0);\n"
                    text = text.replace('endmodule', guidance + '  end\nendmodule', 1)
                if unit == 'Translation' and mode == 'mutation-alias' and filename == module + '.sv':
                    base = int(manifest['parameters']['resetVector'])
                    guidance = f'''
  always @* begin
    assume(!ports_0_request_valid && ports_1_request_valid && ports_1_response_ready);
    assume(ports_1_request_bits_address == 64'h12345100 && ports_1_request_bits_privilege == 1);
    assume(!ports_1_request_bits_fetch && !ports_1_request_bits_write && !cancelInstruction);
    assume(state_satp == 64'h{(8 << 60) | (base >> 12):x} && !state_sum && !state_mxr);
    assume(memory_request_ready && memory_response_valid == memory_response_ready);
    assume(!memory_response_bits_fault && memory_response_bits_tag == 0 && formal_permit);
    assume(memory_response_bits_data == (walk_level == 2 ? 64'h{(((base + 4096) >> 12) << 10) | 1:x} :
      walk_level == 1 ? 64'h{(((base + 8192) >> 12) << 10) | 1:x} : 64'h400000cf));
  end
'''
                    if manifest['parameters'].get('tlbEntries'):
                        guidance += '  always @* assume(!invalidate);\n'
                    text = text.replace('endmodule', guidance + 'endmodule', 1)
                if name == 'WideFetch' and mode == 'cover':
                    base = (min(int(r['base']) for r in manifest['parameters']['memoryRegions'] if r['executable'] and not r['device'] and int(r['size']) >= 64) + 63) & ~63
                    if filename == module + '.sv':
                        guidance = f"""
  (* anyconst *) reg wide_warm;
  reg [3:0] wide_beat;
  always @(posedge clock) begin
    if (memory_request_valid && memory_request_ready) wide_beat <= 0;
    else if (memory_response_valid && memory_response_ready) wide_beat <= wide_beat + 1;
  end
  always @* if (wide_warm) begin
    assume(request_bits_pc == 64'h{base:x} && request_bits_tag == 0 && request_valid && output_ready);
    assume(!cancel && !invalidate && memory_request_ready && privilege == 3);
    assume(memory_response_valid == fetch_physical_owned && !memory_response_bits_fault && memory_response_bits_tag == 0 && memory_response_bits_data == 0);
    assume(memory_response_bits_last == (!fetch_physical_line || wide_beat == 7));
    {'assume(_pmp_allowed);' if enabled else ''}
  end
"""
                        if manifest['parameters'].get('virtualAddressBits') == 39:
                            guidance += f"  always @* if (wide_warm) begin assume(translation_request_ready && translation_response_valid == translation_owned); assume(translation_response_bits_address == 64'h{base:x} && !translation_response_bits_fault); end\n"
                        count = 1 << (manifest['parameters']['issueWidth'] - 1).bit_length()
                        text = text.replace(f'cover(output_valid && output_bits_count == {count});', f'cover(wide_warm && output_valid && output_bits_count == {count});')
                        text = text.replace('endmodule', guidance + 'endmodule', 1)
                    if re.fullmatch(r'instructions_\d+x32\.sv', filename):
                        text = text.replace('(* anyseq *) reg [31:0] arbitrary_read;', "wire [31:0] arbitrary_read = 0;")
                    if filename == 'DitDahA1InstructionCache.sv':
                        tag_shift = (manifest['parameters']['iCacheBytes'] // 64 - 1).bit_length() + 6
                        text = text.replace('endmodule', f"  always @* assume(_tags_ext_R0_data == {base >> tag_shift});\nendmodule", 1)
                if name == 'SupervisorFetch' and mutating and filename == module + '.sv':
                    text = text.replace('endmodule', "  always @* assume(privilege == (state == 0 ? 2'd1 : 2'd3));\nendmodule", 1)
                if unit == 'MemoryArbiter' and mode != 'prove' and filename == module + '.sv':
                    guidance = ''.join(f'    assume(ports_{i}_request_valid);\n' + ''.join(
                        f"    assume(ports_{i}_request_bits_{field} == 0);\n"
                        for field in ('address', 'data', 'size', 'mask', 'tag', 'write', 'fetch', 'atomic', 'atomicOperation', 'scEligible'))
                        for i in range(2 * manifest['parameters']['hartCount']))
                    guidance += f'''    assume(downstream_request_ready == (witness_age != 1));
    assume(downstream_response_valid == sent);
    assume(downstream_response_bits_last == {"1" if mode == "mutation-release" else "(witness_age >= 5)"});
    assume(consumers == (witness_age == 3 ? 0 : {2 * manifest['parameters']['hartCount']}'d{(1 << (2 * manifest['parameters']['hartCount'])) - 1}));
'''
                    text = text.replace('endmodule', '''  reg [2:0] witness_age = 0;
  always @(posedge clock) if (reset) witness_age <= 0;
  else if (witness_age != 7) witness_age <= witness_age + 1;
  always @* begin
''' + guidance + '  end\nendmodule', 1)
                if unit == 'Axi' and mutating and not mode.startswith('mutation-line-') and filename == module + '.sv':
                    width = manifest['parameters']['axiDataBits']
                    atomic_operation = {'mutation-or': 8, 'mutation-swap': 1, 'mutation-lr-write': 2,
                                        'mutation-sc-empty': 3, 'mutation-sc-retry': 3, 'mutation-sc-status': 3,
                                        'mutation-read-identity': 2, 'mutation-write-identity': 3}.get(mode, 0)
                    identity = int('identity' in mode)
                    read_code = 2 if mode == 'mutation-read-error' else 1
                    write_code = '0' if mode in ('mutation-retry', 'mutation-sc-retry', 'mutation-sc-status') else '2' if mode == 'mutation-write-error' else '(retried ? 1 : 0)' if mode == 'mutation-stale' else '1'
                    guidance = f'''
  always @* begin
    assume(memory_request_valid && memory_request_bits_atomic && memory_request_bits_write == {int(atomic_operation != 2)} && !memory_request_bits_fetch);
    assume(memory_request_bits_atomicOperation == {atomic_operation} && memory_request_bits_scEligible == {int(mode != 'mutation-sc-empty')});
    assume(hartId == {"(held ? 0 : 1)" if mode == 'mutation-read-identity' else identity});
    assume(memory_request_bits_address == 8 && memory_request_bits_data == 1 && memory_request_bits_tag == 37);
    assume(memory_request_bits_size == 3 && memory_request_bits_mask == {0 if atomic_operation == 2 else 255} && memory_response_ready);
    assume(axi_ar_ready && axi_aw_ready && axi_w_ready);
    assume(axi_r_valid == read_owned && axi_b_valid == (address_sent && data_sent));
    assume(axi_r_bits_id == {identity} && axi_r_bits_last && axi_b_bits_id == {identity});
    assume(axi_r_bits_resp == {read_code} && axi_b_bits_resp == {write_code});
    assume(axi_r_bits_data == ((retried ? {width}'d11 : {width}'d7) << {8 * (8 % (width // 8))}));
  end
'''
                    text = text.replace('endmodule', guidance + '\nendmodule', 1)
                    if mode == 'mutation-privilege':
                        text = text.replace('endmodule', '  always @* assume(!memory_request_bits_privileged);\nendmodule', 1)
                if unit == 'Axi' and mode.startswith('mutation-line-') and filename == module + '.sv':
                    width = manifest['parameters']['axiDataBits']
                    words = sum((index + 1) << (64 * index) for index in range(width // 64))
                    guidance = f'''
  always @* begin
    assume(memory_request_valid && memory_request_bits_fetch && !memory_request_bits_write && !memory_request_bits_atomic && memory_request_bits_size == 6 && memory_request_bits_address == 0);
    assume(memory_response_ready && axi_ar_ready && !axi_b_valid);
    assume(axi_r_valid == (line_owned && line_address_sent && !line_last_seen && !line_buffered));
    assume(axi_r_bits_last == (line_beat == {512 // width - 1}) && axi_r_bits_id == line_id && axi_r_bits_resp == 0);
    assume(axi_r_bits_data == {width}'h{words:x});
  end
'''
                    text = text.replace('endmodule', guidance + '\nendmodule', 1)
                if unit == 'Lsu' and mutating and filename == module + '.sv':
                    load = mode == 'mutation-extension'
                    atomic = mode in ('mutation-consume', 'mutation-pair', 'mutation-alias', 'mutation-lr-fault', 'mutation-pmp-direction')
                    guidance = f'''
  always @* begin
    assume(input_valid && !input_bits_instruction_fault && !input_bits_atomic && storeAllowed && output_ready);
    assume(input_bits_memorySize == 2 && !input_bits_unsignedLoad);
    assume(input_bits_load == {int(load)} && input_bits_store == {int(not load)});
    assume(input_bits_instruction_instruction == 32'h{0x00402283 if load else 0x00102223:x});
    assume(input_bits_address == 4 && input_bits_instruction_tag == 37);
    assume(memory_request_ready && memory_response_valid == (word_sent && !word_replied));
    assume(memory_response_bits_data == 64'h80000000 && memory_response_bits_tag == 37 && !memory_response_bits_fault);
  end
'''
                    if atomic:
                        guidance = f'''
  reg [1:0] pair_sequence = 0;
  always @(posedge clock) if (!reset && output_valid && output_ready && pair_sequence != 2) pair_sequence <= pair_sequence + 1;
  always @* begin
    assume(input_valid && !input_bits_instruction_fault && input_bits_atomic && storeAllowed && output_ready);
    assume(input_bits_memorySize == 3 && !input_bits_unsignedLoad && input_bits_value == 0);
    assume(input_bits_load == {"1" if mode == 'mutation-pmp-direction' else '(pair_sequence == 0)'} && input_bits_store == {"1" if mode == 'mutation-pmp-direction' else '(pair_sequence != 0)'});
    assume(input_bits_instruction_instruction == {"32'h0030b12f" if mode == 'mutation-pmp-direction' else "(pair_sequence == 0 ? 32'h1000b12f : 32'h1830b12f)"});
    assume(input_bits_address == {f"(pair_sequence == 1 ? 64'h{(1 << manifest['parameters']['physicalAddressBits']) + 8:x} : 64'd8)" if mode == 'mutation-alias' else "64'd8"} && input_bits_storeData == 13 && input_bits_instruction_tag == 37);
    assume(memory_request_ready && memory_response_valid == (word_sent && !word_replied));
    assume(memory_response_bits_data == 0 && memory_response_bits_tag == 37 && memory_response_bits_fault == {int(mode == 'mutation-lr-fault')});
  end
'''
                    if enabled:
                        guidance += f"  always @* assume(_pmp_allowed == {int(mode != 'mutation-permission')});\n"
                    text = text.replace('endmodule', guidance + '\nendmodule', 1)
                if name == 'IntegerExecute' and mutating and filename == module + '.sv':
                    op, instruction, immediate, first = {
                        'mutation': (28, 0x3401f2f3, 0, 0),
                        'mutation-word': (23, 0xfff0009b, (1 << 64) - 1, 0),
                        'mutation-shift': (21, 0x02009093, 32, 1),
                        'mutation-branch': (25, 0x00009463, 8, 1),
                        'mutation-wfi': (29, 0x10500073, 0, 0),
                        'mutation-atomic': (30, 0x1830b12f, 0, 8)}[mode]
                    guidance = f'''
  always @* begin
    assume(input_valid && !input_bits_decoded_instruction_fault && csrLegal);
    assume(input_bits_decoded_operation == {op} && input_bits_decoded_instruction_instruction == 32'h{instruction:x});
    assume(input_bits_decoded_instruction_pc == 0 && input_bits_decoded_instruction_length == 4);
    assume(input_bits_decoded_rs1 == {(instruction >> 15) & 31});
    assume(input_bits_decoded_immediate == 64'h{immediate:x} && input_bits_operand1 == {first} && input_bits_operand2 == 0);
    assume(csrValue == 15);
  end
'''
                    text = text.replace('endmodule', guidance + '\nendmodule', 1)
                if name == 'UserExecute' and mutating and filename == module + '.sv':
                    operation = 12 if mode == 'mutation' else 13
                    text = text.replace('endmodule', f'  always @* assume(input_valid && !input_bits_decoded_instruction_fault && input_bits_decoded_operation == {operation} && privilege == 0);\nendmodule', 1)
                if name == 'IntegerDecode' and mode in ('mutation-atomic-width', 'mutation-lr-source', 'mutation-atomic-operation') and filename == module + '.sv':
                    instruction = {'mutation-atomic-width': 0x4000a12f, 'mutation-lr-source': 0x1010b12f, 'mutation-atomic-operation': 0x2800b12f}[mode]
                    text = text.replace('endmodule', f"  always @* assume(input_valid && !input_bits_fault && input_bits_instruction == 32'h{instruction:x});\nendmodule", 1)
                if unit == 'InstructionCache' and mode != 'prove' and filename == module + '.sv':
                    scenario = {'mutation': 7, 'mutation-hold': 1, 'mutation-word': 0,
                                'mutation-invalidate': 6, 'mutation-denied': 3, 'mutation-line-fault': 4}.get(mode)
                    guidance = '''
  (* anyconst *) reg [2:0] cache_scenario;
  reg cache_waited = 0;
  always @(posedge clock) cache_waited <= !reset && cache_bus;
  always @* begin
    assume(cache_scenario <= SCENARIO_MAX);
    assume(upstream_request_valid && upstream_request_bits_address == 0 && upstream_request_bits_tag == 0);
    assume(upstream_response_ready == (cache_scenario != 1));
    assume(downstream_request_ready == (cache_scenario != 1 || killed || state != 3));
    assume(downstream_response_valid == (cache_bus && (cache_scenario != 1 || cache_waited)));
    assume(downstream_response_bits_tag == 0 && _tags_ext_R0_data == 0);
    assume(downstream_response_bits_fault == (cache_scenario == 4 || (cache_scenario == 5 && word == 1 && !bypass)));
    assume(allowed == !(cache_scenario == 3 && word == 1));
    assume(invalidate == ((cache_scenario == 2 && state == 4 && word == 15) || (cache_scenario == 6 && valid != 0)));
    assume(cancel == ((cache_scenario == 1 && (state == 3 || state == 4)) ||
      (cache_scenario == 7 && state == 4 && word == 15) || invalidate));
  end
'''
                    if manifest['parameters'].get('enableBurstRefill'):
                        guidance = guidance.replace('downstream_response_valid == (cache_bus &&', 'downstream_response_valid == (cache_bus && state == 4 &&')
                        guidance = guidance.replace('assume(allowed == !(cache_scenario == 3 && word == 1));', 'assume(allowed == (cache_scenario != 3));')
                        guidance = guidance.replace('state == 4 && word == 15', 'state == 6 && word == 15')
                        guidance += "  always @* assume(downstream_response_bits_last == (bypass || word >= 14));\n"
                    guidance = guidance.replace('SCENARIO_MAX', '4' if scenario is None else '7')
                    if scenario is not None:
                        guidance += f'  always @* assume(cache_scenario == {scenario});\n'
                    if mode == 'mutation-count':
                        guidance += f'  always @* assume(cache_scenario == 0 && upstream_request_bits_size == {banks.bit_length()+1} && upstream_request_bits_tag == 0);\n'
                    text = text.replace('endmodule', guidance + '\nendmodule', 1)
                if unit == 'DataCache' and mode == 'mutation-tag-lifetime' and filename == module + '.sv':
                    base = min(int(r['base']) for r in manifest['parameters']['memoryRegions'] if r.get('dataCacheable'))
                    base = (base + 63) & ~63
                    tag_shift = (manifest['parameters']['dCacheBytes'] // 64 - 1).bit_length() + 6
                    guidance = f'''
  reg cache_witness_second = 0;
  always @(posedge clock) if (reset) cache_witness_second <= 0;
  else if (upstream_response_valid && upstream_response_ready) cache_witness_second <= 1;
  always @* begin
    assume(upstream_request_valid && upstream_response_ready && downstream_request_ready && !invalidate_valid);
    assume(upstream_request_bits_address == (cache_witness_second ? 64'h{base+8:x} : 64'h{base:x}));
    assume(upstream_request_bits_size == 3 && upstream_request_bits_tag == 0);
    assume(!upstream_request_bits_write && !upstream_request_bits_fetch && !upstream_request_bits_atomic);
    assume(downstream_response_valid == cache_bus && !downstream_response_bits_fault && downstream_response_bits_tag == 0);
    assume(_dataTags_ext_R0_data == (state == 1 ? {base >> tag_shift} : {(base >> tag_shift) ^ 1}));
    assume(cache_watched == {(base >> 3) % (manifest['parameters']['dCacheBytes'] // 8)});
  end
'''
                    text = text.replace('endmodule', guidance + '\nendmodule', 1)
                if mutating and filename == mutated_file:
                    assert text.count(before) == (2 if name == 'Csr' else 1), (name, before)
                    text = text.replace(before, after, 1)
                if name == 'WideFetch' and filename == module + '.sv':
                    for instance, prefix in (('DitDahA1InstructionCache', 'CACHE'), ('DitDahA1Pmp', 'PMP')):
                        connected = instance_ports(text, instance)
                        if connected:
                            assert len(connected) == 1
                            for pin, expression in connected[0][1].items():
                                value = "1'b1" if 'unused' in expression else '(' + expression + ')'
                                text = re.sub(rf'\bFORMAL_FETCH_{prefix}_{pin}\b', lambda _: value, text)
                    assert 'FORMAL_FETCH_' not in text
                if unit == 'InstructionCache' and filename == module + '.sv':
                    for bank, (_, pins) in enumerate(instance_ports(text)):
                        for pin, expression in pins.items():
                            text = text.replace(f'FORMAL_CACHE_PIN_{bank}_{pin}', expression)
                    assert 'FORMAL_CACHE_PIN_' not in text
                if unit == 'Backend' and filename == module + '.sv':
                    text = re.sub(r'\binstruction_bits_(pc|tag|instruction|length|fault|cause|tval)\b',
                                  r'instruction_bits_packets_0_\1', text)
                    width = manifest['parameters']['issueWidth']
                    text = text.replace('endmodule', f'  always @* assume(!instruction_valid || (instruction_bits_count >= 1 && instruction_bits_count <= {width}));\nendmodule', 1)
                    if mode != 'prove' and name in ('Backend', 'InterruptBackend', 'SynchronizationBackend', 'WfiBackend'):
                        text = text.replace('endmodule', '  always @* assume(instruction_bits_count == 1);\nendmodule', 1)
                    if name == 'InterruptBackend' and mode != 'prove':
                        text = text.replace(');', ', output [4:0] formal_events);', 1)
                        text = text.replace('endmodule', "  assign formal_events = {(issuedCount != 0 && issuedPackets_0_decoded_instruction_instruction[6:0] == 7'h0f), takeInterrupt_layerCapture, irq_memory_owned, _multiply_output_valid, owned};\nendmodule", 1)
                (work / filename).write_text(text)
            if witness:
                files['witness.sv'] = license + witness_wrapper((work / (module + '.sv')).read_text(), *witness(manifest['parameters'], mode))
                (work / 'witness.sv').write_text(files['witness.sv'])
                top = 'formal_witness'
            task = 'bmc' if mutating else 'prove' if proving else mode
            if mode == 'mutation' and name == 'Fetch':
                task = 'prove'
            engine = 'abc pdr' if task == 'prove' and unit not in ('Gpr', 'Multiply', 'Pmp', 'PmpDecode', 'PmpInterval', 'Csr', 'Memory', 'Axi', 'InstructionCache', 'DataCache', 'Coherence', 'Decode', 'Execute', 'LocalInterrupts', 'Translation') and name not in ('SynchronizationBackend', 'WfiBackend') else 'smtbmc z3'
            if name in ('WideFetch', 'WfiFrontend', 'Gpr', 'PipelineBackend'):
                engine = 'smtbmc z3' if name == 'WideFetch' else 'smtbmc --unroll z3'
            if name in ('Gpr', 'PipelineBackend'):
                engine = 'smtbmc --syn --unroll z3'
            if unit == 'Backend' and task != 'prove':
                engine = 'smtbmc --syn --unroll z3'
            if witness:
                engine = 'smtbmc --unroll z3'
            if name in ('WfiBackend', 'SynchronizationBackend') and task == 'prove':
                engine = 'smtbmc --syn --unroll z3'
            timeout = 180 if name in ('InterruptBackend', 'SynchronizationBackend') and task == 'cover' else 60
            if name == 'InterruptBackend' and task == 'cover' and manifest['parameters']['issueWidth'] == 3:
                timeout = 600
            if name in ('InterruptBackend', 'PipelineBackend') and mutating and manifest['parameters']['issueWidth'] == 3:
                timeout = 180
            if name == 'WfiFrontend' and task == 'prove' and manifest['parameters']['issueWidth'] == 3:
                timeout = 300
            if unit == 'Backend' and task == 'prove' and manifest['parameters']['issueWidth'] > 1:
                timeout = 180
            if name == 'WideFetch' and task == 'cover' and manifest['parameters'].get('virtualAddressBits') == 39:
                timeout = 180
            if unit == 'Axi' and task == 'prove' and manifest['parameters']['axiDataBits'] == 512:
                timeout = 120
            witness_option = 'aigsmt z3\n' if engine == 'abc pdr' else ''
            preparation = (f'hierarchy -check -top {top}\nproc\nflatten\nopt_expr -keepdc\nopt_clean\nwreduce\nopt_clean\ncheck'
                           if name.startswith('Pmp') else f'prep -top {top} -flatten')
            depth = 6 * manifest['parameters']['hartCount'] + 8 if unit == 'MemoryArbiter' else 72 if task == 'cover' or (unit == 'InstructionCache' and mode in ('mutation', 'mutation-invalidate', 'mutation-count')) else 1 if name.startswith('Pmp') or unit in ('Decode', 'Execute') else (3 if task == 'prove' else 8) if unit == 'Csr' else 6 if unit in ('DataCache', 'Coherence') and task == 'prove' else 4 if name in ('Gpr', 'Multiply', 'Memory', 'Axi', 'SynchronizationBackend', 'WfiBackend', 'InstructionCache', 'LocalInterrupts') and task == 'prove' else 24
            if mode == 'mutation-buffer-stage' and manifest['parameters'].get('enableBurstRefill'):
                depth = 40
            if unit == 'Translation' and task == 'prove':
                depth = 6
            if name in ('WideFetch', 'WfiFrontend', 'PipelineBackend') and task == 'prove':
                depth = 6 if name == 'WideFetch' else 4
            if name in ('WfiBackend', 'InterruptBackend') and mutating:
                depth = 32 if name == 'WfiBackend' else 40
            config = f'''[options]
mode {task}
depth {depth}
timeout {timeout}
{witness_option}[engines]
{engine}
[script]
read -formal -sv {' '.join(files)}
{preparation}
[files]
''' + '\n'.join(files) + '\n'
            (work / 'check.sby').write_text(config)
            with (work / 'run.log').open('w') as log:
                result = subprocess.run(['sby', '-f', '-d', 'proof', 'check.sby'], cwd=work, env=proof_env, stdout=log, stderr=subprocess.STDOUT, timeout=timeout + 30)
            assert 'multiple conflicting drivers' not in (work / 'run.log').read_text(), 'Conflicting proof drivers'
            assert 'is implicitly declared' not in (work / 'run.log').read_text(), 'Undeclared proof signal'
            status_file = work / 'proof/status'
            assert status_file.exists(), (work / 'run.log').read_text()[-3000:]
            status = status_file.read_text().split()[0]
            expected = 'FAIL' if mutating else 'PASS'
            assert status == expected and result.returncode == (2 if mutating else 0), (name, mode, status, work)
            if mutating:
                assert list((work / 'proof/engine_0').glob('trace*.vcd')), 'Missing mutation counterexample'
            reports.append(dict(module=module, propertyGroup=name, mode=mode, status=status, engine=engine,
                                assertions=body.count('assert('), covers=body.count('cover(')))
            print(f'  {module} [{name}] {mode}: {status}', flush=True)
    assert all((rtl / p).read_text() == text for p, text in (sources | observation_sources).items()), 'RTL changed during proofs'
    assert checker_hash == hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'Checker changed during proofs'
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in manifest['sourceHashes'].items())
    proved = {report['propertyGroup'] for report in reports if report['mode'].startswith('prove') and report['status'] == 'PASS'}
    if 'PipelineBackend' in proved and manifest['parameters']['issueWidth'] == 3:
        assert {f'prove-bits-{bit}' for bit in range(0, 96, 8)} <= {report['mode'] for report in reports}, 'Incomplete identity proof'
    if 'Pmp' in proved:
        assert {'PmpInterval', 'PmpDecode'} <= proved, 'Missing PMP composition prerequisites'
    summary.write_text(json.dumps(dict(
        scope='module-level safety, cover reachability and mutation detection', propertyGroups=sorted(proved),
        assumptions='initial reset, then no reset except CSR proofs; Fetch responses require accepted requests and stable blocked payloads; enabled control proofs abstract combinational authorization',
        pmpComposition='Pmp uses independently proved PmpInterval identities and PmpDecode request spans; no table-value restrictions' if 'Pmp' in proved else None,
        registerFile='arbitrary nonzero architectural register and immutable data bit, exact reset and ordered multiport writes, zero-register isolation and every asynchronous read port; unrestricted addresses, data and same-address writes' if 'Gpr' in proved else None,
        backendAbstraction='arbitrary multiply result and completion delay; safety overapproximates nonzero GPR reads, with actual GPR retained for covers/mutations; resource and register contracts are separately proved',
        resourceWitnessGuidance='cover/mutations only: faulting SD or configured PMP update followed by MUL and NOP, arbitrary response delay and quiescent interrupts' if 'Backend' in proved else None,
        pipelineMutationGuidance='mutations only: consecutive PCs, constant legal ADDI groups, incrementing independent register chains for forwarding or a lane-0-to-lane-1 dependency; actual arithmetic and register storage' if 'PipelineBackend' in proved else None,
        pipelineCoverGuidance='cover only: independent ADDI groups, a leading SD with arbitrary response delay, or a lane-0-to-lane-1 RAW; actual arithmetic and register storage' if 'PipelineBackend' in proved else None,
        pipeline='independent FIFO of accepted PC/encoding bits checks every valid stage lane; W=3 partitions all 96 identity bits into eight-bit proof domains; greedy oldest prefix, youngest older writer, scalar effect ownership and every GPR write port; generated observation registers inlined; safety overapproximates nonzero GPR reads, with actual GPR retained for covers/mutations and separately proved' if 'PipelineBackend' in proved else None,
        synchronization='raw barrier encodings, independent accepted-data ownership until retirement, sequential instruction synchronization redirect and younger flush; no data response timing assumptions' if 'SynchronizationBackend' in proved else None,
        synchronizationWitnessGuidance='cover/mutations only: port-driven zero-address SD, FENCE/FENCE.I, one request and response stall, faulted FENCE.I and quiescent interrupts; unrestricted safety proof' if 'SynchronizationBackend' in proved else None,
        instructionCache='control proof at configured geometry; arbitrary native SRAM read outputs; independent ownership, authorization, response fault/tag/last history, native write data, complete publication, invalidation and precise fallback; functional array contents require separate simulation' if 'InstructionCache' in proved else None,
        dataCache='control safety with arbitrary native SRAM reads; independently captured requests, physical ownership, valid-sector/tag-qualified sampling, fault/tag attribution, index invalidation and sector publication; functional SRAM contents require separate simulation' if 'DataCache' in proved else None,
        dataCacheWitnessGuidance='tag-lifetime mutation only: two permitted sectors, successful immediate service, lookup tag match and unrelated later SRAM output; safety and cover remain unrestricted' if 'DataCache' in proved else None,
        coherence='broadcast completion before cacheable writes; held upstream request and one physical transaction supplied by the shared arbiter; no endpoint progress assumption or DMA coherence claim' if 'Coherence' in proved else None,
        cacheWitnessGuidance='cover/mutations only: zero-address demand, successful service, canceled stalls, last-beat/post-fill invalidation, permission denial and demand/speculative fault scenarios; unrestricted safety proof' if 'InstructionCache' in proved else None,
        arbitration='one retained request and owner, hart identity from independent accepted requester/2 through response; at most 2N-1 other completions while continuously requesting; no bound on external service delay' if 'MemoryArbiter' in proved else None,
        interruptProgress='with eligibility held, successful matching data response reaches interrupt entry or priority synchronous trap within three cycles; memory service itself is external' if any(r['propertyGroup'] == 'InterruptBackend' for r in reports) else None,
        witnessGuidance='InterruptBackend cover/mutations drive ADDI and mie/mstatus at clocks 0/8/16, then SD, AMOADD.D, MUL, SD-to-MUL, SD-to-FENCE.I or FENCE.I; fixed PC/tag, successful data service, request stall and read-only ownership events select interrupt timing; unrestricted safety proof' if 'InterruptBackend' in proved else None,
        arbiterWitnessGuidance='cover/mutations hold all requesters valid with zero payloads, one request stall and one response stall then immediate service; unrestricted proof' if 'MemoryArbiter' in proved else None,
        readStreaming='one accepted line and external AR; independent beat/chunk counters, buffered data ordering, response-last ownership, stalled payloads and malformed-last drain; endpoint R data, ID, status, last and delays unrestricted' if 'Axi' in proved and manifest['parameters'].get('enableBurstRefill') else None,
        cachedFetch='actual cache upstream scalar connections retain request/response ownership; external scalar responses terminate, line responses may fault or end early/late; cancel and invalidate are independent' if 'Fetch' in proved and manifest['parameters'].get('iCacheBytes') else None,
        wideFetch='actual cache connections, captured privilege and permission, full-block and scalar fallback shapes, bounded suffix count, short-return barrier, stable payload and cancellation drain; arbitrary native SRAM read outputs; translation replies require accepted requests and successful replies preserve the page offset' if 'WideFetch' in proved else None,
        frontendQueue='actual queue RTL with abstract single-owner fetch contract; arbitrary stalls, payloads, cancellation and 1-to-demand-suffix returns; independent credit history and complete reference FIFO over an arbitrary immutable packet bit proves conservation of every field through compaction, stable groups and oldest restart; concrete fetch and translation proofs are composition prerequisites' if 'WfiFrontend' in proved else None,
        wideFetchWitnessGuidance='cover only: full-count return uses aligned repeated demand, granted permission, successful immediate service, zero data and matching tag-array reads; other covers retain arbitrary requests and responses with zero native instruction reads; safety and mutations unrestricted' if 'WideFetch' in proved else None,
        atomicTransport='independent request and AXI channel ownership and retained hart identity; LR read-only, one-shot SC status/no-bus failure, ADD/OR/SWAP exclusive retry and error isolation; no external-memory atomicity or eventual-success theorem' if 'Axi' in proved else None,
        axiAssumptions='initial reset only; R requires accepted AR, B requires accepted AW and W; blocked response payloads persist; all request metadata, hart/response IDs, data, responses, last and delays unrestricted' if 'Axi' in proved else None,
        axiMutationGuidance='mutations only: aligned D ADD/OR/SWAP/LR/SC at address8, operand1, values7 then11 after retry, immediate service, per-fault codes, SC eligibility and valid hart1 with changing live sideband for retained-ID check; prove and cover unrestricted' if 'Axi' in proved else None,
        wordMemory='independent decode and execution metadata, accepted LSU ownership, size/mask, alignment, authorization, narrow extension and response fault attribution; metadata inputs unrestricted, functional completion checked for byte/halfword/word/doubleword sizes' if 'Lsu' in proved else None,
        reservation='independent last-LR physical word and validity, successful matching LR completion only, any atomic acceptance consumes old pair, full-EA SC qualification captured before protection and stable through backpressure; endpoint exclusivity is separate' if 'Lsu' in proved else None,
        physicalMemory='independent configured region/permission/shape model; D-only atomic directions/opcodes, malformed and denied SC isolation regardless of eligibility, retained local-fault response and complete request payload forwarding' if 'Memory' in proved else None,
        integerExecution='independent raw encoding validity and dependency decode, D-only atomic encodings/LR rs2 and direction metadata, integer ALU and 5/6-bit shifts, word truncation/sign extension, branches, narrow metadata and CSR semantics; combinational safety with unrestricted inputs' if 'IntegerExecute' in proved else None,
        userMode='M/U trap stack, fixed UXL64, MPP WARL, MPRV effective data access and lower-return clearing, TW legality, CSR minimum privilege and U ECALL/MRET/WFI exceptions; CSR write/mret inputs are legal retired effects' if 'UserCsr' in proved else None,
        supervisorMode='M/S/U trap target and bank isolation, shared CSR aliases, interrupt target priority, effective data mode and legal return effects; legal retired CSR/return inputs, unrestricted pending levels and trap causes' if 'SupervisorCsr' in proved else None,
        addressTranslation='independent accepted VA/access/status, PTE interpreter and physical ownership; all Sv39 page sizes, permission/reserved/A-D faults, physical read authorization, original access fault classes, cancellation drain and fair client ownership; arbitrary response data/errors/tags/delays, no service progress assumption' if 'Translation' in proved else None,
        translationProtection='PMP outcome abstracted with arbitrary permit; actual full-width address, size=8 bytes, S effective privilege and read type checked before each first offer; separate PMP proofs and simulation compose the concrete protection function' if 'Translation' in proved else None,
        translationCache='actual small register entries, complete PTE/VPN/page-size storage, independent lookup permissions and offsets, overlap eviction, local invalidation and stale-refill exclusion' if 'Translation' in proved and manifest['parameters'].get('tlbEntries') else None,
        translationMutationGuidance='alias mutant only: fixed legal S read, three page levels, immediate successful service and a high leaf PPN; prove and cover inputs remain unrestricted by this witness' if 'Translation' in proved else None,
        wfi='raw retired encoding drives independent wait/continuation model; wake priority, younger flush, no new work while waiting, frontend halt and retained requests; sleep is architectural wait, not physical idle' if 'WfiBackend' in proved else None,
        wfiWitnessGuidance='cover/mutations only: port-driven ADDI/mie/WFI/MUL at clocks 0/8/16/17, pending at 17 or 24 or fetch fault, fixed PC/tag and no data service; safety inputs unrestricted' if 'WfiBackend' in proved else None,
        wordMutationGuidance='mutations only: SW/LW at address4 or valid D LR/SC/ADD sequences at address8, high-EA SC alias, faulted LR, matching tag37, immediate memory service and permission grant except denial mutant; unrestricted prove and cover' if 'Lsu' in proved else None,
        localInterrupts='independent request-driven MSIP, MTIME and MTIMECMP model; exact register widths, WARL bit, invalid-access isolation, read snapshots, write-once side effects, tag ownership and timer comparison; timeTick unrestricted' if 'LocalInterrupts' in proved else None,
        configurations=manifest['parameters'], sourceHashes=manifest['sourceHashes'],
        rtlHashes={p: hashlib.sha256(text.encode()).hexdigest() for p, text in (sources | observation_sources).items()},
        checkerHash=checker_hash, tools=tools, reports=reports), indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--rtl', type=Path, default=Path('result/production'))
    parser.add_argument('--output', type=Path, default=Path('result/formal'))
    parser.add_argument('--modules', nargs='+', choices=('Fetch', 'WideFetch', 'Gpr', 'Multiply', 'Backend', 'PipelineBackend', 'Pmp', 'PmpDecode', 'PmpInterval', 'Csr', 'UserCsr', 'UserExecute', 'SupervisorCsr', 'SupervisorExecute', 'SupervisorFetch', 'Lsu', 'InterruptCsr', 'InterruptBackend', 'SynchronizationBackend', 'InstructionCache', 'DataCache', 'Coherence', 'MemoryArbiter', 'Memory', 'Axi', 'WordDecode', 'WordExecute', 'IntegerDecode', 'IntegerExecute', 'WfiBackend', 'WfiFrontend', 'LocalInterrupts', 'Translation'))
    args = parser.parse_args()
    verify(args.rtl, args.output, args.modules)
