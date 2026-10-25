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
    dual = parameters.get('loadQueueEntries', 1) == 2
    width, capacity = parameters['issueWidth'], (5 + parameters.get('loadQueueEntries', 1)) * parameters['issueWidth']
    stages = ('commit', 'memory', *(('extra',) if dual else ()), 'result', 'issued', 'decoded', 'instruction')
    prediction = parameters.get('enableBranchPrediction', False)
    identity_bits = 97 if prediction else 96
    identity = lambda p, live=True: '{' + ((p + '_predictedTaken' if live else "1'b0") + ', ' if prediction else '') + p + '_pc, ' + p + '_instruction}'
    body = f'''
  reg pipeline_past = 0;
  reg [{capacity.bit_length()-1}:0] pipeline_owned;
  reg pipeline_fifo[{capacity}];
  (* anyconst *) reg [6:0] pipeline_bit;
  wire [{identity_bits-1}:0] pipeline_input[{width}];
  wire [{width.bit_length()-1}:0] pipeline_added = received ? instruction_bits_count : 0;
  wire [{capacity.bit_length()-1}:0] pipeline_discarded = {"memoryAdvance && memoryFault ? extraCount : 0" if dual else '0'};
  wire [{capacity.bit_length()-1}:0] pipeline_remaining = pipeline_owned - retireCount - (earlyRedirect ? instructionCount + decodedCount : 0) - pipeline_discarded;
  always @* assume(pipeline_bit < {identity_bits});
'''
    for lane in range(width):
        body += f'  assign pipeline_input[{lane}] = {identity(f"instruction_bits_packets_{lane}")};\n'
    def control_encoding(word):
        return f"({word}[6:0] == 7'h6f || ({word}[6:0] == 7'h67 && {word}[14:12] == 0) || ({word}[6:0] == 7'h63 && ({word}[14:12] == 0 || {word}[14:12] == 1 || {word}[14])))"
    older = '0'
    for stage in stages:
        suffix = '_decoded_instruction' if stage == 'issued' else '' if stage == 'instruction' else '_instruction'
        for lane in range(width):
            body += f'''  wire [{identity_bits-1}:0] pipeline_{stage}_{lane} = {identity(f'{stage}Packets_{lane}' + suffix, stage in ('instruction', 'decoded') or lane == 0)};
  always @(posedge clock) if (!reset && {stage}Count > {lane}{" && pipeline_bit < 96" if prediction and lane > 0 and stage not in ("instruction", "decoded") else ""})
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
          pipeline_fifo[pipeline_i] <= pipeline_fifo[pipeline_i + retireCount +
            (pipeline_discarded != 0 && pipeline_i >= commitCount + memoryCount - retireCount ? pipeline_discarded : 0)];
        else if (pipeline_i < pipeline_remaining + pipeline_added)
          pipeline_fifo[pipeline_i] <= pipeline_input[pipeline_i - pipeline_remaining][pipeline_bit];
      end
    end
    if (!reset) begin
      assert(pipeline_owned <= {capacity} && pipeline_owned == ({older}));
      assert(retireCount <= commitCount && issueCount <= decodedCount);
      if (redirect_0) assert(!received && !issued && !executed && !data_request_valid);
      assert(retireCount == (_commit_output_valid ? (_commit_output_bits_instruction_fault ? 1 : commitCount) : 0));
      if (_commit_output_valid && commitResolved) assert(!redirect_0);
      if (earlyRedirect) assert(!redirect_0 && !received && !issued && executed && issuedCount == 1);
      cover(earlyRedirect && memoryPending);
      cover(commitResolved && retireCount != 0 && !redirect_0);
      if (memoryPending) assert(memoryCount >= 1{"" if dual else ' && !commitValid'});
      if (lsu_input_valid) assert(resultCount >= 1);
      if (multiply_input_valid) assert(issuedCount == 1);
      cover(pipeline_owned == {6 * width} && received && retireCount == {width});
      cover(memoryPending && decodedValid && !issued);
      cover(issueCount == {width} && retireCount == {width});
      cover(issueCount == 0 && pipeline_owned != 0);
'''
    if width > 1:
        body += f'      cover(issueCount > 0 && issueCount < {width} && decodedCount == {width});\n'
    if dual:
        body += '''      assert(!extraPending || extraCount != 0);
      if (commitCount != 0 && (memoryPending || extraPending))
        assert(commitPackets_0_load && !commitPackets_0_store && !commitPackets_0_atomic && !commitPackets_0_instruction_fault);
      if (memoryPending) assert((memoryPackets_0_load || memoryPackets_0_store) && !memoryPackets_0_instruction_fault);
      if (extraPending) assert(!extraPackets_0_instruction_fault);
      if (extraCount != 0) begin
        assert(memoryCount != 0 && memoryPackets_0_load && !memoryPackets_0_store && !memoryPackets_0_atomic);
        assert(extraPackets_0_load && !extraPackets_0_store && !extraPackets_0_atomic && !extraPackets_0_csrWrite);
        assert(extraPackets_0_instruction_instruction[6:0] == 7'h03);
      end
      if (memoryFault) begin
        assert(!lsu_input_valid);
        if (data_request_valid) assert(!data_request_bits_write && !data_request_bits_atomic);
        if (extraPending) assert(!memoryAdvance);
      end
      cover(extraCount != 0 && memoryPending && extraPending);
      cover(memoryFault && extraPending);
'''
    body += '    end\n  end\n'
    for stage in stages:
        body += f'  always @(posedge clock) if (!reset) assert({stage}Count <= {width});\n'
        if stage in ('issued', 'result', 'memory', 'commit'):
            for lane in range(width):
                fault = f'{stage}Packets_{lane}_' + ('decoded_' if stage == 'issued' else '') + 'instruction_fault'
                if stage != 'commit' or lane != 0:
                    body += f'  always @(posedge clock) if (!reset && {stage}Count > 1 && {stage}Count > {lane}) assert(!{fault});\n'
    for stage in ('result', 'memory', 'commit'):
        p = stage + 'Packets_0'
        effects = ' || '.join(f'{p}_{field}' for field in ('atomic', 'csrWrite', 'mret', 'sret', 'wfi', 'fenceI', 'sfenceVma')
                             if re.search(rf'\b{p}_{field}\b', source))
        body += f'  always @(posedge clock) if (!reset && {stage}Count > 1) assert(!({effects}));\n'
    for stage in ('result', 'memory', 'commit'):
        p = f'{stage}Packets_0_instruction'
        control = control_encoding(p + '_instruction')
        body += f'  always @(posedge clock) if (!reset && {stage}Count != 0) assert({stage}Resolved == (!{p}_fault && {control}));\n'
        effects = ' || '.join(f'{stage}Packets_0_{field}' for field in ('load', 'store', 'atomic', 'csrWrite', 'mret', 'sret', 'wfi', 'fenceI', 'sfenceVma')
                             if re.search(rf'\b{stage}Packets_0_{field}\b', source))
        body += f'  always @(posedge clock) if (!reset && {stage}Count != 0 && {stage}Resolved) assert(!({effects}));\n'
        if dual:
            p = f'{stage}Packets_0'
            body += f'''  always @(posedge clock) if (!reset && {stage}Count != 0 && !{p}_atomic) begin
    if ({p}_load) assert({p}_instruction_instruction[6:0] == 7'h03);
    if ({p}_store) assert({p}_instruction_instruction[6:0] == 7'h23);
  end
'''
    if dual:
        for stage in ('result', 'memory', 'extra', 'commit'):
            p = f'{stage}Packets_0'
            effects = ' || '.join(p + '_' + field for field in ('csrWrite', 'mret', 'sret', 'wfi', 'fenceI', 'sfenceVma')
                                  if re.search(rf'\b{p}_{field}\b', source))
            body += f'''  always @(posedge clock) if (!reset && {stage}Count != 0 && ({p}_load || {p}_store)) begin
    assert({p}_nextPc == {p}_instruction_pc + {p}_instruction_length);
    assert(!({effects}));
    if (!{p}_atomic) assert(!({p}_load && {p}_store));
  end
'''

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
            control = ' || '.join(f'{packet}_operation == {op}' for op in (5, 6, 7, 25))
            body += f'  always @(posedge clock) if (!reset && {stage}Count > {lane}) assert(({control}) == {control_encoding(packet + "_instruction_instruction")});\n'
            if dual and lane == 0:
                for operations, opcode in (((8, 18, 19, 26), 3), ((9, 20, 27), 0x23), ((15, 30), 0x2f)):
                    selected = ' || '.join(f'{packet}_operation == {op}' for op in operations)
                    body += f"  always @(posedge clock) if (!reset && {stage}Count != 0 && ({selected})) assert({packet}_instruction_instruction[6:0] == 7'h{opcode:x});\n"

        if lane == 0:
            for stage, packet in (('decoded', d), ('issued', 'issuedPackets_0_decoded')):
                memory = ' || '.join(f'{packet}_operation == {op}' for op in (8, 9, 18, 19, 20, 26, 27))
                body += f'  wire pipeline_head_{stage} = pipeline_simple_{stage}_0 || (!{packet}_instruction_fault && ({memory}));\n'
        body += f'  always @(posedge clock) if (!reset && issuedCount > 1 && issuedCount > {lane}) assert({"pipeline_head_issued" if lane == 0 else f"pipeline_simple_issued_{lane}"});\n'
        blocked = []
        for operand in (1, 2):
            writers = []
            for stage in ('issued', 'result', *(('extra',) if dual else ()), 'memory', 'commit'):
                for previous in reversed(range(width)):
                    p = f'{stage}Packets_{previous}'
                    if stage == 'issued':
                        p += '_decoded'
                        ready = '_execute_output_valid && !_execute_output_bits_instruction_fault && !_execute_output_bits_load && !_execute_output_bits_store' if previous == 0 else '_execute_output_valid && !' + p + '_instruction_fault'
                        value = 'isMultiply ? _multiply_output_bits : _execute_output_bits_value' if previous == 0 else f'pipeline_execution_{previous}'
                    else:
                        ready = ('!memoryOperation && ' if stage == 'result' and previous == 0 else
                                 '(!memoryPending || _lsu_output_valid) && ' if dual and stage == 'memory' and previous == 0 else
                                 '!extraPending && ' if stage == 'extra' else
                                 '(!memoryCompletion || (memoryPending && _lsu_output_valid)) && ' if stage == 'memory' and previous == 0 else '') + (
                                     '!completion_instruction_fault' if stage == 'memory' and previous == 0 else '!' + p + '_instruction_fault')
                        value = ('memoryPending && _lsu_output_valid ? _lsu_output_bits_value : ' if dual else 'memoryPending ? _lsu_output_bits_value : ') + p + '_value' if stage == 'memory' and previous == 0 else p + '_value'
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
    {f"pipeline_prefix_{lane-1} && pipeline_head_decoded && pipeline_simple_decoded_{lane} && !(" + " || ".join(conflict) + ")" if lane else "1'b1"};
'''
    for lane in range(1, width):
        match = re.search(rf'resultPackets_{lane}_value <=\s*([^;]+);', source)
        assert match
        body += f'  wire [63:0] pipeline_execution_{lane} = {match[1]};\n'
    expected = ' + '.join(f"{{{width.bit_length()-1}'b0, pipeline_prefix_{lane}}}" if width > 1 else f'pipeline_prefix_{lane}' for lane in range(width))
    sleeping = 'sleep' if parameters.get('enableInterrupts') else "1'b0"
    body += f'''  always @(posedge clock) if (!reset) begin
    assert(issueCount == ((!issuedValid || executed) && !executePending && !redirect_0 && !earlyRedirect && !{sleeping} ? ({expected}) : 0));
  end
'''
    offset = 'issuedPackets_0_decoded_instruction_length'
    if parameters.get('enableBranchPrediction'):
        offset = 'issuedPackets_0_decoded_instruction_predictedTaken ? issuedPackets_0_decoded_immediate : ' + offset
    body += f"""  wire pipeline_control = issuedPackets_0_decoded_operation == 5 || issuedPackets_0_decoded_operation == 6 ||
    issuedPackets_0_decoded_operation == 7 || issuedPackets_0_decoded_operation == 25;
  wire [63:0] pipeline_expected_pc = issuedPackets_0_decoded_instruction_pc + ({offset});
  always @(posedge clock) if (!reset) assert(earlyRedirect == (executed && pipeline_control &&
    !_execute_output_bits_instruction_fault && _execute_output_bits_nextPc != pipeline_expected_pc));
"""
    before = re.search(r'commitPackets_0_instruction_pc <=\s*[^;]+;', source).group()
    translation = ' || translation_request_valid || translation_response_ready' if parameters.get('virtualAddressBits') == 39 else ''
    if dual:
        body += '''  always @(posedge clock) if (!reset && backend_memory_owned != 0) begin
    assert(memoryPending || extraPending);
    assert(_lsu_output_bits_instruction_pc == (memoryPending ? memoryPackets_0_instruction_pc : extraPackets_0_instruction_pc));
    assert(_lsu_output_bits_instruction_tag == (memoryPending ? memoryPackets_0_instruction_tag : extraPackets_0_instruction_tag));
    assert(_lsu_output_bits_instruction_instruction == (memoryPending ? memoryPackets_0_instruction_instruction : extraPackets_0_instruction_instruction));
  end
'''
    else:
        body += '''  always @(posedge clock) if (!reset) assert(memoryPending == backend_memory_owned);
  always @(posedge clock) if (!reset && memoryPending) begin
    assert(memoryPackets_0_instruction_tag == _lsu_output_bits_instruction_tag &&
      memoryPackets_0_instruction_pc == _lsu_output_bits_instruction_pc &&
      memoryPackets_0_instruction_instruction == _lsu_output_bits_instruction_instruction);
  end
'''
    lsu = instance_ports(source, 'DitDahA1Lsu')[0][1]
    for field in ('load', 'store', 'atomic', 'csrWrite', 'mret', 'sret', 'wfi', 'fenceI', 'sfenceVma', 'instruction_predictedTaken', *(('nextPc', 'instruction_length') if dual else ())):
        if not re.search(rf'\b_lsu_output_bits_{field}\b', source):
            continue
        expected = f'memoryPackets_0_{field}'
        if not re.search(rf'\b{expected}\b', source):
            expected = lsu[f'input_bits_{field}']
            assert re.fullmatch(r"\d+'[hbd][0-9a-fA-F]+", expected), expected
        if dual:
            expected = f'(memoryPending ? {expected} : extraPackets_0_{field})'
        body += f'  always @(posedge clock) if (!reset && {"backend_memory_owned != 0" if dual else "memoryPending"}) assert({expected} == _lsu_output_bits_{field});\n'
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
  (* anyconst *) reg [2:0] scenario;
  (* anyseq *) reg respond;
  reg started = 0, pending = 0;
  reg [63:0] pc = 64'h100;
  always @(posedge clock) if (!reset) begin
    if (instruction_valid && instruction_ready) begin started <= 1; pc <= pc + 4 * instruction_bits_count; end
    if (data_request_valid && data_request_ready) pending <= 1;
    if (data_response_valid && data_response_ready) pending <= 0;
  end
'''
    scenario = 3 if mode.startswith('mutation-recovery') or mode == 'cover-recovery' else 4 if mode.startswith('mutation-memory') else {'cover-memory': 1, 'cover-dependency': 2, 'cover-dual': 5, 'cover-drain': 6, 'mutation-dual-owner': 5, 'mutation-dual-drain': 6}.get(mode, 0)
    body = body.replace('(* anyconst *) reg [2:0] scenario;', f"wire [2:0] scenario = {scenario};")
    values = dict(instruction_valid=1, instruction_bits_count=f'scenario == 3 || (scenario == 1 && !started) ? 1 : {width}',
                  data_request_ready=1, data_response_valid='pending && (scenario == 3 || respond)', data_response_bits_last=1, data_response_bits_fault='scenario == 4')
    for lane in range(width):
        packet = f'instruction_bits_packets_{lane}_'
        word = (1 << 20) | ((lane + 1) << 7) | 0x13
        values[packet + 'instruction'] = (f"scenario == 4 && !started ? 32'h00803083 : scenario == 3 ? (!started ? 32'h00003023 : pc == 64'h108 ? 32'h0080006f : 32'h{word:x}) : scenario == 1 && !started ? 32'h00003023 : 32'h{word:x}" if lane == 0 else
                                         f"scenario == 2 ? 32'h{word | (1 << 15):x} : 32'h{word:x}" if lane == 1 else f"32'h{word:x}")
        values[packet + 'pc'], values[packet + 'length'] = f'pc + {4 * lane}', 4
    if mode in ('mutation', 'mutation-forward', 'mutation-dependency'):
        for lane in range(width):
            rd = lane + 1
            rs1 = rd if mode == 'mutation-forward' else 1 if mode == 'mutation-dependency' and lane == 1 else 0
            values[f'instruction_bits_packets_{lane}_instruction'] = f"32'h{(1 << 20) | (rs1 << 15) | (rd << 7) | 0x13:x}"
    if mode == 'mutation-recovery-retirement':
        values['instruction_bits_packets_0_instruction'] = "!started ? 32'h0080006f : 32'h13"
    if parameters.get('loadQueueEntries', 1) == 2 and scenario in (5, 6):
        body += '''  reg [1:0] read_pending = 0;
  reg both_seen = 0;
  always @(posedge clock) if (!reset) begin
    if (data_request_valid && data_request_ready) read_pending[data_request_bits_tag[0]] <= 1;
    if (data_response_valid && data_response_ready) read_pending[data_response_bits_tag[0]] <= 0;
    if (&read_pending) both_seen <= 1;
  end
'''
        values.update(instruction_bits_count=1,
                      data_response_valid='both_seen && (|read_pending)',
                      data_response_bits_tag='scenario == 5 ? (read_pending[1] ? 1 : 0) : (read_pending[0] ? 0 : 1)',
                      data_response_bits_fault='scenario == 6 && data_response_bits_tag == 0')
        values['instruction_bits_packets_0_instruction'] = "pc == 64'h100 ? 32'h00003083 : pc == 64'h104 ? 32'h00803103 : 32'h00100193"
    if parameters.get('virtualAddressBits') == 39:
        body += r'''
  reg translation_pending = 0;
  reg [63:0] translation_address;
  always @(posedge clock) if (!reset) begin
    if (translation_request_valid && translation_request_ready) begin translation_pending <= 1; translation_address <= translation_request_bits_address; end
    if (translation_response_valid && translation_response_ready) translation_pending <= 0;
  end
'''
        values.update(translation_request_ready=1, translation_response_valid='translation_pending',
                      translation_response_bits_address='translation_address')
    return body, values


def protection_cases(parameters):
    width = parameters['physicalAddressBits'] - 2
    fetch_sizes = ([4] if parameters.get('iCacheBytes') and parameters['issueWidth'] == 3 else []) + ([6] if parameters.get('enableBurstRefill') else [])
    line_size = ''.join(f' || (size == {size} && fetch && !write && !atomic)' for size in fetch_sizes)
    data_line = parameters.get('dCacheRefillBytes', 8) == 64
    span_sizes = sorted(set(fetch_sizes + ([6] if data_line else [])))
    if data_line:
        line_size += ' || (size == 6 && !fetch && !write && !atomic)'
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
        supported = 'size <= 3' + ''.join(f' || size == {size}' for size in span_sizes)
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
'''.replace('OFFSET', str(max(span_sizes)-1)).replace('SUPPORTED', supported).replace('EXTRA', str(max(span_sizes)))
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
    if data_line:
        pmp += '  always @* begin cover(allowed && size == 6 && !fetch && !write && !atomic); cover(!allowed && size == 6 && !fetch && !write && !atomic); end\n'
        subset = f'''
  (* anyconst *) reg [5:0] subset_offset;
  (* anyconst *) reg [1:0] subset_size;
  (* anyconst *) reg whole_line;
  wire [64:0] whole_start = {{1'b0, address}}, whole_end = {{1'b0, address}} + (whole_line ? 65'd64 : 65'd8);
  wire [64:0] subset_start = whole_start + subset_offset;
  wire [64:0] subset_end = subset_start + (65'd1 << subset_size);
  wire permission = ({machine}) && !config[7] || config[0];
  wire whole_hit = config[4:3] != 0 && high > low && whole_start < high && whole_end > low;
  wire subset_hit = config[4:3] != 0 && high > low && subset_start < high && subset_end > low;
  wire whole_allowed = (whole_hit ? whole_start >= low && whole_end <= high && permission : prior_whole) && whole_end <= (65'd1 << {width+2});
  wire subset_allowed = (subset_hit ? subset_start >= low && subset_end <= high && permission : prior_subset) && subset_end <= (65'd1 << {width+2});
  always @* begin
    assume(!prior_whole || prior_subset);
    if (subset_end <= whole_end) begin
      assert(!whole_allowed || subset_allowed);
      cover(whole_line && whole_allowed && subset_allowed);
      cover(whole_line && !whole_allowed && subset_allowed);
      cover(!whole_line && whole_allowed && subset_allowed);
      cover(!whole_line && !whole_allowed && subset_allowed);
    end
  end
'''
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
            ('Backend', backend, '| _commit_output_bits_csrWrite\n', "| 1'h0 & _commit_output_bits_csrWrite\n")] + ([
                ('PmpSubset', subset, 'whole_end <= high', 'whole_start < high')]
                if data_line else [])


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
    pipelined = bool(parameters.get('iCacheBytes'))
    fetch = fetch.replace('PIPELINED', str(int(pipelined)))
    if pipelined and parameters['issueWidth'] > 1:
        banks = 1 << (parameters['issueWidth'] - 1).bit_length()
        fetch = fetch.replace('&& !output_bits_fault;', f'&& !output_bits_fault && output_bits_count >= {banks} - output_bits_pc[{banks.bit_length()}:2];')
    if pipelined:
        fetch += '\n  always @(posedge clock) if (!reset) cover(state != 0 && request_valid && request_ready && retained_fetch_mode != privilege);\n'
    if parameters.get('virtualAddressBits') == 39:
        fetch += '''
  reg context_translation_owned = 0;
  always @(posedge clock) if (reset) context_translation_owned <= 0;
  else begin
    assume(!translation_response_valid || context_translation_owned || (translation_request_valid && translation_request_ready));
    if (translation_request_valid && translation_request_ready) context_translation_owned <= 1;
    if (translation_response_valid && translation_response_ready) context_translation_owned <= 0;
  end
'''
    return [('SupervisorCsr', csr, 'assign trapVector = supervisorTrap_1 ? stvec : mtvec;', 'assign trapVector = mtvec;'),
            ('SupervisorExecute', execute, 'assign output_bits_instruction_cause =', 'assign output_bits_instruction_cause = 11 |'),
            ('SupervisorFetch', fetch, 'wire [1:0] formal_fetch_mode =', "wire [1:0] formal_fetch_mode = 2'd3 |")]


def translation_case(parameters):
    count = parameters.get('tlbEntries', 0)
    invalidating = 'invalidate' if count else "1'b0"
    ordinary = ' || '.join(f"(walk_address >= 64'h{int(region['base']):x} && walk_address <= 64'h{int(region['base']) + int(region['size']) - 8:x})"
                          for region in parameters['memoryRegions'] if region['readable'] and not region['device'] and int(region['size']) >= 8) or "1'b0"
    permit = '_pmp_allowed' if parameters['pmpEntries'] else "1'b1"
    body = f'''
  wire formal_permit = {permit};
  wire ordinary = ({ordinary}) && walk_address <= 64'h{(1 << parameters['physicalAddressBits']) - 8:x};
  wire formal_invalidate = {invalidating};
''' + r'''
  reg translation_past = 0, active, client, priority_client, translation_cancelled;
  reg bus_owned, offered, denied, done, expected_fault, expected_page_fault, completed_leaf;
  reg [63:0] virtual_address, walk_address, expected_address;
  reg [1:0] effective_privilege, walk_level;
  reg fetch_access, write_access, allow_sum, allow_mxr;
  wire cancel_now = translation_cancelled || cancelInstruction && !client;
  wire [63:0] access_cause = fetch_access ? 1 : write_access ? 7 : 5;
  wire [63:0] page_cause = fetch_access ? 12 : write_access ? 15 : 13;
  wire [63:0] formal_pte = memory_response_bits_data;
  wire leaf_pte = formal_pte[1] || formal_pte[3];
  wire access_allowed = fetch_access ? formal_pte[3] : write_access ? formal_pte[2] : formal_pte[1] || allow_mxr && formal_pte[3];
  wire mode_allowed = effective_privilege == 0 ? formal_pte[4] : !formal_pte[4] || allow_sum && !fetch_access;
  wire bad_alignment = walk_level == 2 && formal_pte[27:10] != 0 || walk_level == 1 && formal_pte[18:10] != 0;
  wire bad_pte = !formal_pte[0] || !formal_pte[1] && formal_pte[2] || formal_pte[63:54] != 0 ||
    (leaf_pte ? !access_allowed || !mode_allowed || bad_alignment || !formal_pte[6] || write_access && !formal_pte[7] :
      walk_level == 0 || formal_pte[4] || formal_pte[6] || formal_pte[7]);
  wire [63:0] page_mask = walk_level == 2 ? 64'h3fffffff : walk_level == 1 ? 64'h1fffff : 64'hfff;
  wire [63:0] leaf_address = ((formal_pte >> 10 << 12) & ~page_mask) | (virtual_address & page_mask);
  wire [63:0] next_address = ((formal_pte >> 10) & 64'hfffffffffff) * 4096 +
    ((walk_level == 2 ? (virtual_address >> 21) : (virtual_address >> 12)) & 511) * 8;
  wire any_response = ports_0_response_valid || ports_1_response_valid;
  wire walk_response = active && (done || denied);
'''
    for port in range(2):
        q = f'ports_{port}_request_bits'
        hit = [f"(tlbValid[{i}] && ({q}_address[38:12] >> (9 * tlb_{i}_level)) == (tlb_{i}_vpn >> (9 * tlb_{i}_level)))" for i in range(count)]
        cached_pte = ''.join(f'{hit[i]} ? tlb_{i}_pte : ' for i in range(count)) + "64'd0"
        cached_level = ''.join(f'{hit[i]} ? tlb_{i}_level : ' for i in range(count)) + "2'd0"
        p = f'formal_lookup_{port}'
        body += f'''
  reg formal_held_{port};
  reg [63:0] formal_held_address_{port}, formal_held_cause_{port};
  reg formal_held_fault_{port};
  wire {p}_available = !formal_held_{port} && !(active && client == {port}) && !formal_invalidate {'&& !cancelInstruction' if port == 0 else ''};
  wire {p}_paged = {q}_privilege != 3 && state_satp[63:60] != 0;
  wire {p}_invalid = {p}_paged && (state_satp[63:60] != 8 || {q}_address[63:39] != {{25{{{q}_address[38]}}}});
  wire {p}_hit = {' || '.join(hit) or "1'b0"};
  wire [63:0] {p}_pte = {cached_pte};
  wire [1:0] {p}_level = {cached_level};
  wire [63:0] {p}_mask = {p}_level == 2 ? 64'h3fffffff : {p}_level == 1 ? 64'h1fffff : 64'hfff;
  wire {p}_access = {q}_fetch ? {p}_pte[3] : {q}_write ? {p}_pte[2] : {p}_pte[1] || state_mxr && {p}_pte[3];
  wire {p}_mode = {q}_privilege == 0 ? {p}_pte[4] : !{p}_pte[4] || state_sum && !{q}_fetch;
  wire {p}_denied = !{p}_access || !{p}_mode || !{p}_pte[6] || {q}_write && !{p}_pte[7];
  wire {p}_fast = !{p}_paged || {p}_invalid || {p}_hit;
  wire {p}_fault = {p}_invalid || {p}_paged && {p}_hit && {p}_denied;
  wire [63:0] {p}_address = {p}_paged && {p}_hit && !{p}_fault ?
    (({p}_pte >> 10 << 12) & ~{p}_mask) | ({q}_address & {p}_mask) : {q}_address;
  wire [63:0] {p}_cause = {p}_fault ? ({q}_fetch ? 12 : {q}_write ? 15 : 13) : 0;
  wire {p}_miss = ports_{port}_request_valid && {p}_available && !{p}_fast;
  wire {p}_response = ports_{port}_request_valid && {p}_available && {p}_fast;
'''
    body += r'''
  wire data_selected = formal_lookup_1_miss && (!formal_lookup_0_miss || priority_client);
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
      assert(!memory_response_ready || bus_owned);
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
        assert(memory_request_bits_privileged && !memory_request_bits_write && !memory_request_bits_fetch && !memory_request_bits_atomic && !memory_request_bits_atomicOperation && !memory_request_bits_scEligible && !memory_request_bits_refillSize);
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
      if (walk_response) begin
        assert(!bus_owned);
        if (!done) begin done <= 1; expected_fault <= 1; end
        if (client ? ports_1_response_ready : ports_0_response_ready) begin
          active <= 0; priority_client <= !client;
        end
      end
      if ($past(!reset && memory_request_valid && !memory_request_ready)) begin
        assert(memory_request_valid);
        assert($stable({memory_request_bits_address, memory_request_bits_data, memory_request_bits_size,
          memory_request_bits_mask, memory_request_bits_tag, memory_request_bits_write, memory_request_bits_fetch,
          memory_request_bits_privileged, memory_request_bits_atomic, memory_request_bits_atomicOperation, memory_request_bits_scEligible, memory_request_bits_refillSize}));
      end
      cover(memory_request_valid && !memory_request_ready && cancelInstruction && !client);
      cover(cancel_now && bus_owned && memory_response_valid && memory_response_ready && !leaf_pte);
      cover(walk_response && expected_page_fault && write_access);
      cover(walk_response && expected_fault && !expected_page_fault);
      cover(walk_response && completed_leaf && walk_level == 0);
      cover(walk_response && completed_leaf && walk_level == 1);
      cover(walk_response && completed_leaf && walk_level == 2);
      cover(formal_lookup_0_response && formal_lookup_1_response);
      cover(bus_owned && client && formal_lookup_0_response && formal_lookup_0_hit);
      cover(bus_owned && !client && formal_lookup_1_response && formal_lookup_1_hit);
    end
'''
    if not count:
        body = body.replace(' && formal_lookup_0_hit', '').replace(' && formal_lookup_1_hit', '')
    for port in range(2):
        p, q, response = f'formal_lookup_{port}', f'ports_{port}_request_bits', f'ports_{port}_response_bits'
        body += f'''
    if (!reset && ports_{port}_request_valid && ports_{port}_request_ready && !{p}_fast) begin
      assert(!active);
      active <= 1; client <= {port}; translation_cancelled <= 0; offered <= 0; denied <= 0;
      bus_owned <= 0; expected_fault <= 0; expected_page_fault <= 0; completed_leaf <= 0; done <= 0;
      virtual_address <= {q}_address;
      effective_privilege <= {q}_privilege;
      fetch_access <= {q}_fetch; write_access <= {q}_write;
      allow_sum <= state_sum; allow_mxr <= state_mxr; walk_level <= 2;
      expected_address <= {q}_address;
      walk_address <= (state_satp & 64'hfffffffffff) * 4096 + (({q}_address >> 30) & 511) * 8;
    end
    if (reset) formal_held_{port} <= 0;
    else begin
      assert(ports_{port}_request_ready == ({p}_available && ({p}_fast || !active && data_selected == {port})));
      assert(ports_{port}_response_valid == (formal_held_{port} || walk_response && client == {port} || {p}_response));
      assert(!(formal_held_{port} && active && client == {port}));
      if ({p}_response) begin
        assert(ports_{port}_request_ready);
        if (!ports_{port}_response_ready) begin
          formal_held_{port} <= 1;
          formal_held_address_{port} <= {p}_address; formal_held_fault_{port} <= {p}_fault; formal_held_cause_{port} <= {p}_cause;
        end
      end
      if (formal_held_{port} && ports_{port}_response_ready) formal_held_{port} <= 0;
      if (ports_{port}_response_valid) begin
        if (formal_held_{port}) begin
          assert({response}_address == formal_held_address_{port} && {response}_fault == formal_held_fault_{port} && {response}_cause == formal_held_cause_{port});
        end else if (active && client == {port}) begin
          assert({response}_address == expected_address && {response}_fault == (expected_fault || !done));
          assert({response}_cause == ((expected_fault || !done) ? (expected_page_fault ? page_cause : access_cause) : 0));
        end else begin
          assert({p}_response && {response}_address == {p}_address && {response}_fault == {p}_fault && {response}_cause == {p}_cause);
        end
      end
      if ($past(!reset && ports_{port}_response_valid && !ports_{port}_response_ready)) begin
        assert(ports_{port}_response_valid);
        assert($stable({{{response}_address, {response}_fault, {response}_cause}}));
      end
      cover(formal_held_{port} {'&& formal_invalidate' if count else ''} && ports_{port}_response_ready);
    end
'''
    body += '  end\n'
    if count:
        body += '''
  reg cache_refill_allowed = 0;
  wire cache_leaf = bus_owned && memory_response_valid && memory_response_ready && !cancel_now &&
    !memory_response_bits_fault && memory_response_bits_tag == 0 && !bad_pte && leaf_pte;
  wire cache_fill = cache_leaf && cache_refill_allowed && !invalidate;
  always @(posedge clock) begin
    if (reset) cache_refill_allowed <= 0;
    else if (invalidate) cache_refill_allowed <= 0;
    else if (ports_0_request_valid && ports_0_request_ready && !formal_lookup_0_fast ||
             ports_1_request_valid && ports_1_request_ready && !formal_lookup_1_fast) cache_refill_allowed <= 1;
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
      cover(formal_lookup_0_response && formal_lookup_0_hit && !formal_lookup_0_denied);
      cover(formal_lookup_1_response && formal_lookup_1_hit && formal_lookup_1_denied && ports_1_request_bits_write);
      cover(cache_leaf && cache_refill_allowed && invalidate);
      cover(walk_response && !cache_refill_allowed && !fault);
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
      assert(memoryPending == backend_memory_owned);
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
      assert(memoryPending == backend_memory_owned);
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
    fields = ('pc', 'tag', 'predictedTaken', 'instruction', 'length', 'fault', 'cause', 'tval')
    packed = lambda prefix: '{' + ', '.join(prefix + field for field in fields) + '}'
    count = '_fetch_output_bits_count' if words > 1 else '1'
    reserved = 'reserved' if words > 1 else '1'
    expected = f"{words} - pc[{words.bit_length()}:2]" if words > 1 else '1'
    flush = 'redirect || invalidate' if parameters.get('iCacheBytes') else 'redirect'
    pending_pc = 'pendingPc' if parameters.get('iCacheBytes') else 'front_pc'
    body = f'''
  reg front_past = 0;
  (* anyconst *) reg [7:0] front_bit;
  always @* assume(front_bit < 237);
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
  wire [{index_bits-1}:0] front_raw_count = front_return ? {count} : 0;
  reg [{index_bits-1}:0] front_count;
  reg front_prediction;
  reg [63:0] front_target;
  wire [63:0] front_request_pc = front_prediction ? front_target : pc;
  wire [{index_bits-1}:0] front_expected = {expected.replace('pc[', 'front_request_pc[')};
  wire [{index_bits-1}:0] front_buffered = front_owned - (formal_fetch_pending ? front_reserved : 0);
  reg front_reference [0:{capacity-1}];
  wire front_sequence [0:{capacity+words-1}];
  wire [236:0] front_input [0:{words-1}], front_buffer [0:{capacity-1}], front_output [0:{width-1}];
'''
    for lane in range(words):
        instruction = '_fetch_output_bits_instruction' if lane == 0 else f'_fetch_output_bits_following_{lane-1}'
        body += f"""  wire [31:0] front_word_{lane} = {instruction};
  wire front_branch_{lane} = front_word_{lane}[6:0] == 7'h63 && (front_word_{lane}[14:12] == 0 || front_word_{lane}[14:12] == 1 || front_word_{lane}[14]);
  wire front_jump_{lane} = front_word_{lane}[6:0] == 7'h6f;
  wire front_predict_{lane} = {int(parameters.get('enableBranchPrediction', False))} && !_fetch_output_bits_fault && (front_jump_{lane} || (front_branch_{lane} && front_word_{lane}[31]));
  wire signed [63:0] front_offset_{lane} = front_jump_{lane} ?
    $signed({{{{front_word_{lane}[31], front_word_{lane}[19:12], front_word_{lane}[20], front_word_{lane}[30:21], 1'b0}}}}) :
    $signed({{{{front_word_{lane}[31], front_word_{lane}[7], front_word_{lane}[30:25], front_word_{lane}[11:8], 1'b0}}}});
"""
        body += f"  assign front_input[{lane}] = {{_fetch_output_bits_pc + 64'd{4*lane}, _fetch_output_bits_tag + 8'd{lane}, front_predict_{lane}, {instruction}, 3'd4, " + (
            "_fetch_output_bits_fault, _fetch_output_bits_cause, _fetch_output_bits_tval};\n" if lane == 0 else "1'b0, 64'd0, 64'd0};\n")
    body += "  always @* begin\n    front_count = front_raw_count; front_prediction = 0; front_target = 0;\n"
    for lane in range(words):
        body += f"    if (!front_prediction && front_return && {lane} < front_raw_count && front_predict_{lane}) begin front_count = {lane+1}; front_prediction = 1; front_target = _fetch_output_bits_pc + 64'd{lane*4} + front_offset_{lane}; end\n"
    body += "  end\n"
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
      if (front_accept) begin front_reserved <= front_expected; front_pc <= front_request_pc; end
    end
    if (!reset) begin
      assert(FORMAL_FRONT_REQUEST_PC == front_request_pc);
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
        else if ($past(front_accept)) assert(pc == $past(front_request_pc + 64'd4 * front_expected));
        else if ($past(front_prediction)) assert(pc == $past(front_target));
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
    if parameters.get('enableBranchPrediction'):
        body += '      cover(front_prediction && front_accept);\n      cover(front_prediction && !front_accept);\n'
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


def line_lsu_contract(body, parameters):
    translated = parameters.get('virtualAddressBits') == 39
    protected = bool(parameters['pmpEntries'])
    address = 'translation_response_bits_address' if translated else 'input_bits_address'
    size = 'word_size' if translated else 'input_bits_memorySize'
    load, store, atomic = ('word_load', 'word_store', 'word_atomic') if translated else ('input_bits_load', 'input_bits_store', 'input_bits_atomic')
    accepted = 'translation_response_valid && translation_response_ready' if translated else 'input_valid && input_ready'
    valid = '!translation_response_bits_fault' if translated else '!input_bits_instruction_fault && word_aligned'
    physical = 'word_physical_address' if translated else 'word_address'
    privilege = 'word_privilege' if translated else 'privilege'
    permitted = '_pmp_allowed' if protected else "1'b1"
    def region_span(count):
        return ' || '.join(f"(({address} & ~64'd{count-1}) >= 64'h{int(r['base']):x} && ({address} & ~64'd{count-1}) <= 64'h{int(r['base'])+int(r['size'])-count:x})"
                          for r in parameters['memoryRegions'] if r.get('dataCacheable') and r['readable'] and not r['device'] and int(r['size']) >= count) or "1'b0"
    body = body.replace('!word_permitted', 'word_initial_denied')
    declarations = f'''
  reg [2:0] word_check, word_grant;
  reg [1:0] word_access_privilege;
  reg word_eight_candidate;
  wire word_load_candidate = {load} && !{store} && !{atomic} && {size} <= 3;
  wire word_line_candidate = word_load_candidate && ({region_span(64)});
  wire word_word_candidate = word_load_candidate && {size} < 3 && ({region_span(8)});
  wire [2:0] word_candidate = word_line_candidate ? 6 : word_word_candidate ? 3 : 0;
  wire [63:0] word_probe_address = word_candidate == 6 ? ({address} & ~64'd63) : word_candidate == 3 ? ({address} & ~64'd7) : {address};
  wire [2:0] word_probe_size = word_candidate != 0 ? word_candidate : {size};
  wire word_initial_denied = !word_permitted && word_candidate == 0;
  always @(posedge clock) begin
    if (reset) begin word_check <= 0; word_grant <= 0; end
    else begin
      if (input_valid && input_ready) begin word_access_privilege <= privilege; word_grant <= 0; word_check <= 0; end
      if ({accepted} && ({valid})) begin
        word_eight_candidate <= word_word_candidate;
        word_grant <= {permitted} ? word_candidate : 0;
        word_check <= !{permitted} && word_candidate != 0 ?
          (word_candidate == 6 && word_word_candidate ? 6 : 7) : 0;
      end
      assert((state == 6 || state == 7) == (word_check != 0));
      if (word_check != 0) begin
        assert(state == word_check && !memory_request_valid && !output_valid);
        word_check <= word_check == 6 && !{permitted} ? 7 : 0;
        word_grant <= word_check == 6 && {permitted} ? 3 : 0;
      end
      if (memory_request_valid) begin
        assert(word_check == 0 && memory_request_bits_refillSize == word_grant);
        if (word_grant != 0) assert(word_load && !word_store && !word_atomic && word_size <= 3);
      end
      if ($past(!reset && memory_request_valid && !memory_request_ready)) assert($stable(memory_request_bits_refillSize));
      cover(memory_request_valid && word_grant == 6);
      cover(memory_request_valid && word_grant == 3);
      cover(memory_request_valid && word_grant == 0 && word_eight_candidate);
    end
  end
'''
    if protected:
        declarations += f'''
  always @* if (!reset && word_check != 0) begin
    assert(formal_pmp_address == (word_check == 6 ? ({physical} & ~64'd7) : {physical}));
    assert(formal_pmp_size == (word_check == 6 ? 3 : word_size));
    assert(formal_pmp_privilege == word_access_privilege && !formal_pmp_fetch);
    assert(formal_pmp_write == (word_check == 7 && word_store));
    assert(formal_pmp_atomic == (word_check == 7 && word_load && word_store));
  end
'''
        body = body.replace('      if (memory_request_valid) begin', f'''
      if (word_check == 7 && !{permitted}) begin
        word_done <= 1; word_fault <= 1; word_cause <= word_store ? 7 : 5; word_tval <= word_address;
      end
      if (memory_request_valid) begin''', 1)
    else:
        declarations = declarations.replace('      cover(memory_request_valid && word_grant == 0 && word_eight_candidate);', '').replace('      cover(memory_request_valid && word_grant == 3);', '')
    return declarations + body


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
    data_line = parameters.get('dCacheRefillBytes', 8) == 64 and parameters.get('dCacheBytes')
    if parameters.get('dCacheBytes') and not data_line:
        ranges = ' || '.join(f"((input_bits_address & ~64'd7) >= 64'h{int(r['base']):x} && (input_bits_address & ~64'd7) <= 64'h{int(r['base'])+int(r['size'])-8:x})"
                            for r in parameters['memoryRegions'] if r.get('dataCacheable') and not r['device'] and int(r['size']) >= 8) or "1'b0"
        lsu += f'''
  reg word_refill_pending, word_refill_permission;
  reg [1:0] word_refill_privilege;
  wire word_refill_candidate = input_bits_load && !input_bits_store && !input_bits_atomic &&
    input_bits_memorySize < 3 && ({ranges});
  always @(posedge clock) begin
    if (reset) begin word_refill_pending <= 0; word_refill_permission <= 0; end
    else begin
      if (memory_request_valid) assert(!word_refill_pending && memory_request_bits_refillSize == (word_refill_permission ? 3 : 0));
'''
        if parameters['pmpEntries']:
            lsu += '''
      assert(word_refill_pending == (state == 6));
      if (word_refill_pending) begin
        assert(formal_pmp_address == (word_address & ~64'd7) && formal_pmp_size == 3);
        assert(!formal_pmp_write && !formal_pmp_fetch && !formal_pmp_atomic && formal_pmp_privilege == word_refill_privilege);
        word_refill_permission <= _pmp_allowed; word_refill_pending <= 0;
      end
'''
        lsu += f'''
      if (input_valid && input_ready) begin
        word_refill_pending <= {int(bool(parameters['pmpEntries']))} && word_refill_candidate &&
          !input_bits_instruction_fault && word_aligned && word_permitted;
        word_refill_permission <= {int(not parameters['pmpEntries'])} && word_refill_candidate;
        word_refill_privilege <= privilege;
      end
      cover(memory_request_valid && memory_request_bits_refillSize);
      cover(memory_request_valid && word_load && !word_store && word_size < 3 && !memory_request_bits_refillSize);
    end
  end
'''
    elif not data_line:
        lsu += '  always @* if (memory_request_valid) assert(!memory_request_bits_refillSize);\n'
    if parameters.get('virtualAddressBits') == 39:
        lsu = lsu.replace(' || !word_permitted', '').replace('input_bits_address == word_reserved_address && ', '')
        lsu = lsu.replace("((64'd1 << input_bits_memorySize) - 1)", "((64'd1 << (input_bits_memorySize < 3 ? input_bits_memorySize : 3)) - 1)")
        lsu = lsu.replace('memory_request_bits_address == word_address', 'memory_request_bits_address == word_physical_address')
        lsu = lsu.replace('word_reserved_address <= word_address &', 'word_reserved_address <= word_physical_address &')
        lsu = lsu.replace('formal_pmp_address == (word_address &', 'formal_pmp_address == (word_physical_address &')
        lsu = lsu.replace('word_reservation <= 0; end', 'word_reservation <= 0; word_translation_sent <= 0; word_translated <= 0; end')
        lsu = lsu.replace('word_owned <= 1; word_sent <= 0; word_replied <= 0;', 'word_owned <= 1; word_sent <= 0; word_replied <= 0; word_translation_sent <= 0; word_translated <= 0; word_privilege <= privilege;')
        if parameters.get('dCacheBytes') and not data_line:
            candidate = re.search(r'wire word_refill_candidate =[^;]+;', lsu).group()
            updated = candidate.replace('input_bits_address', 'translation_response_bits_address')
            for field, captured in (('load', 'load'), ('store', 'store'), ('atomic', 'atomic'), ('memorySize', 'size')):
                updated = updated.replace('input_bits_' + field, 'word_' + captured)
            lsu = lsu.replace(candidate, updated).replace('if (input_valid && input_ready) begin\n        word_refill_pending', 'if (translation_response_valid && translation_response_ready) begin\n        word_refill_pending')
            lsu = lsu.replace('!input_bits_instruction_fault && word_aligned && word_permitted', '!translation_response_bits_fault && word_permitted')
            lsu = lsu.replace('word_refill_privilege <= privilege;', 'word_refill_privilege <= word_privilege;')
        lsu = '  reg word_translation_sent, word_translated;\n  reg [63:0] word_physical_address;\n  reg [1:0] word_privilege;\n' + lsu
        lsu = ("  wire word_legal_request = word_valid_size && !word_atomic && (word_load != word_store) && word_privilege <= 1 && word_address[63:39] == {25{word_address[38]}};\n"
               + f"  wire word_translated_range = word_physical_address[63:{parameters['physicalAddressBits']}] == 0 && word_physical_address[11:0] == word_address[11:0];\n" + lsu)
        lsu = lsu.replace('cover(memory_request_valid && memory_request_bits_refillSize);', 'cover(memory_request_valid && memory_request_bits_refillSize && word_legal_request && word_translated_range);')
        lsu = lsu.replace('&& !memory_request_bits_refillSize);', '&& !memory_request_bits_refillSize && word_legal_request && word_translated_range);')
        events = r'''
      assert(translation_request_valid == (word_owned && !word_done && !word_translation_sent));
      assert(translation_response_ready == (word_owned && word_translation_sent && !word_translated));
      if (translation_request_valid) begin
        assert(translation_request_bits_address == word_address && translation_request_bits_privilege == word_privilege);
        assert(!translation_request_bits_fetch && translation_request_bits_write == word_store);
        if (translation_request_ready) word_translation_sent <= 1;
      end
      assume(!translation_response_valid || (word_translation_sent && !word_translated) || (translation_request_valid && translation_request_ready));
      if (translation_response_valid && translation_response_ready) begin
        word_translated <= 1; word_physical_address <= translation_response_bits_address;
        word_pair <= word_pair && translation_response_bits_address == word_reserved_address;
        word_done <= translation_response_bits_fault || !word_permitted;
        word_fault <= translation_response_bits_fault || !word_permitted;
        word_cause <= translation_response_bits_fault ? translation_response_bits_cause : word_store ? 7 : 5;
        word_tval <= word_address;
      end
      if (memory_request_valid) assert(word_translated && !word_fault);
      if ($past(!reset && translation_request_valid && !translation_request_ready)) begin
        assert(translation_request_valid);
        assert($stable({translation_request_bits_address, translation_request_bits_privilege, translation_request_bits_fetch, translation_request_bits_write}));
      end
      if ($past(!reset && translation_response_valid && !translation_response_ready)) begin
        assume(translation_response_valid);
        assume($stable({translation_response_bits_address, translation_response_bits_fault, translation_response_bits_cause}));
      end
      cover(memory_request_valid && word_legal_request && word_translated_range && word_physical_address != word_address && privilege == 3);
      cover(output_valid && word_legal_request && word_translated && word_translated_range && word_fault && !word_sent);
      cover(output_valid && word_legal_request && word_translated && word_fault && !word_sent && word_cause == (word_store ? 15 : 13) && output_bits_instruction_tval == word_address);
      cover(translation_request_valid && word_legal_request && !translation_request_ready && privilege == 3);
'''
        lsu = lsu.replace('      if (input_valid && input_ready) begin', events + '      if (input_valid && input_ready) begin', 1)
    if data_line:
        lsu = line_lsu_contract(lsu, parameters)
    return [('WordDecode', decode, 'assign output_bits_usesRs2 =', "assign output_bits_usesRs2 = 1'h0 &"),
            ('WordExecute', execute, 'assign output_bits_unsignedLoad =', "assign output_bits_unsignedLoad = 1'h0 &"),
            ('Lsu', lsu, 'assign memory_request_bits_size =', "assign memory_request_bits_size = 3'h3 |")]


def lsu_reads_case(parameters):
    assert parameters.get('loadQueueEntries') == 2 and not parameters.get('pmpEntries') and parameters.get('virtualAddressBits') == 0
    ranges = ' || '.join(f"(input_bits_address >= 64'd{int(r['base'])} && input_bits_address <= 64'd{int(r['base']) + int(r['size']) - 8})"
                         for r in parameters['memoryRegions'] if r['readable'] and not r['device'] and int(r['size']) >= 8)
    body = r'''
  reg q_past = 0, q_head = 0, q_tail = 0, q_poison = 0;
  reg [1:0] q_live = 0, q_pending = 0, q_done = 0, q_killed = 0, q_offered = 0, q_fault = 0, q_value;
  reg [63:0] q_pc[2], q_address[2];
  reg [7:0] q_tag[2];
  (* anyconst *) reg [5:0] q_bit;
  wire q_in = input_valid && input_ready;
  wire q_out = output_valid && output_ready;
  wire q_request = memory_request_valid && memory_request_ready;
  wire q_response = memory_response_valid && memory_response_ready;
  wire q_known = memory_response_bits_tag < 2 && q_pending[memory_response_bits_tag[0]];
  always @* begin
    assume(input_bits_load && !input_bits_store && !input_bits_atomic && !input_bits_instruction_fault);
    assume(input_bits_memorySize == 3 && !input_bits_address[2:0] && (RANGES));
    assume(!memory_response_valid || q_pending != 0);
  end
  always @(posedge clock) begin
    q_past <= 1;
    if (!q_past) assume(reset); else assume(!reset);
    if (reset) begin
      q_head <= 0; q_tail <= 0; q_poison <= 0;
      q_live <= 0; q_pending <= 0; q_done <= 0; q_killed <= 0; q_offered <= 0; q_fault <= 0;
    end else begin
      if ($past(!reset && memory_response_valid && !memory_response_ready)) begin
        assume(memory_response_valid);
        assume($stable({memory_response_bits_data, memory_response_bits_fault, memory_response_bits_tag, memory_response_bits_last}));
      end
      if ($past(!reset && memory_request_valid && !memory_request_ready)) begin
        assert(memory_request_valid);
        assert($stable({memory_request_bits_address, memory_request_bits_data, memory_request_bits_size, memory_request_bits_mask,
          memory_request_bits_tag, memory_request_bits_write, memory_request_bits_atomic, memory_request_bits_atomicOperation,
          memory_request_bits_cacheOperation, memory_request_bits_privileged, memory_request_bits_refillSize, memory_request_bits_scEligible}));
      end
      if ($past(!reset && output_valid && !output_ready)) begin
        assert(output_valid);
        assert($stable({output_bits_value, output_bits_address, output_bits_instruction_pc, output_bits_instruction_tag,
          output_bits_instruction_fault, output_bits_instruction_cause, output_bits_instruction_tval}));
      end
      if (q_poison || cancel) assert(!q_in);
      if (memory_request_valid) begin
        assert(memory_request_bits_tag < 2 && q_live[memory_request_bits_tag[0]] && !q_pending[memory_request_bits_tag[0]]);
        assert(!memory_request_bits_write && !memory_request_bits_atomic && !memory_request_bits_fetch && memory_request_bits_size == 3);
        assert(memory_request_bits_address == q_address[memory_request_bits_tag[0]]);
        if (q_killed[memory_request_bits_tag[0]] || cancel || q_poison) assert(q_offered[memory_request_bits_tag[0]]);
      end
      if (output_valid) begin
        assert(q_live[q_head]);
        assert(q_done[q_head] || (!q_pending[q_head] && !q_offered[q_head] && (q_killed[q_head] || q_poison)));
        assert(output_bits_instruction_pc == q_pc[q_head] && output_bits_instruction_tag == q_tag[q_head]);
        assert(output_bits_address == q_address[q_head]);
        if (!q_killed[q_head]) begin
          assert(output_bits_instruction_fault == (q_done[q_head] ? q_fault[q_head] : q_poison));
          if (!output_bits_instruction_fault) assert(output_bits_value[q_bit] == q_value[q_head]);
        end
      end
      for (integer n = 0; n < 2; n++) begin
        if (q_out && q_head == n) begin q_live[n] <= 0; q_done[n] <= 0; q_offered[n] <= 0; end
        if (cancel && q_live[n]) q_killed[n] <= 1;
        if (q_in && q_tail == n) begin
          assert(!q_live[n]); q_live[n] <= 1; q_done[n] <= 0; q_killed[n] <= 0; q_offered[n] <= 0; q_fault[n] <= 0;
          q_pc[n] <= input_bits_instruction_pc; q_tag[n] <= input_bits_instruction_tag; q_address[n] <= input_bits_address;
        end
        if (memory_request_valid && !memory_request_ready && memory_request_bits_tag == n) q_offered[n] <= 1;
        if (q_request && memory_request_bits_tag == n) begin
          assert(q_live[n] && !q_pending[n] && !q_done[n]); q_pending[n] <= 1;
        end
        if (q_response && q_known && memory_response_bits_tag == n) begin
          q_value[n] <= memory_response_bits_data[q_bit];
          q_fault[n] <= q_fault[n] || memory_response_bits_fault || !memory_response_bits_last || q_poison;
          if (memory_response_bits_last) begin q_pending[n] <= 0; q_done[n] <= 1; q_offered[n] <= 0; end
        end
      end
      if (q_in) q_tail <= !q_tail;
      if (q_out) q_head <= !q_head;
      if (q_response && !q_known) q_poison <= 1;
      cover(q_pending == 3);
      cover(q_pending[q_head] && q_done[!q_head]);
      cover(q_pending == 3 && cancel);
      cover(q_poison && q_pending == 0 && q_live == 0);
    end
  end
'''.replace('RANGES', ranges)
    return 'LsuReads', body, 'assign memory_request_bits_tag =', "assign memory_request_bits_tag = 8'h1 ^"


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


def instance_ports(source, pattern=r'instructions_\d+x32', instance=r'\w+'):
    arrays = re.findall(pattern + r'\s+' + instance + r'\s*\((.*?)\n  \);', source, re.S)
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
    returning = f'''      end else if (state == 5) begin
        assert(translation_response_valid && translation_response_ready && !translation_response_bits_fault && {full});
        assert(memory_request_bits_address == {candidate} && memory_request_bits_tag == accepted_tag && memory_request_bits_size == {bits+2});
''' if translated else ''
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
        assert(request_valid && {full}{' && translation_response_valid && translation_request_ready && !translation_response_bits_fault' if translated else ''});
        assert(memory_request_bits_address == {candidate} && memory_request_bits_tag == request_bits_tag && memory_request_bits_size == {bits+2});
{returning}      end else begin
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
      assert(formal_fetch_pmp_privilege == {'(accepting ? privilege : wide_privilege)' if translated else 'privilege'});
    end
    if (state == 6) assert(formal_fetch_pmp_address == {held} && formal_fetch_pmp_size == 2 && formal_fetch_pmp_privilege == wide_privilege);
  end
'''
    if translated:
        body += '''  reg translation_owned;
  always @(posedge clock) if (reset) translation_owned <= 0;
  else begin
    assert(translation_owned == (state == 5));
    if (state == 5) assert(wholeBlock && !wide_scalar);
    if (state == 1 || state == 2 || state == 6) assert(physicalAddress == wide_physical && wide_physical[11:0] == accepted_pc[11:0]);
    if (translation_response_valid && !translation_response_bits_fault) assume(translation_response_bits_address[11:0] == (translation_owned ? accepted_pc[11:0] : request_bits_pc[11:0]));
    assume(!translation_response_valid || translation_owned || (translation_request_valid && translation_request_ready));
    if ($past(!reset && translation_response_valid && !translation_response_ready)) begin
      assume(translation_response_valid); assume($stable({translation_response_bits_address, translation_response_bits_fault, translation_response_bits_cause}));
    end
    if (translation_request_valid && translation_request_ready) begin assert(!translation_owned); translation_owned <= 1; end
    if (translation_response_valid && translation_response_ready) translation_owned <= 0;
  end
'''
    body = re.sub(r'\bmemory_(request|response)(?:_bits_\w+|_valid|_ready)\b', lambda m: 'FORMAL_FETCH_CACHE_' + m[0].replace('memory_', 'upstream_', 1), body)
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


def writeback_cache_case(parameters):
    index = (parameters['dCacheBytes'] // 64 - 1).bit_length()
    lines = parameters['dCacheBytes'] // 64
    body = f'''
  reg wb_past = 0, wb_probe_owned, wb_lookup, wb_sampling, wb_matched, wb_was_dirty;
  reg wb_bus, wb_main_lookup;
  reg [1:0] wb_operation;
  reg [2:0] wb_size, wb_word;
  reg [7:0] wb_tag, wb_frame_mask, wb_old_mask, wb_store_mask;
  reg [63:0] wb_address, wb_frame_data, wb_store_address, wb_store_data, wb_old_data, wb_probe_address;
  reg wb_invalidate;
  wire wb_probe_accept = probe_request_valid && probe_request_ready;
  wire wb_frame_accept = probe_response_valid && probe_response_ready;
  wire wb_final = wb_frame_accept && probe_response_bits_last;
  wire [{index-1}:0] wb_index = wb_probe_address[{index+5}:6];
  wire [{index+2}:0] wb_sector = {{wb_index, wb_word}};
  wire wb_native_probe_read = wb_probe_owned && FORMAL_DATA_R0_en;
  wire wb_collision = wb_final && wb_matched && wb_invalidate && wb_index == wb_store_address[{index+5}:6];
  wire wb_reply = downstream_response_valid && downstream_response_ready;
  wire wb_error = downstream_response_bits_fault || downstream_response_bits_tag != wb_tag;
  wire wb_store_commit = wb_reply && wb_operation == 1 && !wb_error && !fault && !invalidated && !wb_collision;
  wire [{lines-1}:0] wb_clear_mask = (wb_final && wb_matched) ? ({lines}'d1 << wb_index) : 0;
  wire [{lines-1}:0] wb_set_mask = wb_store_commit ? ({lines}'d1 << wb_address[{index+5}:6]) : 0;
  wire [7:0] wb_access_mask = wb_store_mask << wb_store_address[2:0];
  wire [63:0] wb_store_value;
  for (genvar byte_index = 0; byte_index < 8; byte_index = byte_index + 1) begin
    assign wb_store_value[8 * byte_index +: 8] = byte_index >= wb_store_address[2:0] &&
      wb_store_mask[byte_index - wb_store_address[2:0]] ? wb_store_data[8 * (byte_index - wb_store_address[2:0]) +: 8] : wb_old_data[8 * byte_index +: 8];
  end
  always @(posedge clock) begin
    wb_past <= 1;
    if (!wb_past) assume(reset); else assume(!reset);
    if (reset) begin
      wb_probe_owned <= 0; wb_lookup <= 0; wb_sampling <= 0; wb_bus <= 0; wb_main_lookup <= 0;
    end else begin
      assume(!upstream_request_valid || (upstream_request_bits_cacheOperation == 0 && upstream_request_bits_size <= 3));
      assume(!downstream_response_valid || wb_bus);
      if (downstream_response_valid && (wb_operation == 1 || (wb_operation == 0 && wb_size <= 3))) assume(downstream_response_bits_last);
      if ($past(!reset && downstream_response_valid && !downstream_response_ready)) begin
        assume(downstream_response_valid);
        assume($stable({{downstream_response_bits_data, downstream_response_bits_fault, downstream_response_bits_tag, downstream_response_bits_last}}));
      end
      if ($past(!reset && probe_request_valid && !probe_request_ready)) begin
        assume(probe_request_valid && $stable({{probe_request_bits_address, probe_request_bits_invalidate}}));
      end
      assert(wb_probe_owned == (probeState != 0));
      assert(wb_lookup == (probeState == 1) && wb_sampling == (probeState == 3));
      if (wb_probe_owned && !wb_lookup) begin
        assert(probeWord == wb_word && dirtyLines[wb_index] == wb_was_dirty);
        if (probeState == 4) assert(probeData == wb_frame_data && probeMask == wb_frame_mask);
      end
      assert(probeState <= 4 && state <= 5);
      assert(wb_bus == (state == 3 || state == 5));
      assert(state != 5 || {int(parameters.get('dCacheRefillBytes', 8) == 64)});
      if (wb_bus) begin
        assert(wb_operation == downstream_request_bits_cacheOperation && wb_size == downstream_request_bits_size);
        assert(wb_address == downstream_request_bits_address && wb_tag == downstream_request_bits_tag);
      end
      assert(wb_main_lookup == (state == 1));
      if (state != 0) begin
        assert(request_cacheOperation == 0 && request_size <= 3);
        assert(request_address == wb_store_address && request_data == wb_store_data && request_mask == wb_store_mask);
      end
      if (state == 5) assert({"line && !acquiring && !releasing" if parameters.get('dCacheRefillBytes', 8) == 64 else "1'b0"});
      if (state == 2 || state == 3 || state == 5) begin
        assert(acquiring == storeHit);
        if (acquiring) begin
          assert(request_write && !expanded && !releasing && !{"line" if parameters.get('dCacheRefillBytes', 8) == 64 else "1'b0"});
          assert(data == wb_old_data && storedDirty == wb_old_mask);
        end
      end
      wb_lookup <= wb_probe_accept;
      wb_sampling <= wb_native_probe_read;
      wb_main_lookup <= upstream_request_valid && upstream_request_ready;
      if (upstream_request_valid && upstream_request_ready) begin
        wb_store_address <= upstream_request_bits_address; wb_store_data <= upstream_request_bits_data;
        wb_store_mask <= upstream_request_bits_mask;
        assert(!wb_probe_owned && !wb_probe_accept);
      end
      if (wb_main_lookup) begin wb_old_data <= FORMAL_DATA_R0_data; wb_old_mask <= FORMAL_DIRTY_R0_data; end
      if (downstream_request_valid && downstream_request_ready) begin
        assert(!wb_bus); wb_bus <= 1;
        wb_operation <= downstream_request_bits_cacheOperation; wb_size <= downstream_request_bits_size;
        wb_address <= downstream_request_bits_address; wb_tag <= downstream_request_bits_tag;
      end
      if (wb_reply && downstream_response_bits_last) wb_bus <= 0;
      if (wb_probe_accept) begin
        assert(!wb_probe_owned && !wb_reply);
        wb_probe_owned <= 1; wb_probe_address <= probe_request_bits_address;
        wb_invalidate <= probe_request_bits_invalidate; wb_word <= 0;
        assert(FORMAL_TAG_R0_en && FORMAL_TAG_R0_addr == probe_request_bits_address[{index+5}:6]);
      end
      if (wb_probe_owned) begin
        assert(probeRequest_address == wb_probe_address && probeRequest_invalidate == wb_invalidate);
        assert(!upstream_request_ready && !downstream_response_ready);
        assert(!FORMAL_DATA_W0_en && !FORMAL_TAG_W0_en);
      end
      if (wb_lookup) begin
        wb_matched <= FORMAL_TAG_R0_data == (wb_probe_address >> {index+6}) &&
          ((valid >> (wb_index * 8)) & 8'hff) != 0;
        wb_was_dirty <= dirtyLines[wb_index];
        wb_frame_data <= 0; wb_frame_mask <= 0;
      end
      if (wb_probe_owned && !wb_lookup) assert(probeMatch == wb_matched);
      if (wb_native_probe_read) begin
        assert(FORMAL_DATA_R0_addr == wb_sector && FORMAL_DIRTY_R0_en && FORMAL_DIRTY_R0_addr == wb_sector);
      end
      if (wb_sampling) begin
        wb_frame_data <= FORMAL_DATA_R0_data;
        wb_frame_mask <= valid[wb_sector] ? FORMAL_DIRTY_R0_data : 0;
      end
      if (probe_response_valid) begin
        assert(wb_probe_owned && !wb_lookup && !wb_sampling);
        assert(probe_response_bits_word == wb_word && probe_response_bits_data == wb_frame_data && probe_response_bits_mask == wb_frame_mask);
        assert(probe_response_bits_last == (!wb_matched || !wb_was_dirty || wb_word == 7));
      end
      if (wb_frame_accept) begin
        if (probe_response_bits_last) wb_probe_owned <= 0;
        else wb_word <= wb_word + 1;
        if (wb_frame_mask != 0) begin
          assert(FORMAL_DIRTY_W0_en && FORMAL_DIRTY_W0_addr == wb_sector && FORMAL_DIRTY_W0_data == 0);
        end
      end
      if (FORMAL_DIRTY_W0_en && !FORMAL_DATA_W0_en) begin
        assert(wb_frame_accept && wb_frame_mask != 0 && FORMAL_DIRTY_W0_addr == wb_sector && FORMAL_DIRTY_W0_data == 0);
      end
      if (wb_reply && wb_operation == 1) begin
        assert(FORMAL_DATA_W0_en == (!wb_error && !fault && !invalidated && !wb_collision));
        if (wb_error) assert(!FORMAL_DATA_W0_en && !FORMAL_DIRTY_W0_en);
        if (FORMAL_DATA_W0_en) begin
          assert(FORMAL_DATA_W0_addr == wb_store_address[{index+5}:3] && FORMAL_DATA_W0_data == wb_store_value);
          assert(FORMAL_DIRTY_W0_en && FORMAL_DIRTY_W0_addr == FORMAL_DATA_W0_addr && FORMAL_DIRTY_W0_data == (wb_old_mask | wb_access_mask));
        end
      end
      if (wb_past && $past(!reset)) begin
        assert(($past(dirtyLines) & ~dirtyLines & ~$past(wb_clear_mask)) == 0);
        assert((dirtyLines & ~$past(dirtyLines) & ~$past(wb_set_mask)) == 0);
        if ($past(probe_response_valid && !probe_response_ready))
          assert(probe_response_valid && $stable({{probe_response_bits_data, probe_response_bits_mask, probe_response_bits_word, probe_response_bits_last}}));
      end
      cover(probe_response_valid && probe_response_bits_mask != 0 && !probe_response_ready);
      cover(wb_final && wb_matched && wb_was_dirty && wb_invalidate && state == 3);
      cover(wb_reply && wb_operation == 1 && wb_error);
      cover(wb_reply && wb_operation == 2 && !wb_error);
    end
  end
'''
    return ('DataCacheWriteback', body, 'assign probe_response_valid =', "assign probe_response_valid = 1'h1 |")


def writeback_storage_case(parameters):
    sector = (parameters['dCacheBytes'] // 8 - 1).bit_length()
    tag_bits = parameters['physicalAddressBits'] - sector - 3
    ranges = ' || '.join(f"((upstream_request_bits_address & ~64'd7) >= 64'h{int(r['base']):x} && (upstream_request_bits_address & ~64'd7) <= 64'h{int(r['base'])+int(r['size'])-8:x})"
                         for r in parameters['memoryRegions'] if r.get('dataCacheable') and r['readable'] and not r['device'] and int(r['size']) >= 8) or '0'
    shapes = []
    for size in range(4):
        count = 1 << size
        writable = ' || '.join(f"(upstream_request_bits_address >= 64'h{int(r['base']):x} && upstream_request_bits_address <= 64'h{int(r['base'])+int(r['size'])-count:x})"
                              for r in parameters['memoryRegions'] if r['writable'] and int(r['size']) >= count) or '0'
        shapes.append(f"(upstream_request_bits_size == {size} && (upstream_request_bits_address & 64'd{count-1}) == 0 && (upstream_request_bits_mask & 8'h{255 ^ ((1 << count)-1):x}) == 0 && ({writable}))")
    legal = 'upstream_request_bits_cacheOperation == 0 && upstream_request_bits_write && !upstream_request_bits_fetch && !upstream_request_bits_atomic && upstream_request_bits_mask != 0 && (' + ranges + ') && (' + ' || '.join(shapes) + ')'
    line_invariants = ''
    if parameters.get('dCacheRefillBytes', 8) == 64:
        line_ranges = ' || '.join(f"((request_address & ~64'd63) >= 64'h{int(r['base']):x} && (request_address & ~64'd63) <= 64'h{int(r['base'])+int(r['size'])-64:x})"
                                 for r in parameters['memoryRegions'] if r.get('dataCacheable') and r['readable'] and not r['device'] and int(r['size']) >= 64) or '0'
        line_invariants = f'''
      if (line && state >= 2) begin
        AUTH_SHAPE(!request_write && !request_fetch && !request_atomic && request_refillSize == 6 && ({line_ranges}));
        if (releasing) AUTH_SHAPE(beat == 0);
        if (!releasing && !fault && request_address[{sector+2}:6] == auth_watched[{sector-1}:3] && beat > auth_watched[2:0])
          AUTH_BYTES(auth_native_dirty == 0);
      end
'''
    return f'''
  (* anyconst *) reg [{sector-1}:0] auth_watched;
  wire [7:0] auth_native_dirty;
  wire [{tag_bits-1}:0] auth_native_tag;
  wire [63:0] auth_native_address = {{auth_native_tag, auth_watched, 3'b0}};
  reg [7:0] auth_mask;
  reg [63:0] auth_address;
  reg auth_input;
  wire auth_input_legal = {legal};
  wire auth_request_legal = {legal.replace('upstream_request_bits_', 'request_')};
  wire auth_write = FORMAL_DATA_W0_en && FORMAL_DATA_W0_addr == auth_watched;
  wire [63:0] auth_frame_address = {{wb_probe_address[63:6], probe_response_bits_word, 3'b0}};
  always @(posedge clock) begin
    if (reset) begin auth_mask <= 0; auth_input <= 0; end
    else begin
      if (upstream_request_valid && upstream_request_ready) auth_input <= auth_input_legal;
      if (state != 0) AUTH_SHAPE(auth_input == auth_request_legal);
{line_invariants}
      if (state >= 2 && sameTag && wb_store_address[{sector+2}:6] == auth_watched[{sector-1}:3])
        AUTH_SHAPE(auth_native_tag == wb_store_address[{parameters['physicalAddressBits']-1}:{sector+3}]);
      if (state >= 2 && acquiring && wb_store_address[{sector+2}:3] == auth_watched) begin
        AUTH_SHAPE(auth_input && auth_native_address == {{wb_store_address[63:3], 3'b0}});
      end
      if (wb_probe_owned && !wb_lookup && wb_matched && wb_index == auth_watched[{sector-1}:3])
        AUTH_SHAPE(wb_probe_address[63:6] == auth_native_address[63:6]);
      if (auth_write) begin
        if (wb_store_commit) begin
          AUTH_SHAPE(auth_input);
          auth_mask <= auth_mask | wb_access_mask;
          auth_address <= {{wb_store_address[63:3], 3'b0}};
        end else auth_mask <= 0;
      end
      if (valid[auth_watched] && auth_native_dirty != 0) begin
        AUTH_BYTES((auth_native_dirty & ~auth_mask) == 0);
        AUTH_BYTES(auth_native_address == auth_address);
      end
      if (state >= 2 && acquiring && wb_store_address[{sector+2}:3] == auth_watched && storedDirty != 0) begin
        AUTH_BYTES((storedDirty & ~auth_mask) == 0);
        AUTH_BYTES({{wb_store_address[63:3], 3'b0}} == auth_address);
      end
      if (probe_response_valid && wb_sector == auth_watched && probe_response_bits_mask != 0) begin
        AUTH_FRAME((probe_response_bits_mask & ~auth_mask) == 0);
        AUTH_FRAME(auth_frame_address == auth_address);
      end
      cover(probe_response_valid && wb_sector == auth_watched && probe_response_bits_mask != 0 && auth_mask != 0);
    end
  end
'''


def watched_memory_model(source):
    address = int(re.search(r'input\s+\[(\d+):0\]\s+R0_addr', source)[1])
    width = int(re.search(r'output\s+\[(\d+):0\]\s+R0_data', source)[1])
    return header(source).replace(');', f', input [{address}:0] formal_watch, output [{width}:0] formal_value\n);', 1) + f'''
  reg [{width}:0] value;
  reg [{address}:0] read_address;
  reg read_enabled;
  (* anyseq *) reg [{width}:0] arbitrary_read;
  always @(posedge R0_clk) begin read_address <= R0_addr; read_enabled <= R0_en; end
  always @(posedge W0_clk) if (W0_en && W0_addr == formal_watch) value <= W0_data;
  assign formal_value = value;
  assign R0_data = read_enabled && read_address == formal_watch ? value : arbitrary_read;
endmodule
'''


def data_cache_case(parameters):
    index = (parameters['dCacheBytes'] // 64 - 1).bit_length()
    sector = index + 3
    data_line = parameters.get('dCacheRefillBytes', 8) == 64
    fields = ('address', 'data', 'size', 'mask', 'tag', 'write', 'fetch', 'privileged', 'atomic', 'atomicOperation', 'scEligible', 'refillSize')
    payload = lambda prefix: '{' + ', '.join(prefix + '_' + field for field in fields) + '}'
    ranges = ' || '.join(f"((upstream_request_bits_address & ~64'd7) >= 64'h{int(r['base']):x} && (upstream_request_bits_address & ~64'd7) <= 64'h{int(r['base'])+int(r['size'])-8:x})"
                         for r in parameters['memoryRegions'] if r.get('dataCacheable') and r['readable'] and not r['device'] and int(r['size']) >= 8)
    line_ranges = ' || '.join(f"((upstream_request_bits_address & ~64'd63) >= 64'h{int(r['base']):x} && (upstream_request_bits_address & ~64'd63) <= 64'h{int(r['base'])+int(r['size'])-64:x})"
                         for r in parameters['memoryRegions'] if r.get('dataCacheable') and r['readable'] and not r['device'] and int(r['size']) >= 64)
    forwarded = '\n'.join(f"        assert(downstream_request_bits_{field} == " +
        ("(cache_line ? (cache_address & ~64'd63) : cache_expanded ? (cache_address & ~64'd7) : cache_address)" if field == 'address' else
         "(cache_line ? 3'd6 : cache_expanded ? 3'd3 : cache_size)" if field == 'size' else
         "(cache_retried ? 0 : cache_line ? 6 : cache_expanded ? 3 : request_refillSize)" if field == 'refillSize' else f"request_{field}") + ");"
        for field in fields)
    current_ranges = ranges.replace('upstream_request_bits_address', 'request_address')
    writable = ' || '.join(f"(upstream_request_bits_address >= 64'h{int(r['base']):x} && upstream_request_bits_address <= 64'h{int(r['base'])+int(r['size']):x} - (64'd1 << upstream_request_bits_size))"
                          for r in parameters['memoryRegions'] if r['writable'])
    body = f'''
  wire invalidate_valid = probe_request_valid && probe_request_ready && probe_request_bits_invalidate;
  wire invalidate_ready = probe_request_ready;
  wire [63:0] invalidate_bits = probe_request_bits_address;
  reg cache_probe_owned = 0;
  always @(posedge clock) if (reset) cache_probe_owned <= 0; else begin
    assert(probe_request_ready == (!cache_probe_owned || probe_response_ready));
    assert(probe_response_valid == cache_probe_owned);
    if (probe_response_valid) assert(probe_response_bits_data == 0 && probe_response_bits_mask == 0 && probe_response_bits_word == 0 && probe_response_bits_last);
    if (probe_response_valid && probe_response_ready) cache_probe_owned <= 0;
    if (probe_request_valid && probe_request_ready) cache_probe_owned <= 1;
    if ($past(!reset && probe_request_valid && !probe_request_ready)) begin
      assume(probe_request_valid && $stable({{probe_request_bits_address, probe_request_bits_invalidate}}));
    end
    if (upstream_request_valid) assume(upstream_request_bits_cacheOperation == 0);
  end
  reg cache_past = 0, cache_owned, cache_bus, cache_sent, cache_finished, cache_killed, cache_eligible;
  reg [159:0] cache_request;
  reg [63:0] cache_address, cache_result;
  reg [7:0] cache_tag;
  reg cache_fault, cache_same_tag, cache_expanded, cache_retried;
  reg cache_line, cache_stream_fault;
  reg cache_store, cache_store_hit;
  reg [63:0] cache_store_word;
  reg [3:0] cache_beats;
  reg [63:0] cache_line_result;
  reg [2:0] cache_size;
  (* anyconst *) reg [{sector-1}:0] cache_watched;
  wire cache_accept = upstream_request_valid && upstream_request_ready;
  wire cache_reply = downstream_response_valid && downstream_response_ready;
  wire cache_sample = state == 1 && cache_eligible && valid[cache_address[{index+5}:3]] &&
    _dataTags_ext_R0_data == cache_address[{parameters["physicalAddressBits"]-1}:{index+6}] && !cache_killed && !cache_collision;
  wire cache_invalidate = invalidate_valid && invalidate_ready;
  wire cache_collision = cache_invalidate && invalidate_bits[{index+5}:6] == cache_address[{index+5}:6];
  wire cache_error = downstream_response_bits_fault || downstream_response_bits_tag != cache_tag;
  wire cache_line_error = cache_error || downstream_response_bits_last != (cache_beats == 7) || cache_beats >= 8;
  wire cache_word_write = cache_reply && !cache_line && cache_eligible && (cache_size == 3 || cache_expanded) &&
    !cache_retried && !cache_killed && !cache_collision && !cache_error;
  wire cache_line_write = cache_reply && cache_line && cache_beats < 8 && !cache_stream_fault &&
    !cache_killed && !cache_collision && !cache_line_error;
  wire cache_publish = cache_line_write && cache_beats == 7 && downstream_response_bits_last;
  wire cache_store_write = cache_reply && cache_store_hit && !cache_error && !cache_killed && !cache_collision;
  wire cache_store_failed = cache_reply && request_write && cache_error;
  wire [63:0] cache_store_mask;
  for (genvar byte_index = 0; byte_index < 8; byte_index = byte_index + 1) begin
    assign cache_store_mask[8 * byte_index +: 8] = byte_index >= cache_address[2:0] &&
      request_mask[byte_index - cache_address[2:0]] ? 8'hff : 8'h00;
  end
  wire [63:0] cache_store_data = (cache_store_word & ~cache_store_mask) |
    ((request_data << (8 * cache_address[2:0])) & cache_store_mask);
  wire cache_start_line = state == 1 && !cache_sample && cache_line;
  wire [63:0] cache_mask = cache_size == 0 ? 64'hff : cache_size == 1 ? 64'hffff : cache_size == 2 ? 64'hffffffff : 64'hffffffffffffffff;
  wire [63:0] cache_hit_data = (CACHE_READ >> (8 * cache_address[2:0])) & cache_mask;
  wire [63:0] cache_fill_data = (downstream_response_bits_data >> (8 * cache_address[2:0])) & cache_mask;
  wire cache_clear_watched = (cache_invalidate && invalidate_bits[{index+5}:6] == cache_watched[{sector-1}:3]) ||
    (cache_store_failed && cache_address[{index+5}:6] == cache_watched[{sector-1}:3]);
  wire cache_expected_valid = !cache_clear_watched &&
    ((cache_publish && cache_address[{index+5}:6] == cache_watched[{sector-1}:3]) ||
     (cache_word_write && cache_address[{index+5}:3] == cache_watched) ||
      (valid[cache_watched] && !((cache_start_line || (cache_word_write && !cache_same_tag)) && cache_address[{index+5}:6] == cache_watched[{sector-1}:3])));
  wire cache_input_eligible = !upstream_request_bits_write && !upstream_request_bits_fetch && !upstream_request_bits_atomic &&
    upstream_request_bits_size <= 3 && (upstream_request_bits_address & ((64'd1 << upstream_request_bits_size)-1)) == 0 && ({ranges or '0'});
  wire cache_input_store = upstream_request_bits_write && !upstream_request_bits_fetch && !upstream_request_bits_atomic &&
    upstream_request_bits_size <= 3 && (upstream_request_bits_address & ((64'd1 << upstream_request_bits_size)-1)) == 0 &&
    upstream_request_bits_mask != 0 && (upstream_request_bits_mask >> (1 << upstream_request_bits_size)) == 0 &&
    ({ranges or '0'}) && ({writable or '0'});
  wire cache_input_line = {int(data_line)} && cache_input_eligible && upstream_request_bits_refillSize == 6 && ({line_ranges or '0'});
  wire cache_request_line = {int(data_line)} && cache_eligible && request_refillSize == 6 && ({line_ranges.replace('upstream_request_bits_address', 'request_address') or '0'});
  always @(posedge clock) begin
    cache_past <= 1;
    if (!cache_past) assume(reset); else assume(!reset);
    if (reset) begin
      cache_owned <= 0; cache_bus <= 0; cache_sent <= 0; cache_finished <= 0; cache_killed <= 0;
      cache_line <= 0; cache_beats <= 0; cache_stream_fault <= 0;
    end else begin
      assume(!downstream_response_valid || cache_bus);
      if ($past(!reset && downstream_response_valid && !downstream_response_ready)) begin
        assume(downstream_response_valid);
        assume($stable({{downstream_response_bits_data, downstream_response_bits_fault, downstream_response_bits_tag, downstream_response_bits_last}}));
      end
      assert(state <= {5 if data_line else 4} && cache_owned == (state != 0) && cache_bus == (state == 3 || state == 5));
      assert(cache_finished == (state == 4));
      assert(upstream_response_valid == (cache_finished || cache_sample));
      if (cache_owned && cache_retried) assert(cache_eligible && !cache_store);
      if (cache_owned) begin
        assert(request_cacheOperation == 0);
        assert({payload('request')} == cache_request);
        assert(request_address == cache_address && request_tag == cache_tag && request_size == cache_size);
        assert(cache_store == (request_write && !request_fetch && !request_atomic && request_size <= 3 &&
          (request_address & ((64'd1 << request_size)-1)) == 0 && request_mask != 0 && (request_mask >> (1 << request_size)) == 0 &&
          ({current_ranges or '0'}) && ({writable.replace('upstream_request_bits_', 'request_') or '0'})));
        assert(cache_eligible == (!request_write && !request_fetch && !request_atomic && request_size <= 3 &&
          (request_address & ((64'd1 << request_size)-1)) == 0 && ({current_ranges or '0'})));
        if (cache_expanded) assert(cache_eligible && (request_refillSize == 3 || request_refillSize == 6) && cache_size < 3 && !cache_retried);
        if (state != 4) assert(cache_sent == (state == 3 || state == 5));
        assert(invalidated == cache_killed && CACHE_ELIGIBLE == cache_eligible);
        if (cache_collision) cache_killed <= 1;
      end
      if (state == 1) cache_same_tag <= _dataTags_ext_R0_data == cache_address[{parameters['physicalAddressBits']-1}:{index+6}];
      if (state == 1) begin
        cache_store_hit <= cache_store && valid[cache_address[{index+5}:3]] &&
          _dataTags_ext_R0_data == cache_address[{parameters['physicalAddressBits']-1}:{index+6}] && !cache_killed && !cache_collision;
        cache_store_word <= CACHE_READ;
        assert(!fault && !expanded && !cache_retried && cache_line == cache_request_line);
        assert(cache_expanded == (cache_eligible && !cache_line && cache_size < 3 && (request_refillSize == 3 || request_refillSize == 6)));
      end
      if (state >= 2) begin
        assert(sameTag == cache_same_tag && expanded == cache_expanded);
        assert(storeHit == cache_store_hit);
        if (cache_store_hit) assert(cache_store && request_write && !cache_eligible && !cache_line && !cache_expanded);
        if (cache_store_hit && state != 4) assert(data == cache_store_word);
      end
      if (!cache_line && (state == 2 || state == 3)) assert(fault == cache_retried);
      if (downstream_request_valid) begin
        assert(cache_owned && !cache_bus && !cache_sent);
{forwarded}
        if (cache_expanded) assert(cache_eligible && (request_refillSize == 3 || request_refillSize == 6) && cache_size < 3 && !cache_retried);
      end
      if (downstream_request_valid && downstream_request_ready) begin cache_bus <= 1; cache_sent <= 1; end
      if (cache_reply) begin
        assert(cache_owned && cache_bus);
        if (cache_line) begin
          if (cache_beats < 8) cache_beats <= cache_beats + 1;
          cache_stream_fault <= cache_stream_fault || cache_line_error || cache_killed || cache_collision;
          if (cache_beats < 8 && cache_beats == cache_address[5:3]) cache_line_result <= cache_fill_data;
          if (downstream_response_bits_last) begin
            cache_bus <= 0; cache_line <= 0;
            if (cache_stream_fault || cache_line_error || cache_killed || cache_collision) begin
              cache_expanded <= 0; cache_sent <= 0; cache_retried <= 1;
            end else begin
              cache_finished <= 1; cache_fault <= 0;
              cache_result <= cache_beats == cache_address[5:3] ? cache_fill_data : cache_line_result;
            end
          end
        end else begin
          cache_bus <= 0;
          if (cache_expanded && cache_error) begin
            cache_expanded <= 0; cache_sent <= 0; cache_retried <= 1;
          end else begin
            cache_finished <= 1;
            cache_result <= cache_expanded ? cache_fill_data : downstream_response_bits_data;
            cache_fault <= cache_error;
          end
        end
      end
      if (cache_sample) begin
        assert(cache_owned && cache_eligible && !cache_bus && !cache_sent && !cache_killed && !cache_collision);
        assert(valid[cache_address[{index+5}:3]] && _dataTags_ext_R0_data == cache_address[{parameters['physicalAddressBits']-1}:{index+6}]);
        cache_finished <= 1; cache_result <= cache_hit_data; cache_fault <= 0; cache_expanded <= 0; cache_line <= 0;
      end
      assert(filling_0 == (cache_word_write || cache_line_write || cache_store_write));
      assert(CACHE_TAG_WRITE == (cache_word_write || cache_publish));
      if (filling_0) begin
        assert(CACHE_WRITE_ADDRESS == (cache_line ? {{cache_address[{index+5}:6], cache_beats[2:0]}} : cache_address[{index+5}:3]));
        assert(CACHE_WRITE_DATA == (cache_store_write ? cache_store_data : downstream_response_bits_data));
      end
      if (upstream_response_valid) begin
        assert(cache_owned && (cache_finished || cache_sample) && !cache_bus && !downstream_request_valid);
        assert(upstream_response_bits_last);
        assert(upstream_response_bits_tag == cache_tag && upstream_response_bits_fault == (cache_sample ? 0 : cache_fault));
        if (cache_sample || !cache_fault) assert(upstream_response_bits_data == (cache_sample ? cache_hit_data : cache_result));
        if (upstream_response_ready) begin cache_owned <= 0; cache_finished <= 0; end
      end
      if (cache_accept) begin
        assert(!cache_owned || (upstream_response_valid && upstream_response_ready));
        cache_owned <= 1; cache_request <= {payload('upstream_request_bits')};
        cache_address <= upstream_request_bits_address; cache_tag <= upstream_request_bits_tag;
        cache_size <= upstream_request_bits_size; cache_eligible <= cache_input_eligible;
        cache_store <= cache_input_store;
        cache_expanded <= cache_input_eligible && !cache_input_line && upstream_request_bits_size < 3 && (upstream_request_bits_refillSize == 3 || upstream_request_bits_refillSize == 6);
        cache_line <= cache_input_line; cache_beats <= 0; cache_stream_fault <= 0;
        cache_bus <= 0; cache_sent <= 0; cache_finished <= 0; cache_retried <= 0;
        cache_killed <= cache_invalidate && invalidate_bits[{index+5}:6] == upstream_request_bits_address[{index+5}:6];
      end
      if ($past(!reset)) begin
        assert(valid[cache_watched] == $past(cache_expected_valid));
        if ($past(cache_invalidate && invalidate_bits[{index+5}:6] == cache_watched[{sector-1}:3])) assert(!valid[cache_watched]);
        if (valid[cache_watched] && !$past(valid[cache_watched]))
          assert($past((cache_word_write && cache_address[{index+5}:3] == cache_watched) ||
            (cache_publish && cache_address[{index+5}:6] == cache_watched[{sector-1}:3])));
        if ($past(downstream_request_valid && !downstream_request_ready)) begin
          assert(downstream_request_valid); assert($stable({payload('downstream_request_bits')}));
        end
        if ($past(upstream_response_valid && !upstream_response_ready)) begin
          assert(upstream_response_valid);
          assert($stable({{upstream_response_bits_data, upstream_response_bits_fault, upstream_response_bits_tag}}));
        end
      end
      cover(cache_sample);
      cover(cache_sample && cache_size < 3);
      cover(cache_sample && $past(!reset && cache_sample && upstream_response_ready));
      cover(cache_reply && cache_expanded && !cache_error);
      cover(upstream_response_valid && cache_retried && !upstream_response_bits_fault);
      cover(cache_accept && upstream_response_valid && upstream_response_ready);
      cover(cache_reply && cache_collision && !cache_error);
      cover(cache_bus && cache_invalidate && !downstream_response_valid);
      cover(downstream_request_valid && !downstream_request_ready && cache_invalidate);
      cover(upstream_response_valid && !upstream_response_ready && cache_invalidate);
      cover(upstream_response_valid && cache_fault);
      cover(cache_reply && !cache_eligible && request_atomic);
      cover(cache_store_write && cache_size < 3);
      cover(cache_reply && cache_store_hit && cache_killed && !cache_error);
      cover(cache_store_failed && cache_store_hit);
    end
  end
'''
    if data_line:
        body += f'''
  always @(posedge clock) if (!reset) begin
    if (state >= 2) assert(line == cache_line);
    if (state == 5) assert(cache_line);
    if (state == 1) assert(!line && beat == 0);
    if (cache_line) begin
      assert(cache_eligible && request_refillSize == 6 && !cache_retried && !cache_expanded && cache_beats <= 8);
      if (state == 1 || state == 2) assert(cache_beats == 0 && !cache_stream_fault);
      if (state >= 2) begin
        assert(fault == cache_stream_fault);
        assert(beat == (cache_beats < 8 ? cache_beats[2:0] : 3'd7));
      end
      if (state == 3) assert(cache_beats < 8);
      if (state == 5) assert(cache_beats == 8 && cache_stream_fault);
      if (cache_beats > cache_address[5:3]) assert(data == cache_line_result);
    end
    cover(cache_publish && cache_address[5:3] == 7);
    cover(cache_publish && cache_address[5:3] == 0);
    cover(cache_reply && cache_line && cache_collision && cache_beats == 7);
    cover(state == 5 && cache_reply && downstream_response_bits_last);
  end
'''
    else:
        body += '  always @(posedge clock) if (!reset) assert(!cache_line);\n'
    return ('DataCache', body, 'assign probe_request_ready =', "assign probe_request_ready = 1'h0 &")


def coherence_case(parameters):
    count = parameters['hartCount']
    fields = ('cacheOperation', 'address', 'data', 'size', 'mask', 'tag', 'write', 'fetch', 'privileged', 'atomic', 'atomicOperation', 'scEligible', 'refillSize')
    payload = lambda prefix: '{' + ', '.join(prefix + '_bits_' + field for field in fields) + '}'
    vector = lambda values: '{' + ', '.join(reversed(values)) + '}'
    ranges = ' || '.join(f"(upstream_request_bits_address >= 64'h{int(r['base']):x} && upstream_request_bits_address < 64'h{int(r['base'])+int(r['size']):x})"
                         for r in parameters['memoryRegions'] if r.get('dataCacheable'))
    release_ranges = ' || '.join(f"(upstream_request_bits_address[63:6] >= 58'd{int(r['base'])//64} && upstream_request_bits_address[63:6] <= 58'd{(int(r['base'])+int(r['size'])-1)//64})"
                                for r in parameters['memoryRegions'] if r.get('dataCacheable') and r['readable'] and not r['device'])
    wb = int(bool(parameters.get('dCacheWriteback')))
    completion_witness = 'cc_synthetic && !cc_fault && cc_retried' if wb else f'cc_coherent && !cc_synthetic && cc_owner == {count-1} && !cc_needed[{count-1}] && !upstream_response_bits_fault'
    targets = vector([f'(upstream_request_bits_cacheOperation == 2 && {wb} ? hartId == {h} : upstream_request_bits_cacheOperation == 1 && {wb} ? hartId != {h} : {wb} || upstream_request_bits_atomic || hartId != {h})' for h in range(count)])
    sent = vector([f'(probe_{h}_request_valid && probe_{h}_request_ready)' for h in range(count)])
    done = vector([f'(probe_{h}_response_valid && probe_{h}_response_ready && probe_{h}_response_bits_last)' for h in range(count)])
    dirty = vector([f'(cc_needed[{h}] && cc_issued[{h}] && !cc_done[{h}] && probe_{h}_response_valid && probe_{h}_response_bits_mask != 0)' for h in range(count)])
    choice = ''.join(f'cc_dirty[{h}] ? 4\'d{h} : ' for h in range(count)) + "4'd0"
    body = memory_case(parameters)[1].split('  always @(posedge clock) begin', 1)[0] + f'''
  reg cc_past = 0, cc_owned, cc_accepted, cc_coherent, cc_synthetic, cc_fault;
  reg cc_bus, cc_bus_writeback, cc_writeback, cc_retried, cc_poisoned;
  reg [{count-1}:0] cc_needed, cc_issued, cc_done;
  reg [161:0] cc_request;
  reg [63:0] cc_address;
  reg [7:0] cc_tag;
  reg [3:0] cc_owner, cc_writeback_owner;
  reg cc_invalidate;
  wire cc_authorized = {wb} && upstream_request_bits_cacheOperation == 2 ? ({release_ranges or '0'}) : ({ranges or '0'}) && m_allowed;
  wire cc_invalid = upstream_request_bits_cacheOperation != 0 &&
    (!{wb} || upstream_request_bits_cacheOperation == 3 || upstream_request_bits_atomic || upstream_request_bits_fetch ||
     (upstream_request_bits_cacheOperation == 1 && !upstream_request_bits_write) ||
     (upstream_request_bits_cacheOperation == 2 && (upstream_request_bits_write || upstream_request_bits_size != 3 || upstream_request_bits_address[5:0] != 0)) || !cc_authorized);
  wire cc_input_coherent = cc_authorized && ({wb} || upstream_request_bits_write);
  wire cc_start = !cc_owned && upstream_request_valid && cc_input_coherent && !cc_invalid;
  wire cc_accept = upstream_request_valid && upstream_request_ready;
  wire cc_reply = downstream_response_valid && downstream_response_ready;
  wire cc_end = upstream_response_valid && upstream_response_ready && upstream_response_bits_last;
  wire cc_error = cc_poisoned || downstream_response_bits_fault || downstream_response_bits_tag != cc_tag || !downstream_response_bits_last;
  wire [{count-1}:0] cc_sent_now = {sent};
  wire [{count-1}:0] cc_done_now = {done};
  wire [{count-1}:0] cc_dirty = {dirty};
  wire [3:0] cc_choice = {choice};
'''
    for field, width in (('data', 64), ('mask', 8), ('word', 3), ('last', 1)):
        select = ''.join(f'cc_writeback_owner == {h} ? probe_{h}_response_bits_{field} : ' for h in range(count - 1)) + f'probe_{count-1}_response_bits_{field}'
        body += f'  wire [{width-1}:0] cc_frame_{field} = {select};\n'
    body += f'''
  always @(posedge clock) begin
    cc_past <= 1;
    if (!cc_past) assume(reset); else assume(!reset);
    if (reset) begin
      cc_owned <= 0; cc_accepted <= 0; cc_bus <= 0; cc_writeback <= 0;
      cc_needed <= 0; cc_issued <= 0; cc_done <= 0; cc_retried <= 0;
      cc_poisoned <= 0;
    end
    else begin
      if ($past(!reset && upstream_request_valid && !upstream_request_ready)) begin
        assume(upstream_request_valid); assume($stable({{{payload('upstream_request')}, hartId}}));
      end
      assume(!downstream_response_valid || cc_bus);
      if ($past(!reset && downstream_response_valid && !downstream_response_ready)) begin
        assume(downstream_response_valid); assume($stable({{downstream_response_bits_data, downstream_response_bits_fault, downstream_response_bits_tag, downstream_response_bits_last}}));
      end
      assert(state <= 6 && cc_owned == (state != 0) && cc_accepted == (state == 5 || state == 6));
      assert(cc_bus == (state == 3 || state == 6));
      assert(cc_writeback == (state == 2 || state == 3));
      if (cc_owned && !cc_accepted) begin
        assert(upstream_request_valid && {payload('upstream_request')} == cc_request && hartId == cc_owner);
        assert(cc_coherent && cc_input_coherent && !cc_invalid && cc_synthetic == (upstream_request_bits_cacheOperation != 0));
        assert(cc_address == upstream_request_bits_address && cc_tag == upstream_request_bits_tag);
        assert(cc_needed == {targets});
        assert(cc_invalidate == (upstream_request_bits_write || upstream_request_bits_atomic || upstream_request_bits_cacheOperation == 2));
      end
      if (cc_owned && cc_coherent) begin
        assert(pending == (cc_needed & ~cc_done) && sent == cc_issued);
        assert((cc_issued & ~cc_needed) == 0 && (cc_done & ~cc_issued) == 0);
        assert(tag == cc_tag);
        assert(!cc_fault);
        if (!cc_writeback) assert(!fault);
        if (cc_accepted) assert(cc_needed == cc_done);
        cc_issued <= cc_issued | cc_sent_now;
        cc_done <= cc_done | cc_done_now;
        if (cc_needed != cc_done) assert(!upstream_request_ready && !upstream_response_valid);
      end
      if (cc_owned && !cc_accepted && !cc_writeback && |cc_dirty) begin
        cc_writeback <= 1; cc_writeback_owner <= cc_choice; cc_poisoned <= 0;
      end
      if (cc_writeback) begin
        assert(cc_owned && cc_coherent && !cc_accepted && cc_writeback_owner == {'0' if count == 1 else 'selected'});
        assert(fault == cc_poisoned);
        assert(cc_writeback_owner < {count} && cc_dirty[cc_writeback_owner] && cc_frame_mask != 0);
      end
      if (cc_bus) assert(cc_bus_writeback == cc_writeback);
      if (downstream_request_valid) begin
        assert(upstream_request_valid && !cc_bus && downstream_request_bits_cacheOperation == 0);
        if (cc_writeback) begin
          assert(downstream_request_bits_write && downstream_request_bits_privileged && !downstream_request_bits_fetch && !downstream_request_bits_atomic);
          assert(downstream_request_bits_size == 3 && downstream_request_bits_refillSize == 0);
          assert(downstream_request_bits_address == ((cc_address & ~64'd63) | (64'd8 * cc_frame_word)));
          assert(downstream_request_bits_data == cc_frame_data && downstream_request_bits_mask == cc_frame_mask && downstream_request_bits_tag == cc_tag);
          assert(!upstream_request_ready);
        end else begin
          assert(!cc_owned || (!cc_accepted && !cc_synthetic && cc_needed == cc_done));
          assert({payload('downstream_request')} == {payload('upstream_request')});
        end
      end
      if (downstream_request_valid && downstream_request_ready) begin
        cc_bus <= 1; cc_bus_writeback <= cc_writeback;
        if (cc_writeback) cc_poisoned <= 0;
        if (!cc_writeback) assert(cc_accept);
      end
      assert(downstream_response_ready == (cc_bus && (cc_bus_writeback || upstream_response_ready)));
      if (cc_reply) begin
        cc_bus <= !downstream_response_bits_last;
        if (cc_bus_writeback) begin
          cc_poisoned <= cc_error;
          if (downstream_response_bits_last) begin
            if (cc_error) cc_retried <= 1;
            else cc_writeback <= 0;
          end
        end
      end
      assert(upstream_response_valid == (cc_accepted && (cc_synthetic || downstream_response_valid)));
      if (upstream_response_valid) begin
        assert(cc_owned && !cc_writeback);
        if (cc_synthetic) begin
          assert(upstream_response_bits_tag == cc_tag && upstream_response_bits_fault == cc_fault);
          assert(upstream_response_bits_data == 0 && upstream_response_bits_last);
        end else assert({{upstream_response_bits_data, upstream_response_bits_fault, upstream_response_bits_tag, upstream_response_bits_last}} ==
          {{downstream_response_bits_data, downstream_response_bits_fault, downstream_response_bits_tag, downstream_response_bits_last}});
      end
      if (cc_start || (!cc_owned && cc_accept)) begin
        cc_owned <= 1; cc_coherent <= cc_start; cc_accepted <= 0;
        cc_request <= {payload('upstream_request')}; cc_owner <= hartId;
        cc_address <= upstream_request_bits_address; cc_tag <= upstream_request_bits_tag;
        cc_synthetic <= cc_invalid || upstream_request_bits_cacheOperation != 0;
        cc_fault <= cc_invalid;
        cc_invalidate <= upstream_request_bits_write || upstream_request_bits_atomic || upstream_request_bits_cacheOperation == 2;
        cc_needed <= cc_start ? {targets} : 0; cc_issued <= 0; cc_done <= 0; cc_retried <= 0; cc_poisoned <= 0;
      end
      if (cc_accept) begin
        assert(!cc_accepted && (!cc_owned || cc_needed == cc_done));
        cc_accepted <= 1;
      end
      if (cc_end) begin cc_owned <= 0; cc_accepted <= 0; end
      if ($past(!reset && downstream_request_valid && !downstream_request_ready)) begin
        assert(downstream_request_valid && $stable({payload('downstream_request')}));
      end
      cover(cc_owned && |cc_issued && cc_done == 0 && !cc_accepted);
      cover(cc_writeback && !cc_bus && !downstream_request_ready);
      cover(cc_reply && cc_bus_writeback && cc_error);
      cover(upstream_response_valid && {completion_witness});
      cover(upstream_response_valid && !upstream_response_ready);
'''
    for hart in range(count):
        body += f'''      assume(!probe_{hart}_response_valid || (cc_owned && cc_coherent && cc_issued[{hart}] && !cc_done[{hart}]));
      if ($past(!reset && probe_{hart}_response_valid && !probe_{hart}_response_ready)) begin
        assume(probe_{hart}_response_valid && $stable({{probe_{hart}_response_bits_data, probe_{hart}_response_bits_mask, probe_{hart}_response_bits_word, probe_{hart}_response_bits_last}}));
      end
      assert(probe_{hart}_request_valid == (cc_owned && cc_coherent && !cc_accepted && cc_needed[{hart}] && !cc_issued[{hart}]));
      if (probe_{hart}_request_valid) begin
        assert(probe_{hart}_request_bits_address == (cc_address & ~64'd63) && probe_{hart}_request_bits_invalidate == cc_invalidate);
      end
      if (probe_{hart}_response_valid) assert(probe_{hart}_response_ready == (cc_owned && cc_coherent && cc_issued[{hart}] && !cc_done[{hart}] &&
        ((!cc_writeback && probe_{hart}_response_bits_mask == 0) ||
         (cc_bus && cc_bus_writeback && cc_writeback_owner == {hart} && downstream_response_valid && !cc_error))));
      if ($past(!reset && probe_{hart}_request_valid && !probe_{hart}_request_ready)) begin
        assert(probe_{hart}_request_valid && $stable({{probe_{hart}_request_bits_address, probe_{hart}_request_bits_invalidate}}));
      end
'''
    body += '    end\n  end\n'
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
    fields = dict(cacheOperation=2, address=64, data=64, size=3, mask=8, tag=8, write=1, fetch=1, privileged=1, atomic=1, atomicOperation=5, scEligible=1, refillSize=3)
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


def fabric_case(parameters):
    count = 2 * parameters['hartCount']
    depth = parameters.get('fabricReadSlots') or 2
    owner_bits = (count - 1).bit_length()
    vector = lambda suffix: '{' + ', '.join(f'{"instruction" if i % 2 == 0 else "data"}_{i//2}_{suffix}' for i in reversed(range(count))) + '}'
    body = f'''
  reg fabric_past = 0, fabric_writer_bypassed;
  (* anyconst *) reg [5:0] fabric_bit;
  reg [{depth-1}:0] fabric_live, fabric_kind;
  reg [{owner_bits-1}:0] fabric_owner [0:{depth-1}];
  reg [7:0] fabric_tags [0:{depth-1}];
  wire [{count-1}:0] fabric_owned = {' | '.join(f"(fabric_live[{n}] ? ({count}'d1 << fabric_owner[{n}]) : 0)" for n in range(depth))};
  wire [{count-1}:0] fabric_exclusive = {' | '.join(f"((fabric_live[{n}] && fabric_kind[{n}]) ? ({count}'d1 << fabric_owner[{n}]) : 0)" for n in range(depth))};
  wire [{count-1}:0] fabric_accepted = {vector('request_valid')} & {vector('request_ready')};
  wire [{count-1}:0] fabric_replied = {vector('response_valid')};
  wire [{count-1}:0] fabric_completed = fabric_replied & {vector('response_ready')} & {vector('response_bits_last')};
  wire fabric_single = |fabric_exclusive;
  always @(posedge clock) begin
    fabric_past <= 1;
    if (!fabric_past) assume(reset); else assume(!reset);
    if (!reset) begin
      assert($onehot0(fabric_accepted));
      if (|fabric_accepted) assert(!(&fabric_live));
      {''.join(f'if (fabric_live[{n}] && fabric_live[{m}]) assert(fabric_owner[{n}] != fabric_owner[{m}]);' for n in range(depth) for m in range(n))}
      assert($countones(fabric_owned) <= {depth});
      assert((fabric_owned & ~fabric_exclusive) == formal_queue_live);
      assert(fabric_exclusive == formal_single_live);
      assert(active == fabric_single);
      assert(!fabric_writer_bypassed || (!preferRead && !active));
      assert(!fabric_single || $onehot(fabric_owned));
      assert(!active || _readers_empty);
      assert(axi_ar_valid == (active ? _axi_axi_ar_valid : _readers_ar_valid));
      assert(axi_r_ready == (active ? _axi_axi_r_ready : _readers_r_ready));
      if (axi_aw_valid || axi_w_valid) assert(fabric_single);
      if (axi_ar_valid) assert(|fabric_owned);
      if (active) assert(!_readers_ar_valid);
      if (!active) assert(!_axi_axi_ar_valid && !axi_aw_valid && !axi_w_valid);
      cover($countones(fabric_owned) == {depth});
      cover(fabric_single && axi_w_valid && !axi_w_ready);
      cover(fabric_single && |fabric_replied && !(|({vector('response_ready')} & fabric_replied)));
    end
  end
'''
    for i in range(count):
        port = f'{"instruction" if i % 2 == 0 else "data"}_{i//2}'
        req, resp = port + '_request', port + '_response'
        device = ' || '.join(f"({req}_bits_address >= 64'h{int(r['base']):x} && {req}_bits_address < 64'h{int(r['base'])+int(r['size']):x})"
                            for r in parameters['memoryRegions'] if r['device']) or "1'b0"
        coherent = ' || '.join(f"({req}_bits_address >= 64'h{int(r['base']):x} && {req}_bits_address < 64'h{int(r['base'])+int(r['size']):x})"
                               for r in parameters['memoryRegions'] if r.get('dataCacheable') and r['readable'] and not r['device']) if parameters.get('dCacheWriteback') else "1'b0"
        body += f'''
  wire [7:0] fabric_tag_{i} = {' | '.join(f'(fabric_live[{n}] && fabric_owner[{n}] == {i} ? fabric_tags[{n}] : 0)' for n in range(depth))};
  wire fabric_special_{i} = {req}_bits_cacheOperation != 0 || {req}_bits_write || {req}_bits_atomic || ({coherent or "1'b0"}) ||
    ({req}_bits_size > 3 && !({req}_bits_size == 6 &&
      ({req}_bits_fetch ? {int(bool(parameters.get('enableBurstRefill')))} : {int(parameters.get('dCacheRefillBytes') == 64)}))) || ({device});
  always @(posedge clock) if (!reset) begin
    if ({resp}_valid) begin
      assert(fabric_owned[{i}]);
      assert({resp}_bits_tag == fabric_tag_{i});
    end
    if (fabric_accepted[{i}]) begin
      assert(!fabric_owned[{i}] && !fabric_single);
      if (fabric_special_{i}) assert(fabric_owned == 0);
    end
    if ($past(!reset && {resp}_valid && !{resp}_ready)) begin
      assert({resp}_valid);
      assert($stable({resp}_bits_data[fabric_bit])); assert($stable({resp}_bits_tag));
      assert($stable({{{resp}_bits_fault, {resp}_bits_last}}));
    end
  end
'''
    for slot in range(depth):
        free = ' && '.join([f'!fabric_live[{slot}]', *(f'fabric_live[{n}]' for n in range(slot))])
        body += f'''  always @(posedge clock) if (reset) fabric_live[{slot}] <= 0; else begin
    if (fabric_live[{slot}]) assert(fabric_owner[{slot}] < {count});
    if (fabric_live[{slot}] && fabric_completed[fabric_owner[{slot}]]) fabric_live[{slot}] <= 0;
'''
        for i in range(count):
            port = f'{"instruction" if i % 2 == 0 else "data"}_{i//2}'
            body += f'''    if (fabric_accepted[{i}] && ({free})) begin
      fabric_live[{slot}] <= 1; fabric_owner[{slot}] <= {i};
      fabric_kind[{slot}] <= fabric_special_{i}; fabric_tags[{slot}] <= {port}_request_bits_tag;
    end
'''
        body += '  end\n'
    special = '{' + ', '.join(f'fabric_special_{i}' for i in reversed(range(count))) + '}'
    body += f'''
  wire [{count-1}:0] fabric_special = {special};
  wire fabric_writer_waiting = |(fabric_special & {vector('request_valid')});
  always @(posedge clock) begin
    if (reset || !fabric_writer_waiting || |(fabric_accepted & fabric_special)) fabric_writer_bypassed <= 0;
    else if (|(fabric_accepted & ~fabric_special)) begin
      assert(!fabric_writer_bypassed); fabric_writer_bypassed <= 1;
    end
    if (!reset) cover(fabric_writer_waiting && $countones(fabric_owned) == {depth});
  end
'''
    body += '''
  always @(posedge clock) if (!reset) begin
    if ($past(!reset && axi_r_valid && !axi_r_ready)) begin
      assume(axi_r_valid); assume($stable({axi_r_bits_data, axi_r_bits_id, axi_r_bits_resp, axi_r_bits_last}));
    end
    if ($past(!reset && axi_b_valid && !axi_b_ready)) begin
      assume(axi_b_valid); assume($stable({axi_b_bits_id, axi_b_bits_resp}));
    end
  end
'''
    return ('MemoryFabric', body, 'assign axi_ar_valid = active ?', "assign axi_ar_valid = 1'h0 ?")


def memory_case(parameters):
    fields = ('address', 'data', 'size', 'mask', 'tag', 'write', 'fetch', 'privileged', 'atomic', 'atomicOperation', 'scEligible', 'refillSize')
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
    data_line = parameters.get('dCacheRefillBytes', 8) == 64
    for size in (*range(4), *((6,) if parameters.get('enableBurstRefill') or data_line else ())):
        count = 1 << size
        line_shape = f"!m_write && !m_atomic && (m_fetch ? {int(bool(parameters.get('enableBurstRefill')))} : {int(data_line)}) && " if size == 6 else ''
        body += f"      {size}: if ({line_shape}m_shape && (m_address & 64'd{count-1}) == 0 && (!m_write || (m_mask != 0 && (m_mask & 8'h{(255 ^ ((1 << count) - 1)) if size != 6 else 0:x}) == 0))) begin\n"
        for region in parameters['memoryRegions']:
            rights = {key: int(region[key]) for key in ('readable', 'writable', 'executable', 'device', 'atomic')}
            if int(region['size']) >= count:
                if size == 6:
                    body += f"        if (!m_write && !m_atomic && m_address >= 64'h{int(region['base']):x} && m_address <= 64'h{int(region['base'])+int(region['size'])-count:x} && (m_fetch ? {int(bool(rights['executable'] and not rights['device']))} : {int(bool(rights['readable'] and region.get('dataCacheable') and not rights['device']))})) m_allowed = 1;\n"
                    continue
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
    if data_line:
        body += '''  always @(posedge clock) if (!reset) begin
    cover(downstream_request_valid && !m_fetch && upstream_request_bits_size == 6);
    cover(upstream_request_valid && upstream_request_ready && !m_fetch && upstream_request_bits_size == 6 && !m_allowed);
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
        assert(request_data == addend);
        assert(request_address == accepted_address && request_size == accepted_size &&
          request_mask == accepted_mask && request_tag == accepted_tag && request_atomic == is_atomic);
        assert({request_fetch, 1'b0, STORED_PRIVILEGED} == accepted_protection);
        assert(request_atomicOperation == accepted_operation);
        assert(hartId_0 == accepted_id);
        assert(data == old_value); assert(fault == expected_fault);
      end
      if (held && !complete)
        assert(awDone == address_sent && wDone == data_sent && request_write == can_write);
      assert(axi_ar_valid == (can_read && !read_owned));
      assert(axi_aw_valid == (can_write && !address_sent));
      assert(axi_w_valid == (can_write && !data_sent));
      assert(axi_r_ready == read_owned && axi_b_ready == (address_sent && data_sent));
      if (held && is_lr) assert(!axi_aw_valid && !axi_w_valid && !can_write);
      if (held && is_sc && accepted_write) assert(!axi_ar_valid && !can_read && !retried);
      if (held && is_sc && !accepted_eligible) begin assert(complete && !expected_fault); assert(old_value == 1); end
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
        assert(memory_response_bits_tag == accepted_tag); assert(memory_response_bits_data == old_value);
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
    if parameters.get('enableBurstRefill') or parameters.get('dCacheRefillBytes', 8) == 64:
        body = body.replace('reg checked_past = 0;', '''
  wire input_line = (memory_request_bits_fetch ? INSTRUCTION_LINE : DATA_LINE) && !memory_request_bits_write && !memory_request_bits_atomic && memory_request_bits_size == 6;
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
        body = body.replace('INSTRUCTION_LINE', str(int(bool(parameters.get('enableBurstRefill'))))).replace('DATA_LINE', str(int(parameters.get('dCacheRefillBytes', 8) == 64)))
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
            body += '  always @(posedge clock) if (!reset && line_owned && line_buffered) begin assert(slice == line_slice); assert(block == line_block); end\n'
        if parameters.get('dCacheRefillBytes', 8) == 64:
            body += '  always @(posedge clock) if (!reset) cover(line_owned && !line_protection[2] && memory_response_valid && memory_response_ready && memory_response_bits_last && !line_fault);\n'
        for token, value in (('BEATS', 512 // width), ('SLICES', width // 64), ('BUSSIZE', lane_bits)):
            body = body.replace(token, str(value))
    if parameters.get('enableBurstRefill') or parameters.get('dCacheRefillBytes') == 64:
        body = re.sub(r'\bline\b', 'axi_request_line', body)
        body = f'''  wire axi_request_line = !request_write && !request_atomic && request_size == 6 &&
    (request_fetch ? {int(bool(parameters.get('enableBurstRefill')))} : {int(parameters.get('dCacheRefillBytes') == 64)});
''' + body
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
    body = body.replace('assert($stable({memory_response_bits_data, memory_response_bits_fault, memory_response_bits_tag, memory_response_bits_last}));',
                        'assert($stable(memory_response_bits_data)); assert($stable({memory_response_bits_fault, memory_response_bits_tag, memory_response_bits_last}));')
    body = body.replace('assert($stable({axi_w_bits_data, axi_w_bits_strb, axi_w_bits_last}));',
                        'assert($stable(axi_w_bits_data)); assert($stable({axi_w_bits_strb, axi_w_bits_last}));')
    return ('Axi', body, 'request_atomic <= memory_request_bits_atomic;', 'request_atomic <= 0;')


def read_schedule_case(depth):
    suffixes = tuple('' if n == 0 else f'_{n-1}' for n in range(depth))
    states = ' '.join(f'assign schedule_state[{n}] = state{suffix};' for n, suffix in enumerate(suffixes))
    return f'''
  reg schedule_past = 0;
  (* anyconst *) reg [{(depth-1).bit_length()-1}:0] watched_slot;
  reg [{depth.bit_length()-1}:0] bypassed = 0;
  wire [2:0] schedule_state [0:{depth-1}];
  {states}
  wire waiting_slot = schedule_state[watched_slot] == 1 || schedule_state[watched_slot] == 2;
  wire own_grant = schedule_state[watched_slot] == 2 && ar_valid && ar_ready;
  wire [{depth-1}:0] schedule_allowed = {{{', '.join(f'rq_dut_permission_{n}' for n in reversed(range(depth)))}}};
  wire [{depth.bit_length()}:0] distance = watched_slot >= addressNext ? watched_slot - addressNext : {depth} + watched_slot - addressNext;
  integer selected_slot, selected_distance, active_slot;
  wire [{depth.bit_length()}:0] following = active_slot == {depth-1} ? 0 : active_slot + 1;
  wire [{depth.bit_length()}:0] remaining = watched_slot >= following ? watched_slot - following : {depth} + watched_slot - following;
  always @* begin
    selected_slot = 0; selected_distance = {depth}; active_slot = 0;
    for (integer n = 0; n < {depth}; n++) begin
      if (schedule_state[n] == 2) active_slot = n;
      if (schedule_state[n] == 1 && ((n >= addressNext ? n - addressNext : {depth} + n - addressNext) < selected_distance)) begin
        selected_slot = n; selected_distance = n >= addressNext ? n - addressNext : {depth} + n - addressNext;
      end
    end
  end
  always @(posedge clock) begin
    schedule_past <= 1;
    assume(watched_slot < {depth});
    if (!schedule_past) assume(reset); else assume(!reset);
    if (reset || !waiting_slot || own_grant) bypassed <= 0;
    else if (ar_valid && ar_ready) bypassed <= bypassed + 1;
    if (!reset) begin
      assert(addressNext < {depth});
      assert($onehot0({{{', '.join(f'state{suffix} == 2' for suffix in suffixes)}}}));
      if (schedule_past && !poisoned && $past(!reset && !poisoned && !ar_valid && selected_distance < {depth} && schedule_allowed[selected_slot]))
        assert(schedule_state[$past(selected_slot)] == 2);
      assert(bypassed < {depth});
      if (waiting_slot) assert(bypassed + distance < {depth});
      if (waiting_slot && ar_valid && schedule_state[watched_slot] != 2) assert(bypassed + remaining < {depth-1});
      cover(own_grant && watched_slot == {depth-1} && bypassed == {depth-1});
    end
  end
'''


def read_queue_case(parameters):
    harts, width = parameters['hartCount'], parameters['axiDataBits']
    dual = parameters.get('loadQueueEntries', 1) == 2
    depth = parameters.get('fabricReadSlots') or 2
    suffixes = tuple('' if n == 0 else f'_{n-1}' for n in range(depth))
    states = tuple('state' + suffix for suffix in suffixes)
    lane_bits, owner_bits = (width // 8 - 1).bit_length(), (2 * harts - 1).bit_length()
    slices, beats = width // 64, 512 // width
    burst = parameters.get('enableBurstRefill') or parameters.get('dCacheRefillBytes') == 64
    instruction_line, data_line = int(bool(parameters.get('enableBurstRefill'))), int(parameters.get('dCacheRefillBytes') == 64)
    body = f'''
  (* anyconst *) reg [5:0] rq_bit;
  reg rq_past = 0, rq_poison = 0, rq_reordered = 0, rq_interleaved = 0, rq_previous = 0;
  reg [{depth-1}:0] rq_owned = 0, rq_checked = 0, rq_sent = 0, rq_terminal = 0;
  reg [{depth-1}:0] rq_allowed, rq_fault, rq_fetch, rq_privileged, rq_write, rq_atomic, rq_line;
  reg [{owner_bits-1}:0] rq_owner [0:{depth-1}];
  reg rq_address [0:{depth-1}];
  reg [{lane_bits-1}:0] rq_offset [0:{depth-1}];
  reg [2:0] rq_size [0:{depth-1}];
  reg [7:0] rq_tag [0:{depth-1}];
  reg [{slices-1}:0] rq_data [0:{depth-1}];
  reg [3:0] rq_count [0:{depth-1}], rq_beats [0:{depth-1}];
  reg [{max(1, (max(harts, depth) - 1).bit_length())-1}:0] rq_first_id, rq_previous_id;
  wire [{depth-1}:0] rq_waiting = rq_owned & rq_sent & ~rq_terminal;
  wire [{depth-1}:0] rq_matches = {{{', '.join(f'rq_waiting[{n}] && r_bits_id == {n}' for n in reversed(range(depth)))}}};
  wire rq_known = |rq_matches;
  wire [{depth.bit_length()-1}:0] rq_wait_count = $countones(rq_waiting);
'''
    def permission(suffix):
        field = lambda name: 'request_' + name + suffix
        address, size = field('address'), field('size')
        ranges = []
        for amount in (*range(4), *((6,) if burst else ())):
            terms = []
            for region in parameters['memoryRegions']:
                if region['device'] or int(region['size']) < 1 << amount:
                    continue
                execute = region['executable'] and (amount != 6 or parameters.get('enableBurstRefill'))
                read = region['readable'] and (amount != 6 or parameters.get('dCacheRefillBytes') == 64 and region.get('dataCacheable'))
                terms.append(f"({address} >= 64'h{int(region['base']):x} && {address} <= 64'h{int(region['base'])+int(region['size'])-(1<<amount):x} && ({field('fetch')} ? 1'b{int(bool(execute))} : 1'b{int(bool(read))}))")
            ranges.append(f"({size} == 3'd{amount} && ({address} & 64'd{(1<<amount)-1}) == 0 && ({' || '.join(terms) or '0'}))")
        return f"!{field('write')} && !{field('atomic')} && (" + ' || '.join(ranges) + ')'
    for slot, suffix in enumerate(suffixes):
        ready = ' || '.join(f'(rq_owner[{slot}] == {port} && ports_{port}_response_ready' +
                            (f' && ports_{port}_response_valid && ports_{port}_response_bits_tag == rq_tag[{slot}]' if dual else '') + ')'
                            for port in range(2 * harts))
        body += f'''  wire rq_permission_{slot} = {permission(suffix)};
  wire [63:0] rq_word_{slot} = READ_QUEUE_DATA_{slot};
  wire rq_take_{slot} = rq_owned[{slot}] && rq_count[{slot}] != 0 && ({ready});
'''
    for port in range(2 * harts):
        body += f'  wire rq_accept_{port} = ports_{port}_request_valid && ports_{port}_request_ready;\n'
    body += f'''  wire [{2*harts-1}:0] rq_accepted = {{{', '.join(f'rq_accept_{port}' for port in reversed(range(2*harts)))}}};
  always @(posedge clock) begin
    rq_past <= 1;
    if (!rq_past) assume(reset); else assume(!reset);
    if (reset) begin
      rq_owned <= 0; rq_checked <= 0; rq_sent <= 0; rq_terminal <= 0;
      rq_poison <= 0; rq_reordered <= 0; rq_interleaved <= 0; rq_previous <= 0;
    end else begin
      assume(!r_valid || |rq_waiting);
      assert((rq_accepted & (rq_accepted - {2*harts}'d1)) == 0);
      assert(empty == (!(|rq_owned) && !rq_poison));
      assert(poisoned == rq_poison);
      assert({' && '.join(f'{state} <= {6 if burst else 4}' for state in states)});
      assert($onehot0({{{', '.join(state + ' == 2' for state in states)}}}));
      {''.join(f'if (rq_owned[{n}] && rq_owned[{m}] && rq_owner[{n}] == rq_owner[{m}]) assert(' +
               (f'rq_owner[{n}][0] && rq_tag[{n}] != rq_tag[{m}]' if dual else "1'b0") + ');' for n in range(depth) for m in range(n))}
      if (rq_poison) assert(rq_accepted == 0);
      if (ar_valid) begin
        assert({' || '.join(f'(rq_owned[{n}] && ar_bits_id == {n})' for n in range(depth))});
        assert(ar_bits_burst == 1 && !ar_bits_lock && ar_bits_cache == 0 && ar_bits_qos == 0);
        if (ar_ready && rq_wait_count == 0) rq_first_id <= ar_bits_id;
      end
      if (r_valid && r_ready) begin
        if (!rq_known) rq_poison <= 1;
        else begin
          if (rq_wait_count > 1 && r_bits_last && r_bits_id != rq_first_id) rq_reordered <= 1;
          if (rq_previous && rq_wait_count > 1 && r_bits_id != rq_previous_id) rq_interleaved <= 1;
          rq_previous <= 1; rq_previous_id <= r_bits_id;
        end
      end
      if ($past(!reset && ar_valid && !ar_ready)) begin
        assert(ar_valid);
        assert($stable({{ar_bits_id, ar_bits_len, ar_bits_size, ar_bits_burst, ar_bits_lock, ar_bits_cache, ar_bits_prot, ar_bits_qos}}));
        if (rq_bit < {parameters['physicalAddressBits']}) assert($stable(ar_bits_addr[rq_bit]));
      end
      if ($past(!reset && rq_poison && !ar_valid)) assert(!ar_valid);
      if ($past(!reset && r_valid && !r_ready)) begin
        assume(r_valid); assume($stable({{r_bits_data, r_bits_id, r_bits_resp, r_bits_last}}));
      end
      cover(&rq_waiting);
      {'cover(rq_reordered && !(|rq_owned));' if depth > 1 else ''}
      cover(ar_valid && !ar_ready && &rq_owned);
      cover(rq_poison && !(|rq_owned));
'''
    if burst:
        body += '      cover(&(rq_waiting & rq_line));\n'
        if depth > 1:
            body += '      cover(rq_interleaved && !(|rq_owned));\n'
        if width > 64:
            body += '      assert($onehot0({' + ', '.join(state + ' == 5' for state in states) + '}));\n'
    for n, suffix in enumerate(suffixes):
        body += f'''
      if (rq_owned[{n}] && !rq_checked[{n}]) begin
        rq_checked[{n}] <= 1; rq_allowed[{n}] <= rq_permission_{n};
        if (!rq_permission_{n}) begin rq_count[{n}] <= 1; rq_terminal[{n}] <= 1; rq_fault[{n}] <= 1; rq_data[{n}] <= 0; end
      end
      if (ar_valid && ar_bits_id == {n} && rq_owned[{n}]) begin
        assert(rq_checked[{n}] && rq_allowed[{n}] && !rq_sent[{n}] && !rq_terminal[{n}]);
        assert(ar_bits_len == (rq_line[{n}] ? {beats-1} : 0));
        assert(ar_bits_size == (rq_line[{n}] ? {lane_bits} : rq_size[{n}]));
        assert(ar_bits_prot == {{rq_fetch[{n}], 1'b0, rq_privileged[{n}]}});
        if (rq_bit < {parameters['physicalAddressBits']}) assert(ar_bits_addr[rq_bit] == rq_address[{n}]);
        if (ar_ready) rq_sent[{n}] <= 1;
      end
      if (r_valid && r_ready && rq_matches[{n}]) begin
        assert(rq_count[{n}] == 0);
        rq_terminal[{n}] <= r_bits_last;
        rq_fault[{n}] <= rq_fault[{n}] || rq_poison || r_bits_resp != 0 ||
          (rq_line[{n}] ? r_bits_last != (rq_beats[{n}] == {beats-1}) : !r_bits_last);
        if (rq_line[{n}] && rq_beats[{n}] < {beats}) begin
          rq_count[{n}] <= {slices}; rq_beats[{n}] <= rq_beats[{n}] + 1;
          for (integer part = 0; part < {slices}; part++) rq_data[{n}][part] <= r_bits_data[64 * part + rq_bit];
        end else if (r_bits_last) begin
          rq_count[{n}] <= 1;
          rq_data[{n}] <= !rq_line[{n}] && rq_size[{n}] <= 3 && rq_bit < (7'd8 << rq_size[{n}]) && rq_offset[{n}] * 8 + rq_bit < {width} && r_bits_data[rq_offset[{n}] * 8 + rq_bit];
        end
      end
      if (rq_take_{n}) begin
        rq_count[{n}] <= rq_count[{n}] - 1; rq_data[{n}] <= rq_data[{n}] >> 1;
        if (rq_terminal[{n}] && rq_count[{n}] == 1) rq_owned[{n}] <= 0;
      end
'''
        for port in range(2 * harts):
            req = f'ports_{port}_request_bits_'
            privilege = req + 'privileged' if parameters.get('enableUserMode') else "1'b1"
            select = ' && '.join([f'!rq_owned[{n}]', *(f'rq_owned[{m}]' for m in range(n))])
            body += f'''      if (rq_accept_{port} && ({select})) begin
        rq_owned[{n}] <= 1; rq_checked[{n}] <= 0; rq_sent[{n}] <= 0; rq_terminal[{n}] <= 0;
        rq_owner[{n}] <= {port}; rq_count[{n}] <= 0; rq_beats[{n}] <= 0; rq_fault[{n}] <= 0;
        rq_size[{n}] <= {req}size; rq_address[{n}] <= {req}address[rq_bit]; rq_offset[{n}] <= {req}address[{lane_bits-1}:0]; rq_tag[{n}] <= {req}tag;
        rq_fetch[{n}] <= {req}fetch; rq_privileged[{n}] <= {privilege}; rq_write[{n}] <= {req}write; rq_atomic[{n}] <= {req}atomic;
        rq_line[{n}] <= !{req}write && !{req}atomic && {req}size == 6 && ({req}fetch ? {instruction_line} : {data_line});
      end
'''
        state, owner = 'state' + suffix, 'owner' + suffix
        body += f'''      assert(rq_owned[{n}] == ({state} != 0));
      if (rq_owned[{n}]) begin
        if ({state} != 1) assert(rq_checked[{n}]);
        assert(rq_sent[{n}] == ({state} >= 3 && ({state} != 4 || rq_allowed[{n}])));
        assert(rq_owner[{n}] < {2*harts} && {owner} == rq_owner[{n}]);
        {f'assert(request_tag{suffix} == rq_tag[{n}]);' if dual else ''}
        assert(request_size{suffix} == rq_size[{n}] && request_fetch{suffix} == rq_fetch[{n}] && request_write{suffix} == rq_write[{n}] && request_atomic{suffix} == rq_atomic[{n}]);
        assert(request_address{suffix}[rq_bit] == rq_address[{n}] && request_address{suffix}[{lane_bits-1}:0] == rq_offset[{n}] && request_tag{suffix} == rq_tag[{n}]);
        assert(rq_line[{n}] == (!rq_write[{n}] && !rq_atomic[{n}] && rq_size[{n}] == 6 && (rq_fetch[{n}] ? {instruction_line} : {data_line})));
        if (rq_checked[{n}]) assert(rq_permission_{n} == rq_allowed[{n}]);
        if ({state} >= 2 && {state} != 4) assert(rq_allowed[{n}] && rq_checked[{n}]);
        assert(fault{suffix} == rq_fault[{n}]);
        if ({state} == 1 || {state} == 2 || {state} == 3 || {state} == 6) assert(rq_count[{n}] == 0);
        if ({state} == 3 || {state} == 6) assert(rq_waiting[{n}]);
        if ({state} == 1 || {state} == 2) assert(!rq_sent[{n}] && !rq_terminal[{n}]);
        if ({state} == 4) begin
          assert(rq_count[{n}] == 1 && rq_terminal[{n}]);
          assert(data{suffix}[rq_bit] == rq_data[{n}][0]);
        end
'''
        if burst:
            body += f'''        if ({state} == 5) begin
          assert(rq_line[{n}] && rq_sent[{n}] && rq_count[{n}] >= 1 && rq_count[{n}] <= {slices});
          assert(terminal{suffix} == rq_terminal[{n}] && beat{suffix} + 1 == rq_beats[{n}] && beat{suffix} < {beats});
          if ((beat{suffix} == {beats-1}) != rq_terminal[{n}]) assert(rq_fault[{n}]);
'''
            if width > 64:
                body += f'''          assert(slice == {slices} - rq_count[{n}]);
          for (integer part = 0; part < {slices}; part++)
            if (part < rq_count[{n}]) assert(block[(slice + part) * 64 + rq_bit] == rq_data[{n}][part]);
'''
            else:
                body += f'          assert(data{suffix}[rq_bit] == rq_data[{n}][0]);\n'
            body += f'''        end
        if ({state} == 1 || {state} == 2) assert(beat{suffix} == 0 && rq_beats[{n}] == 0);
        if ({state} == 3) assert(beat{suffix} == rq_beats[{n}] && beat{suffix} < {beats});
        if ({state} == 6) assert(rq_line[{n}] && beat{suffix} == {beats-1} && rq_beats[{n}] == {beats} && rq_fault[{n}]);
'''
        body += f'        assert(request_privileged{suffix} == rq_privileged[{n}]);\n' if parameters.get('enableUserMode') else f'        assert(rq_privileged[{n}]);\n'
        body += '      end\n'
    for port in range(2 * harts):
        prefix = f'ports_{port}'
        owned = [f'(rq_owned[{n}] && rq_owner[{n}] == {port})' for n in range(depth)]
        if dual:
            body += f"      assert($countones({{{', '.join(owned)}}}) <= {2 if port % 2 else 1});\n"
            if port % 2 and depth > 1:
                suffix = '' if port == 1 else f'_{port // 2 - 1}'
                body += f'      if (held{suffix}) assert(saved{suffix} < {depth} && rq_owned[saved{suffix}] && rq_owner[saved{suffix}] == {port} && rq_count[saved{suffix}] != 0);\n'
        availability = (f"$countones({{{', '.join(owned)}}}) < 2 && " + ' && '.join(
            f'(!{owned[n]} || rq_tag[{n}] != {prefix}_request_bits_tag)' for n in range(depth))) if dual and port % 2 else ' && '.join(
            f'!{term}' for term in owned)
        body += f'''      if (rq_accept_{port}) begin
        assert(!(&rq_owned));
        assert({availability});
      end
      assert({prefix}_response_valid == ({' || '.join(f'(rq_owned[{n}] && rq_owner[{n}] == {port} && rq_count[{n}] != 0)' for n in range(depth))}));
'''
        if dual:
            body += f"      if ({prefix}_response_valid) assert(" + ' || '.join(
                f'(rq_owned[{n}] && rq_owner[{n}] == {port} && rq_count[{n}] != 0 && {prefix}_response_bits_tag == rq_tag[{n}])'
                for n in range(depth)) + ');\n'
        for n in range(depth):
            selection = f' && rq_count[{n}] != 0 && {prefix}_response_bits_tag == rq_tag[{n}]' if dual else ''
            body += f'''      if ({prefix}_response_valid && rq_owner[{n}] == {port} && rq_owned[{n}]{selection}) begin
        assert({prefix}_response_bits_fault == rq_fault[{n}] && {prefix}_response_bits_last == (rq_terminal[{n}] && rq_count[{n}] == 1));
        assert({prefix}_response_bits_tag == rq_tag[{n}] && {prefix}_response_bits_data[rq_bit] == rq_data[{n}][0]);
      end
'''
        body += f'''      if ($past(!reset && {prefix}_response_valid && !{prefix}_response_ready)) begin
        assert({prefix}_response_valid); assert($stable({{{prefix}_response_bits_fault, {prefix}_response_bits_last}}));
        assert($stable({{{prefix}_response_bits_data[rq_bit], {prefix}_response_bits_tag}}));
        {f'assert($stable({prefix}_response_bits_tag));' if dual else ''}
      end
'''
    body += '    end\n  end\n'
    if dual and depth > 1:
        pairs = ' || '.join(f'(rq_owner[{n}] == rq_owner[{m}] && rq_owner[{n}][0] && rq_waiting[{n}] && rq_waiting[{m}])'
                            for n in range(depth) for m in range(n))
        body += f'  always @(posedge clock) if (!reset) cover({pairs});\n'
    for hart in range(harts):
        for kind, condition in (
            ('denied', 'rq_checked[N] && !rq_allowed[N] && rq_count[N] == 1'),
            ('short', 'rq_sent[N] && rq_count[N] == 1 && !rq_fault[N] && rq_size[N] < 3'),
            ('fault', 'rq_sent[N] && rq_count[N] == 1 && rq_fault[N] && !rq_poison'),
            ('terminal', f'rq_terminal[N] && rq_count[N] != 0 && rq_wait_count == {int(depth > 1)}')):
            expression = ' || '.join(f'(rq_owned[{n}] && (rq_owner[{n}] >> 1) == {hart} && {condition.replace("N", str(n))})' for n in range(depth))
            body += f'  wire rq_hart_{hart}_{kind} = {expression};\n  always @(posedge clock) if (!reset) begin\n    cover(rq_hart_{hart}_{kind});\n  end\n'
    return ('ReadQueue', body, 'assign ar_bits_len =', "assign ar_bits_len = 8'h80 |")


def verify(rtl, directory, modules=None, mutations=None):
    assert mutations is None or modules and all(mode.startswith('mutation') for mode in mutations), 'Select modules and negative controls'
    directory.mkdir(parents=True, exist_ok=True)
    summary = directory / 'summary.json'
    summary.unlink(missing_ok=True)
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    read_slots = manifest['parameters'].get('fabricReadSlots') or 2
    read_bit_step = 4 if read_slots > 2 and manifest['parameters']['hartCount'] == 16 else 8
    read_suffixes = tuple('' if n == 0 else f'_{n-1}' for n in range(read_slots))
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in manifest['sourceHashes'].items())
    sources = {p.name: p.read_text() for p in rtl.glob('*.sv') if 'DV' not in p.name and not p.name.startswith('ref_')}
    backend_dv = rtl / 'DitDahA1Backend_DV.sv'
    observation_sources = {backend_dv.name: backend_dv.read_text()} if backend_dv.exists() else {}
    license = '\n'.join(line.replace('#', '//', 1) for line in Path(__file__).read_text().splitlines()[:2]) + '\n'
    reports = []
    checker_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    regions = manifest['parameters']['memoryRegions']
    cache_routing_base = next((int(r['base']) & ~63 for r in regions if r.get('dataCacheable') and r['readable'] and not r['device'] and
        int(r['base']) % 64 and not any((p['device'] or p.get('dataCacheable') and p['readable']) and
        int(p['base']) <= (int(r['base']) & ~63) < int(p['base']) + int(p['size']) for p in regions)), None)
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
    if manifest['parameters'].get('loadQueueEntries', 1) == 2 and not enabled and manifest['parameters'].get('virtualAddressBits') == 0:
        cases.append(lsu_reads_case(manifest['parameters']))
    if 'DitDahA1ReadQueue.sv' in sources:
        cases.append(read_queue_case(manifest['parameters']))
    if 'DitDahA1Backend.sv' in sources:
        cases.append(pipeline_case(sources['DitDahA1Backend.sv'], manifest['parameters']))
    if 'DitDahA1ReadQueue.sv' in sources and 'DitDahA1MemoryFabric.sv' in sources:
        cases.append(fabric_case(manifest['parameters']))
    if manifest['parameters'].get('localInterruptBase') is not None:
        cases.append(local_interrupt_case(manifest['parameters']))
    if manifest['parameters'].get('iCacheBytes'):
        cases.append(instruction_cache_case(manifest['parameters']))
    if manifest['parameters'].get('dCacheBytes'):
        cases += [writeback_cache_case(manifest['parameters']) if manifest['parameters'].get('dCacheWriteback') else data_cache_case(manifest['parameters']),
                  coherence_case(manifest['parameters'])]
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
        if name == 'DataCacheWriteback':
            unit = 'DataCache'
        if name == 'LsuReads':
            unit = 'Lsu'
        machine = 'privilege != 0' if manifest['parameters'].get('enableUserMode') else "1'b1"
        if name in ('Pmp', 'PmpDecode') and (manifest['parameters'].get('enableBurstRefill') or manifest['parameters'].get('dCacheRefillBytes', 8) == 64 or manifest['parameters'].get('iCacheBytes') and manifest['parameters']['issueWidth'] == 3):
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
        if unit in ('Lsu', 'InstructionCache') and name != 'LsuReads':
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
        if unit == 'DataCache':
            capacity = manifest['parameters']['dCacheBytes']
            tag_bits = manifest['parameters']['physicalAddressBits'] - (capacity - 1).bit_length()
            cache_memories = ((rf'\w+_{capacity//8}x64', 'data_ext', 'DATA'),
                              (rf'\w+_{capacity//64}x{tag_bits}', 'dataTags_ext', 'TAG'))
            data_ports, tag_ports = [instance_ports(sources['DitDahA1DataCache.sv'], memory, instance) for memory, instance, _ in cache_memories]
            if manifest['parameters'].get('dCacheWriteback'):
                cache_memories += ((rf'\w+_{capacity//8}x8', 'dataDirty_ext', 'DIRTY'),)
                watched_types = {re.search(r'(\w+)\s+' + instance + r'\s*\(', sources['DitDahA1DataCache.sv'])[1] + '.sv'
                                 for _, instance, _ in cache_memories[1:]}
            assert len(data_ports) == len(tag_ports) == 1
            body = body.replace('CACHE_READ', 'FORMAL_DATA_R0_data').replace('filling_0', 'formal_data_write')
            body += '\n  wire formal_data_write = FORMAL_DATA_W0_en;\n'
            body = body.replace('CACHE_WRITE_ADDRESS', 'FORMAL_DATA_W0_addr').replace('CACHE_WRITE_DATA', 'FORMAL_DATA_W0_data')
            body = body.replace('CACHE_TAG_WRITE', 'FORMAL_TAG_W0_en')
            body = body.replace('CACHE_ELIGIBLE', re.search(r'wire\s+(eligible(?:_layerCapture)?)\s*=', sources['DitDahA1DataCache.sv']).group(1))
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
        elif name == 'PmpSubset':
            module = 'formal_subset'
            files = {module + '.sv': license + 'module formal_subset(input [64:0] low, high, input [7:0] config, input [63:0] address, input [1:0] privilege, input prior_whole, prior_subset);\nendmodule\n'}
        else:
            files = dict(sources) if unit in ('Backend', 'Frontend', 'InstructionCache', 'DataCache', 'MemoryFabric') or unit == 'Fetch' and manifest['parameters'].get('iCacheBytes') else {module + '.sv': sources[module + '.sv']}
        if unit == 'MemoryFabric':
            count = 2 * manifest['parameters']['hartCount']
            slot_bits = (count - 1).bit_length() + 1
            observed = [
                ('ReadQueue', 'formal_queue_live', count, ' | '.join(f"((state{suffix} != 0) ? ({count}'d1 << owner{suffix}) : 0)" for suffix in read_suffixes)),
                ('ReadQueue', 'formal_queue_slots', read_slots * slot_bits, '{' + ', '.join('{(state' + suffix + ' != 0), owner' + suffix + '}' for suffix in reversed(read_suffixes)) + '}'),
                ('ReadQueue', 'formal_queue_slot_tags', 8 * read_slots, '{' + ', '.join('request_tag' + suffix for suffix in reversed(read_suffixes)) + '}'),
                ('ReadQueue', 'formal_queue_tags', 8 * count, ' | '.join(f"((state{suffix} != 0) ? ({{{8*count-8}'b0, request_tag{suffix}}} << (8 * owner{suffix})) : 0)" for suffix in read_suffixes)),
                ('MemoryArbiter', 'formal_single_live', count, f"(state != 0) ? ({count}'d1 << owner) : 0"),
                ('MemoryArbiter', 'formal_single_sent', 1, 'state == 2'),
                ('MemoryArbiter', 'formal_arbiter_tag', 8, 'request_tag'),
                ('Axi', 'formal_axi_live', 1, 'state != 0'), ('Memory', 'formal_memory_live', 1, 'pending'),
                ('Memory', 'formal_memory_fault', 1, 'pending && localFault'),
                ('Axi', 'formal_axi_tag', 8, 'request_tag'), ('Memory', 'formal_memory_tag', 8, 'tag')]
            if manifest['parameters'].get('dCacheBytes'):
                observed.append(('Coherence', 'formal_coherence_live', 1, 'state != 0'))
                observed.append(('Coherence', 'formal_coherence_tag', 8, 'tag'))
                observed.append(('Coherence', 'formal_coherence_tag_valid', 1, 'state != 0 && state != 6'))
                observed.append(('Coherence', 'formal_coherence_bus', 1, 'state == 3 || state == 6' if manifest['parameters'].get('dCacheWriteback') else 'state == 6'))
                observed.append(('Coherence', 'formal_coherence_sent', 1, 'state == 5 || state == 6'))
            if manifest['parameters'].get('localInterruptBase') is not None:
                observed.append(('LocalInterrupts', 'formal_local_live', 1, 'pending'))
                observed.append(('LocalInterrupts', 'formal_local_tag', 8, 'response_tag'))
            for child, signal, bits, expression in observed:
                child_file = 'DitDahA1' + child + '.sv'
                files[child_file] = files[child_file].replace(');', f', output [{bits-1}:0] {signal});', 1)
                files[child_file] = files[child_file].replace('endmodule', f'assign {signal} = {expression};\nendmodule', 1)
                files[module + '.sv'], connected = re.subn(rf'(DitDahA1{child}\s+\w+\s*\()', rf'\1\n.{signal}({signal}),', files[module + '.sv'])
                assert connected == 1
                body += f'\n  wire [{bits-1}:0] {signal};\n'
                if bits == 1:
                    body += f'  always @(posedge clock) if (!reset) assert(!{signal} || active);\n'
            if manifest['parameters'].get('dCacheBytes'):
                files['DitDahA1Coherence.sv'] = files['DitDahA1Coherence.sv'].replace('endmodule', 'always @(posedge clock) if (!reset) begin assert(state <= 6); if (state == 0 || state >= 4) assert(pending == 0); end\nendmodule', 1)
                if not manifest['parameters'].get('dCacheWriteback'):
                    files['DitDahA1Coherence.sv'] = files['DitDahA1Coherence.sv'].replace('endmodule', 'always @(posedge clock) if (!reset) assert(state != 2 && state != 3);\nendmodule', 1)
                for hart in range(manifest['parameters']['hartCount']):
                    probe = f'probe_{hart}'
                    environment = f'''
  reg probe_owned_{hart} = 0;
  always @(posedge clock) if (reset) probe_owned_{hart} <= 0; else begin
    assert(probe_owned_{hart} == (pending[{hart}] && sent[{hart}]));
    assume(!{probe}_response_valid || probe_owned_{hart});
    if ({probe}_response_valid && {probe}_response_ready && {probe}_response_bits_last) probe_owned_{hart} <= 0;
    if ({probe}_request_valid && {probe}_request_ready) begin
      assert(!probe_owned_{hart} || ({probe}_response_valid && {probe}_response_ready && {probe}_response_bits_last));
      probe_owned_{hart} <= 1;
    end
    if ($past(!reset && {probe}_response_valid && !{probe}_response_ready)) begin
      assume({probe}_response_valid);
      assume($stable({{{probe}_response_bits_data, {probe}_response_bits_mask, {probe}_response_bits_word, {probe}_response_bits_last}}));
    end
  end
'''
                    if not manifest['parameters'].get('dCacheWriteback'):
                        environment += f'  always @* if ({probe}_response_valid) assume({probe}_response_bits_data == 0 && {probe}_response_bits_mask == 0 && {probe}_response_bits_word == 0 && {probe}_response_bits_last);\n'
                    files['DitDahA1Coherence.sv'] = files['DitDahA1Coherence.sv'].replace('endmodule', environment + '\nendmodule', 1)
            if manifest['parameters'].get('dCacheWriteback'):
                body += '  always @(posedge clock) if (!reset) begin assert(formal_memory_live == formal_coherence_bus); assert(formal_single_sent == formal_coherence_sent); end\n'
            elif manifest['parameters'].get('dCacheBytes'):
                body += '  always @(posedge clock) if (!reset) begin assert(formal_single_sent == formal_memory_live); assert(formal_coherence_sent == (formal_memory_live && !formal_memory_fault)); assert(formal_axi_live == formal_coherence_bus); assert(!formal_coherence_live || !formal_memory_fault); end\n'
            if manifest['parameters'].get('dCacheBytes'):
                body += '  always @(posedge clock) if (!reset && formal_coherence_tag_valid) assert(formal_coherence_tag == fabric_single_tag);\n'
            for n in range(read_slots):
                body += f'''  always @(posedge clock) if (!reset) begin
    assert(formal_queue_slots[{n*slot_bits+slot_bits-1}] == (fabric_live[{n}] && !fabric_kind[{n}]));
    if (fabric_live[{n}] && !fabric_kind[{n}]) assert(formal_queue_slots[{n*slot_bits}+:{slot_bits-1}] == fabric_owner[{n}]);
    if (fabric_live[{n}] && !fabric_kind[{n}]) assert(formal_queue_slot_tags[{8*n}+:8] == fabric_tags[{n}]);
  end
'''
            body += '  wire [7:0] fabric_single_tag = ' + ' | '.join(
                f'(fabric_live[{n}] && fabric_kind[{n}] ? fabric_tags[{n}] : 0)' for n in range(read_slots)) + ';\n'
            body += f'''  always @(posedge clock) if (!reset) begin
    assert(!formal_memory_live || {"active" if manifest['parameters'].get('dCacheWriteback') else "formal_single_sent"});
    assert(!formal_axi_live || (formal_memory_live && !formal_memory_fault));
  end
  always @(posedge clock) if (!reset) begin
    if (active) assert(formal_arbiter_tag == fabric_single_tag);
    if (formal_memory_live) assert(formal_memory_tag == fabric_single_tag);
    if (formal_axi_live) assert(formal_axi_tag == fabric_single_tag);
  end
'''
            for i in range(count):
                body += f'  always @(posedge clock) if (!reset && fabric_owned[{i}] && !fabric_exclusive[{i}]) assert(formal_queue_tags[{8*i}+:8] == fabric_tag_{i});\n'
            if manifest['parameters'].get('localInterruptBase') is not None:
                body += '''  always @(posedge clock) if (!reset) begin
    assert(!formal_local_live || (formal_memory_live && !formal_memory_fault));
    assert(!(formal_local_live && formal_axi_live));
    if (formal_local_live) assert(formal_local_tag == fabric_single_tag);
  end
'''
            queue_invariants = ''.join(f'assert(!(state{a} != 0 && state{b} != 0) || owner{a} != owner{b});\n' for n, a in enumerate(read_suffixes) for b in read_suffixes[:n])
            queue_invariants += 'assert($onehot0({' + ', '.join('state' + suffix + ' == 2' for suffix in read_suffixes) + '}));\n'
            if manifest['parameters']['axiDataBits'] > 64 and (manifest['parameters'].get('enableBurstRefill') or manifest['parameters'].get('dCacheRefillBytes') == 64):
                queue_invariants += 'assert($onehot0({' + ', '.join('state' + suffix + ' == 5' for suffix in read_suffixes) + '}));\n'
            files['DitDahA1ReadQueue.sv'] = files['DitDahA1ReadQueue.sv'].replace('endmodule',
                'always @(posedge clock) if (!reset) begin\n' + queue_invariants + 'end\nendmodule')
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
            fetch_pins = instance_ports(sources[module + '.sv'], 'DitDahA1Fetch')[0][1]
            body = body.replace('FORMAL_FRONT_REQUEST_PC', '(' + fetch_pins['request_bits_pc'] + ')')
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
                match = re.fullmatch(r'(?:instructions|tags|data|dataTags|dataDirty|mem)_\d+x(\d+)\.sv', filename)
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
                    checking = 'input_valid && input_ready'
                    if manifest['parameters'].get('virtualAddressBits') == 39:
                        checking = 'translation_response_valid && translation_response_ready'
                        expected = {'address': 'translation_response_bits_address', 'size': 'word_size', 'write': 'word_store', 'fetch': "1'b0", 'atomic': 'word_load && word_store', 'privilege': 'word_privilege'}[port]
                    if manifest['parameters'].get('dCacheBytes') and manifest['parameters'].get('dCacheRefillBytes', 8) == 64:
                        expected = {'address': 'word_probe_address', 'size': 'word_probe_size'}.get(port, expected)
                    body += f'\n  wire [{width-1}:0] formal_pmp_{port} = {connections[0]};\n  always @* if (!reset && {checking}) assert(formal_pmp_{port} == ({expected}));\n'
        if enabled and unit == 'Translation':
            files['DitDahA1Pmp.sv'] = license + header(sources['DitDahA1Pmp.sv']) + '\n(* anyseq *) reg permit;\nassign allowed = permit;\nendmodule\n'
            for port, width, expected in (('address', 64, 'walk_address'), ('size', 3, "3'd3"), ('write', 1, "1'b0"),
                                          ('fetch', 1, "1'b0"), ('atomic', 1, "1'b0"), ('privilege', 2, "2'd1")):
                pattern = rf'\.{port}\s*\(([^()]*)\)'
                connections = re.findall(pattern, files[module + '.sv'])
                assert len(connections) == 1, (port, connections)
                files[module + '.sv'] = re.sub(pattern, f'.{port}(formal_pmp_{port})', files[module + '.sv'])
                body += f'\n  wire [{width-1}:0] formal_pmp_{port} = {connections[0]};\n  always @(posedge clock) if (!reset && memory_request_valid && !offered) assert($past(formal_pmp_{port} == ({expected})));\n'
        if unit == 'ReadQueue':
            for slot, suffix in enumerate(read_suffixes):
                update = re.search(r'\bdata' + suffix + r' <=\s*([^;]+);', files[module + '.sv'])
                assert update and 'shifted' in update[1]
                body = body.replace(f'READ_QUEUE_DATA_{slot}', update[1])
                files[module + '.sv'] = files[module + '.sv'].replace(update[0], f'data{suffix} <= rq_word_{slot};', 1)
                candidates = [name for name, expression in re.findall(r'wire\s+(\w+)\s*=\s*([^;]+);', sources[module + '.sv'])
                              if re.match(rf'~request_write{suffix}\s*&\s*~request_atomic{suffix}\s*&', expression)
                              and f'request_address{suffix} ' in expression]
                assert len(candidates) == 1, 'Ambiguous read authorization driver'
                body += f'\n  wire rq_dut_permission_{slot} = {candidates[0]};\n'
        if unit in ('Backend', 'Frontend', 'Gpr', 'Multiply', 'Csr', 'MemoryArbiter', 'ReadQueue', 'MemoryFabric', 'Memory', 'Axi', 'InstructionCache', 'DataCache', 'Coherence', 'Lsu', 'LocalInterrupts', 'Translation') or (enabled and unit not in ('Decode', 'Execute')) or unit == 'Fetch' and manifest['parameters'].get('iCacheBytes'):
            if unit == 'Backend':
                dual = manifest['parameters'].get('loadQueueEntries', 1) == 2
                owned = '{1\'b0, contexts != 0} + {1\'b0, contexts_0 != 0}' if dual else 'state != 0'
                files['DitDahA1Lsu.sv'] = files['DitDahA1Lsu.sv'].replace(');', ', output [1:0] formal_owned);' if dual else ', output formal_owned);', 1).replace('endmodule', f'assign formal_owned = {owned};\nendmodule', 1)
                if dual:
                    fields = dict(instruction_pc=64, instruction_tag=8, instruction_instruction=32,
                                  instruction_length=3, nextPc=64,
                                  load=1, store=1, atomic=1, csrWrite=1, mret=1, sret=1,
                                  wfi=1, fenceI=1, sfenceVma=1, instruction_predictedTaken=1)
                    metadata = lambda prefix: '{' + ', '.join(prefix + field for field in fields) + '}'
                    metadata_bits = sum(fields.values())
                    files['DitDahA1Lsu.sv'] = files['DitDahA1Lsu.sv'].replace(');', f', output [{metadata_bits-1}:0] formal_second);', 1).replace(
                        'endmodule', f'assign formal_second = head ? {metadata("packet_")} : {metadata("packets_")};\nendmodule', 1)
                    files[module + '.sv'], connected = re.subn(r'(DitDahA1Lsu\s+\w+\s*\()', r'\1\n.formal_second(backend_lsu_second),', files[module + '.sv'])
                    assert connected == 1
                    body += f'''  wire [{metadata_bits-1}:0] backend_lsu_second;
  always @(posedge clock) if (!reset && memoryPending && extraPending)
    assert(backend_lsu_second == {metadata('extraPackets_0_')});
'''
                    files['DitDahA1Lsu.sv'] = files['DitDahA1Lsu.sv'].replace('endmodule', '''
  always @(posedge clock) if (!reset) begin
    if (state != 0) assert(owner ? contexts_0 == 1 : contexts == 1);
    if (contexts == 1 || contexts_0 == 1) assert(state != 0);
    assert(!(contexts == 1 && contexts_0 == 1));
    if (head != tail) assert(head ? contexts_0 != 0 && contexts == 0 : contexts != 0 && contexts_0 == 0);
    else assert((contexts == 0) == (contexts_0 == 0));
    if (contexts != 0 || contexts_0 != 0) assert(head ? contexts_0 != 0 : contexts != 0);
  end
endmodule''', 1)
                files[module + '.sv'], connected = re.subn(r'(DitDahA1Lsu\s+\w+\s*\()', r'\1\n.formal_owned(backend_lsu_owned),', files[module + '.sv'])
                assert connected == 1
                body += ('''
  wire [1:0] backend_lsu_owned;
  reg [1:0] backend_memory_owned = 0;
  always @(posedge clock) begin
    if (reset) backend_memory_owned <= 0;
    else begin
      case ({lsu_input_valid && _lsu_input_ready, _lsu_output_valid && lsu_output_ready})
        2'b10: backend_memory_owned <= backend_memory_owned + 1;
        2'b01: backend_memory_owned <= backend_memory_owned - 1;
      endcase
      assert(backend_memory_owned <= 2 && backend_lsu_owned == backend_memory_owned);
      assert(backend_memory_owned == {1'b0, memoryPending} + {1'b0, extraPending});
      if (data_request_valid || data_response_ready || _lsu_output_valid) assert(backend_memory_owned != 0);
    end
  end
''' if dual else '''
  wire backend_lsu_owned;
  reg backend_memory_owned = 0;
  always @(posedge clock) begin
    if (reset) backend_memory_owned <= 0;
    else begin
      if (lsu_input_valid && _lsu_input_ready) begin assert(!backend_memory_owned); backend_memory_owned <= 1; end
      if (_lsu_output_valid && lsu_output_ready) begin assert(backend_memory_owned); backend_memory_owned <= 0; end
      assert(memoryPending == backend_memory_owned && backend_lsu_owned == backend_memory_owned);
      if (data_request_valid || data_response_ready || _lsu_output_valid) assert(backend_memory_owned);
    end
  end
''')
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
        if name == 'LsuReads':
            checks += [('mutation-value', 'assign output_bits_value =', "assign output_bits_value = 64'h1 ^"),
                       ('mutation-cancel', 'assign memory_request_valid =', 'assign memory_request_valid = ~cancel &')]
        if unit == 'MemoryFabric':
            original = sources[module + '.sv']
            tag_modes = [f'prove-tags-{bit}' for bit in range(8)] if read_slots > 2 else ['prove-tags']
            port_modes = [f'prove-ports-{port}' for port in range(0, 32, 8)] if read_slots > 2 and manifest['parameters']['hartCount'] == 16 else []
            checks[:1] = [(mode, before, after) for mode in ('prove-control', *port_modes, *tag_modes, *(f'prove-stability-{i}' for i in range(2 * manifest['parameters']['hartCount'])))]
            payload = re.search(r'assign\s+instruction_0_response_bits_data\s*=[^;]+;', original).group()
            checks += [('mutation-data', payload, payload.replace('=', '= axi_r_bits_data[63:0] ^ (', 1).replace(';', ');'))]
            if manifest['parameters'].get('dCacheWriteback') and cache_routing_base is not None:
                guard = re.search(r"data_0_request_bits_cacheOperation == 2'h0", original).group()
                checks.append(('mutation-cache-routing', guard, "1'h1"))
            drain = re.search(r'wire\s+allowExclusive\s*=[^;]+;', original).group()
            isolate = re.search(r'wire\s+allowRead\s*=[^;]+;', original).group()
            checks += [('mutation-drain', drain, drain.replace('_readers_empty', "1'h1")),
                       ('mutation-isolation', isolate, isolate.replace('~active', "1'h1")),
                       ('mutation-fairness', isolate, re.sub(r'=\s*~active\s*&.*;', '= ~active;', isolate, flags=re.S))]
        if unit == 'Gpr':
            lane = manifest['parameters']['issueWidth'] - 1
            write = re.search(rf"if \(we_{lane} & waddr_{lane} == 5'h1\)", sources[module + '.sv']).group()
            checks += [('mutation-write', write, "if (1'h0)")]
        if name == 'PipelineBackend':
            bindings = re.findall(r'\.rdata1\s*\([^()]*\)', sources[module + '.sv'])
            assert len(bindings) == manifest['parameters']['issueWidth'], bindings
            checks += [('mutation-forward', bindings[-1], f'.rdata1(_gpr_rdata1_{len(bindings)-1})')]
            if manifest['parameters'].get('loadQueueEntries', 1) == 2:
                advance = re.search(r'wire\s+memoryAdvance\s*=[^;]+;', sources[module + '.sv']).group()
                assert '~memoryFault | ~extraPending' in advance
                checks += [('mutation-dual-owner', 'memoryPackets_0_instruction_pc <= extraPackets_0_instruction_pc;',
                            "memoryPackets_0_instruction_pc <= 64'h0;"),
                           ('mutation-dual-drain', advance, advance.replace('~memoryFault | ~extraPending', "1'h1"))]
            if manifest['parameters']['issueWidth'] > 1:
                prefix = re.search(r'wire\s+prefix_1\s*=[^;]+;', sources[module + '.sv']).group()
                assert 'decodedPackets_0_writesRd' in prefix
                checks += [('mutation-dependency', prefix, prefix.replace('decodedPackets_0_writesRd', "1'h0"))]
        if name == 'PipelineBackend':
            checks[2:2] = [(mode, before, after) for mode in ('cover-memory', 'cover-recovery') +
                          (('cover-dual', 'cover-drain') if manifest['parameters'].get('loadQueueEntries', 1) == 2 else ()) +
                          (('cover-dependency',) if manifest['parameters']['issueWidth'] > 1 else ())]
            original = sources[module + '.sv']
            early = re.search(r'wire\s+earlyRedirect\s*=[^;]+;', original).group()
            younger = re.search(r'resultCount <=\s*~redirect_0[^;]+;' if manifest['parameters']['issueWidth'] == 1
                                else r'if \(redirect_0\) begin\s+issuedCount', original).group()
            checks += [('mutation-recovery-missing', early, early.split('=')[0] + '= 0;'),
                       ('mutation-recovery-owner', younger, younger.replace('redirect_0', 'flushYounger')),
                       ('mutation-recovery-retirement', '~commitResolved', "1'h1")]
            if manifest['parameters'].get('enableBranchPrediction'):
                metadata = re.search(r'issuedPackets_0_decoded_instruction_predictedTaken <=\s*([^;]+);', original).group()
                checks += [('mutation-recovery-metadata', metadata, metadata.replace('<=', "<= (decodedPackets_0_instruction_instruction[6:0] == 7'h6f) ^"))]
            if manifest['parameters']['issueWidth'] > 1:
                count = re.search(r'wire\s+\[[^]]+\]\s+retireCount_layerCapture\s*=[^;]+;', original).group()
                checks += [('mutation-memory-fault', count, count.split('=')[0] + '= _commit_output_valid ? commitCount : 0;')]
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
        if name == 'WfiFrontend' and manifest['parameters'].get('enableBranchPrediction'):
            original = sources[module + '.sv']
            fetch_pc = re.search(r'\.request_bits_pc\s*\([^()]*\)', original).group()
            metadata = re.search(r'assign output_bits_packets_0_predictedTaken\s*=[^;]+;', original).group()
            checks += [('mutation-prediction-target', fetch_pc, '.request_bits_pc(pc)'),
                       ('mutation-prediction-metadata', metadata, 'assign output_bits_packets_0_predictedTaken = 0;')]
            if manifest['parameters']['issueWidth'] > 1 and manifest['parameters'].get('iCacheBytes'):
                count = re.search(r'wire\s+\[[^]]+\]\s+returnedCount\s*=[^;]+;', original).group()
                checks += [('mutation-prediction-count', count, count.split('=')[0] + '= returned ? _fetch_output_bits_count : 0;')]
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
                fault_output = re.search(r'assign ports_0_response_bits_fault\s*=\s*([^;]+);', original)[1]
                denied_name = re.search(r':\s*(\w+)\s*$', fault_output)[1]
                denied = re.search(rf'wire\s+{denied_name}\s*=\s*(\w+)\s*\|[^;]+;', original)
                checks += [('mutation-tlb-flush', invalidate.group(), invalidate[1] + 'tlbValid <= tlbValid;'),
                           ('mutation-tlb-refill', 'refillAllowed & ~invalidate', "1'h1"),
                           ('mutation-tlb-permission', denied.group(), f"wire {denied_name} = {denied[1]};"),
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
        if name == 'PmpDecode' and (manifest['parameters'].get('enableBurstRefill') or manifest['parameters'].get('dCacheRefillBytes', 8) == 64):
            checks += [('mutation-line-range', "65'h40", "65'h8")]
        if name == 'PmpDecode' and manifest['parameters'].get('iCacheBytes') and manifest['parameters']['issueWidth'] == 3:
            checks += [('mutation-fetch-range', "+ 65'h10}", "+ 65'h8}")]
        if unit == 'Axi':
            original = sources[module + '.sv']
            retry_state = re.findall(r"state <= \w+ \? 3'h1 : 3'h4;", original)[0]
            read_fault = re.search(r'amo & ~\w+', original).group()
            response_data = re.search(r'assign memory_response_bits_data\s*=\s*([^;]+);', original).group()
            checks[2] = ('mutation', 'request_atomic <= memory_request_bits_atomic;', 'request_atomic <= 0;')
            if manifest['parameters']['axiDataBits'] == 512:
                checks[:1] = [(mode, before, after) for mode in ('prove-control', 'prove-payload')]
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
        if unit == 'Axi' and (manifest['parameters'].get('enableBurstRefill') or manifest['parameters'].get('dCacheRefillBytes', 8) == 64):
            last = re.search(r'assign memory_response_bits_last\s*=\s*[^;]+;', original).group()
            checks += [('mutation-line-last', last, 'assign memory_response_bits_last = 1;'),
                       ('mutation-line-data', response_data, response_data.replace('=', '= axi_request_line ? 0 :', 1))]
            if manifest['parameters']['axiDataBits'] > 64:
                step = re.search(r"slice <= slice \+ \d+'h1;", original).group()
                checks += [('mutation-line-order', step, step.replace("'h1", "'h0"))]
        if name == 'Pmp':
            checks += [('mutation-atomic-read', 'state_config[0] & state_config[1]', 'state_config[1]'),
                       ('mutation-atomic-write', 'state_config[0] & state_config[1]', 'state_config[0]')]
        if unit == 'Lsu' and name != 'LsuReads':
            mask_assignment = re.search(r'assign memory_request_bits_mask\s*=\s*[^;]+;', sources[module + '.sv']).group(0)
            checks += [('mutation-mask', mask_assignment,
                        "assign memory_request_bits_mask = 8'hff;"),
                       ('mutation-extension', 'assign output_bits_value = packet_value;',
                        "assign output_bits_value = {32'd0, packet_value[31:0]};")]
            refill_assignment = re.search(r'assign memory_request_bits_refillSize\s*=\s*[^;]+;', sources[module + '.sv']).group()
            checks += [('mutation-refill-certificate', refill_assignment, "assign memory_request_bits_refillSize = 3'd6;")]
            if enabled:
                denial = next(declaration for declaration in re.findall(r'wire\s+\w+\s*=[^;]+;', sources[module + '.sv']) if '~_pmp_allowed' in declaration)
                checks += [('mutation-permission', denial, denial.replace('~_pmp_allowed', "1'h0"))]
                checks += [('mutation-pmp-direction', 'wire [0:0] formal_pmp_atomic =', "wire [0:0] formal_pmp_atomic = 1'h0 &")]
            original = sources[module + '.sv']
            update = re.search(r'reserved <= (\w+) \| ~\([^;]+;', original).group()
            pair = re.search(r'scEligible <=[^;]+;', original).group()
            success = re.search(r'wire\s+(\w+)\s*=\s*[^;]*packet_atomic[^;]*~memory_response_bits_fault[^;]+;', original).group()
            checks += [('mutation-consume', update, re.sub(r'~\([^;]+?\) & reserved', 'reserved', update)),
                       ('mutation-pair', pair, "scEligible <= 1'h0;"),
                       ('mutation-alias', pair, f"scEligible <= input_bits_atomic & input_bits_instruction_instruction[31:27] == 3 & reserved & input_bits_address[{manifest['parameters']['physicalAddressBits']-1}:3] == reservedWord & input_bits_memorySize == 3;"),
                       ('mutation-lr-fault', success, success.replace('~memory_response_bits_fault', "1'h1"))]
            if manifest['parameters'].get('virtualAddressBits') == 39:
                assignment = re.search(r'assign memory_request_bits_address\s*=[^;]+;', original).group()
                checks.append(('mutation-translated-address', assignment, 'assign memory_request_bits_address = packet_address;'))
                if enabled:
                    assignment = re.search(r'wire \[1:0\] formal_pmp_privilege =[^;]+;', body).group()
                    checks.append(('mutation-translated-privilege', assignment, 'wire [1:0] formal_pmp_privilege = privilege;'))
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
        if name == 'DataCacheWriteback':
            original = sources[module + '.sv']
            store_update = re.search(r'wire\s+storeUpdating\s*=[^;]+;', original).group()
            checks += [('mutation-store-missing', store_update, store_update.replace('storeHit', "1'h0"))]
            dirty_ports = instance_ports(original, *cache_memories[-1][:2])[0][0]
            dirty_data = re.search(r'\.W0_data\s*\(.*?\)(?=\s*,|\s*$)', dirty_ports, re.S).group()
            word_output = re.search(r'assign probe_response_bits_word =[^;]+;', original).group()
            checks += [('prove-storage-shape', before, after), ('prove-storage-bytes', before, after),
                       ('prove-storage', before, after), ('cover-storage', before, after),
                       ('mutation-storage-mask', dirty_data, '.W0_data (8\'hff)'),
                       ('mutation-storage-word', word_output, word_output.replace('probeWord', "(probeWord ^ 3'h1)"))]
        if unit == 'DataCache' and name != 'DataCacheWriteback':
            original = sources[module + '.sv']
            store_update = re.search(r'wire\s+storeUpdating\s*=[^;]+;', original).group()
            store_data = re.search(r'\bdata & ~\(storeMask\[63:0\]\)[^\n]+', original).group()
            store_failure = 'storeComplete & responseFault'
            checks += [('mutation-store-update', store_update, store_update.replace('storeHit', "1'h0")),
                       ('mutation-store-mask', store_data, store_data.replace('storeMask[63:0]', "64'hffffffffffffffff")),
                       ('mutation-store-invalidate', store_update, store_update.replace('~invalidated', "1'h1")),
                       ('mutation-store-error', store_failure, store_failure.replace('responseFault', "1'h0"))]
            retry = re.search(r'wire\s+\w+\s*=\s*expanded & responseFault;', sources[module + '.sv']).group()
            expanded_update, = [update for update in re.findall(r'expanded <=[^;]+;', sources[module + '.sv']) if 'request_refillSize' in update]
            checks += [('mutation-refill-permission', expanded_update, re.sub(r'\(request_refillSize == 3\x27h3 \| (?:\w+|request_refillSize == 3\x27h6)\)', "1'h1", expanded_update)),
                       ('mutation-refill-retry', retry, retry.replace('expanded & responseFault', "1'h0")),
                       ('mutation-read-offset', "{58'h0, request_address[2:0], 3'h0}", "64'h0")]
            write_enable = re.search(r'\.W0_en\s*\([^\n]+\)', data_ports[0][0]).group()
            checks += [('mutation-hold', 'assign downstream_request_valid =',
                        'assign downstream_request_valid = ~invalidate_valid &'),
                       ('mutation-allocation', data_ports[0][0], data_ports[0][0].replace(write_enable, '.W0_en (1\'h1)')),
                       ('mutation-authorization', re.search(r'wire\s+eligible(?:_layerCapture)?\s*=', sources[module + '.sv']).group(), re.search(r'wire\s+eligible(?:_layerCapture)?\s*=', sources[module + '.sv']).group() + " 1'h1 |"),
                       ('mutation-tag-lifetime', '{' + str(manifest['parameters']['dCacheBytes'] // 8) + '{sameTag}}',
                        '{' + str(manifest['parameters']['dCacheBytes'] // 8) + '{hit_0}}'),
                       ('mutation-valid-hit', 'hit[0] & hit_0', "1'h1 & hit_0")]
            if manifest['parameters'].get('dCacheRefillBytes', 8) == 64:
                checks.insert(2, ('cover-line', before, after))
                original = sources[module + '.sv']
                publish = re.search(r'wire\s+publish\s*=[^;]+;', original).group()
                line_fill = re.search(r'wire\s+lineFilling\s*=[^;]+;', original).group()
                line_candidate = re.search(r'wire\s+lineCandidate\s*=[^;]+;', original).group()
                line_grant = re.search(r'wire\s+(\w+)\s*=\s*request_refillSize == 3\x27h6;', original).group(1)
                write_address = re.search(r'\.W0_addr\s*\([^\n]+\)', data_ports[0][0]).group()
                line_update = next(update for update in re.findall(r'line <=[^;]+;', original) if 'reading' in update)
                checks += [('mutation-line-grant', line_candidate, line_candidate.replace('& ' + line_grant, "& 1'h1")),
                           ('mutation-line-publication', publish, 'wire publish = lineFilling;'),
                           ('mutation-line-invalidate', line_fill, line_fill.replace('~invalidated', "1'h1")),
                           ('mutation-line-address', write_address, write_address.replace('beat}', "3'h0}")),
                           ('mutation-line-retry', line_update, line_update.replace('<=', '<= fault |', 1))]
        if unit == 'ReadQueue':
            payload_modes = [f'prove-payload-bits-{bit}' for bit in range(0, 64, read_bit_step)] if manifest['parameters']['hartCount'] > 2 or manifest['parameters']['axiDataBits'] > 64 else ['prove-payload']
            storage_modes = [mode.replace('payload', 'storage') for mode in payload_modes]
            if read_bit_step == 4:
                payload_modes = [f'{mode}-ports-{port}' for mode in payload_modes for port in range(0, 32, 8)]
            response_modes = [f'prove-response-{port}' for port in range(0, 32, 8)] if read_slots > 2 and manifest['parameters']['hartCount'] == 16 else []
            checks[:1] = [(mode, before, after) for mode in ('prove-permission', 'prove-permission-hold', 'prove-read-data', 'prove-control', *response_modes, *storage_modes, *payload_modes)]
            if read_slots > 1:
                checks += [('prove-schedule', before, after), ('cover-schedule', before, after)]
            if manifest['parameters']['hartCount'] > 2:
                cover_index = next(i for i, check in enumerate(checks) if check[0] == 'cover')
                checks[cover_index:cover_index+1] = [('cover-global', before, after)] + [(f'cover-harts-{hart}', before, after) for hart in range(0, manifest['parameters']['hartCount'], 4)]
            original = sources[module + '.sv']
            if read_slots > 1:
                selected = re.findall(r'addressNext <=[^;]+;', original)[-1]
                checks.append(('mutation-schedule', selected, 'addressNext <= 0;'))
            shifted = re.search(r'wire\s+\[[^]]+\]\s+shifted\s*=[^;]+;', original).group()
            offset = re.search(r'request_address\[[^]]+\]', shifted).group()
            checks.append(('mutation-lane', shifted, shifted.replace(offset, "6'h0")))
            permission = re.search(r'wire rq_dut_permission_0 = (\w+);', body)[1]
            update = re.search(r'wire\s+' + permission + r'\s*=[^;]+;', original).group()
            checks.append(('mutation-permission', update, update.split('=', 1)[0] + "= 1'h1;"))
            peer = min(2, 2 * manifest['parameters']['hartCount'] - 1)
            update = re.search(rf'assign ports_{peer}_response_valid\s*=[^;]+;', original).group()
            checks.append(('mutation-route', update, f'assign ports_{peer}_response_valid = ports_0_response_valid;'))
            for mode, signal in (('tag', 'ports_0_response_bits_tag'), ('data', 'ports_0_response_bits_data'), ('id', 'ar_bits_id')):
                update = re.search(r'assign ' + signal + r'\s*=[^;]+;', original).group()
                checks.append(('mutation-' + mode, update, 'assign ' + signal + f" = {int(mode == 'id')};"))
            if manifest['parameters'].get('enableBurstRefill') or manifest['parameters'].get('dCacheRefillBytes') == 64:
                update = re.search(r'assign ports_0_response_bits_last\s*=[^;]+;', original).group()
                checks.append(('mutation-line-last', update, 'assign ports_0_response_bits_last = 1;'))
                if manifest['parameters']['axiDataBits'] < 512:
                    update = re.search(r'ports_0_response_ready[^;]*?beat\s*<=\s*beat \+ 3\x27h1;', original).group()
                    checks.append(('mutation-line-count', update, update.replace("+ 3'h1", "+ 3'h0")))
                if manifest['parameters']['axiDataBits'] > 64:
                    update = re.findall(r'(?:else if \([^;]*?\)\s*)?slice <=[^;]+;', original)[-1]
                    checks.append(('mutation-line-order', update, re.sub(r'slice <=[^;]+;', 'slice <= 0;', update)))
            checks.append(('mutation-sticky-fault', 'fault | poisoned', 'poisoned'))
            update = re.search(r'assign empty\s*=[^;]+;', original).group()
            checks.append(('mutation-fault-release', update, update.replace('~poisoned', "1'h1")))
            if read_slots > 2:
                checks.append(('mutation-capacity', 'assign empty =', f'assign empty = (state{read_suffixes[-1]} != 0) |'))
        if unit == 'Coherence':
            failure = re.search(r'wire\s+writebackFault\s*=[^;]+;', sources[module + '.sv']).group()
            checks += [('mutation-probe-offer', 'assign probe_0_request_valid =', "assign probe_0_request_valid = 1'h0 &"),
                       ('mutation-acknowledgement', 'assign probe_0_response_ready =', "assign probe_0_response_ready = 1'h1 |"),
                       ('mutation-writeback-error', failure, "wire writebackFault = 1'h0;")]
        if name == 'PipelineBackend' and manifest['parameters']['issueWidth'] > 1:
            checks[:1] = [(f'prove-bits-{bit}', before, after) for bit in range(0, 97 if manifest['parameters'].get('enableBranchPrediction') else 96, 4 if manifest['parameters']['issueWidth'] == 3 else 8)]
        if name == 'PipelineBackend' and manifest['parameters'].get('loadQueueEntries', 1) == 2:
            checks[:0] = [('prove-control', before, after)]
            checks = [('prove-identity' if mode == 'prove' else mode, *rest) for mode, *rest in checks]
            checks.sort(key=lambda check: check[0].startswith('prove'))
        proof_top = top
        for check in checks:
            top = proof_top
            files.pop('witness.sv', None)
            mode, before, after, *target = check
            if mutations is not None and mode not in mutations:
                continue
            mutated_file = target[0] if target else module + '.sv'
            mutating = mode.startswith('mutation')
            proving = mode.startswith('prove')
            witness = ({'WfiBackend': wfi_witness, 'SynchronizationBackend': synchronization_witness,
                        'InterruptBackend': interrupt_witness}.get(name) or
                       (pipeline_witness if name == 'PipelineBackend' and (mode.startswith('cover') or mutating) else None) or
                       (resource_witness if name == 'Backend' else None)) if not proving else None
            work = directory / f'{name.lower()}-{mode}'
            work.mkdir(exist_ok=True)
            for filename, text in files.items():
                if name == 'PipelineBackend' and manifest['parameters'].get('loadQueueEntries', 1) == 2 and proving:
                    def partition_pipeline(match):
                        identity = '[pipeline_bit]' in match[0]
                        return ('assert(1);' if identity else match[0]) if mode == 'prove-control' else match[0] if identity else match[0].replace('assert(', 'assume(', 1)
                    text = re.sub(r'\bassert\([^;]+;', partition_pipeline, text)
                if name == 'DataCacheWriteback' and 'storage' in mode:
                    if filename == module + '.sv':
                        if mutating:
                            text = re.sub(r'\bassert\([^;]+;', 'assert(1);', text)
                        elif proving:
                            text = text.replace('assert(', 'assume(')
                        authorization = writeback_storage_case(manifest['parameters'])
                        active = ('SHAPE', 'BYTES', 'FRAME').index({'prove-storage-shape': 'SHAPE', 'prove-storage-bytes': 'BYTES'}.get(mode, 'FRAME'))
                        for position, role in enumerate(('SHAPE', 'BYTES', 'FRAME')):
                            if proving and position > active:
                                authorization = re.sub(r'AUTH_' + role + r'\([^;]+;', 'assert(1);', authorization)
                            authorization = authorization.replace('AUTH_' + role + '(', 'assume(' if proving and position < active else 'assert(')
                        text = text.replace('endmodule', authorization + '\nendmodule', 1)
                        for memory, instance, prefix in cache_memories[1:]:
                            watch = 'auth_watched' + ('[' + str((manifest['parameters']['dCacheBytes'] // 8 - 1).bit_length()-1) + ':3]' if prefix == 'TAG' else '')
                            text, bound = re.subn(r'(' + memory + r'\s+' + instance + r'\s*\()',
                                rf'\1 .formal_watch({watch}), .formal_value(auth_native_{"tag" if prefix == "TAG" else "dirty"}),', text)
                            assert bound == 1
                    elif filename in watched_types:
                        text = license + watched_memory_model(sources[filename])
                if unit == 'MemoryFabric' and filename == 'DitDahA1ReadQueue.sv' and mode.startswith(('prove-ports-', 'prove-tags', 'prove-stability-')):
                    text = text.replace('assert(', 'assume(')
                if unit == 'MemoryFabric' and filename == module + '.sv' and mode.startswith('prove-'):
                    def partition_fabric(match):
                        expression = match[0]
                        port = re.search(r'\b((?:instruction|data)_\d+)_response_bits_data\b', expression)
                        endpoint = re.search(r'\b(instruction|data)_(\d+)_', expression)
                        tag = 'tag' in expression
                        if mode == 'prove-control': return 'assert(1);' if port or tag or port_modes and endpoint else expression
                        if mode.startswith('prove-ports-'):
                            if port or tag: return 'assert(1);'
                            if not endpoint: return expression.replace('assert(', 'assume(', 1)
                            first = int(mode.rsplit('-', 1)[1])
                            index = 2 * int(endpoint[2]) + int(endpoint[1] == 'data')
                            return expression if first <= index < first + 8 else 'assert(1);'
                        if mode.startswith('prove-tags'):
                            if port: return 'assert(1);'
                            if not tag: return expression.replace('assert(', 'assume(', 1)
                            if mode != 'prove-tags':
                                bit = int(mode.rsplit('-', 1)[1])
                                expression = re.sub(r'(formal_queue(?:_slot)?_tags)\[(\d+)\+:8\]', lambda m: f'{m[1]}[{int(m[2])+bit}]', expression)
                                expression = re.sub(r'fabric_tags\[(\d+)\]', rf'fabric_tags[\1][{bit}]', expression)
                                expression = re.sub(r'\b(\w*(?:_tag|_tag_\d+))\b', rf'\1[{bit}]', expression)
                            return expression
                        if not port: return expression.replace('assert(', 'assume(', 1)
                        i = int(mode.rsplit('-', 1)[1])
                        return expression if port[1] == f"{'instruction' if i % 2 == 0 else 'data'}_{i//2}" else 'assert(1);'
                    text = re.sub(r'\bassert\([^;]+;', partition_fabric, text)
                if unit == 'MemoryFabric' and filename == module + '.sv' and mode in ('cover', 'mutation', 'mutation-drain', 'mutation-isolation', 'mutation-fairness') and manifest['parameters']['hartCount'] == 16:
                    base = next((int(r['base']) + 7) & ~7 for r in manifest['parameters']['memoryRegions'] if r['executable'] and r['writable'] and not r['device'] and
                                (mode != 'mutation' or r['atomic']) and
                                ((int(r['base']) + 7) & ~7) + 8 <= int(r['base']) + int(r['size']))
                    read_base = next((int(r['base']) + 7) & ~7 for r in manifest['parameters']['memoryRegions'] if r['executable'] and r['readable'] and not r['device'] and (not manifest['parameters'].get('dCacheWriteback') or not r.get('dataCacheable')))
                    guidance = '  (* anyconst *) reg fabric_read_scenario;\n  always @* begin\n    assume(fabric_read_scenario || data_15_request_valid);\n    assume(axi_ar_ready && axi_r_bits_data == 0 && axi_r_bits_resp == 0 && axi_r_bits_last);\n'
                    if mutating:
                        guidance += f'    assume(fabric_read_scenario == {int(mode != "mutation")});\n'
                    readers = 1 if mode == 'mutation-isolation' else read_slots
                    for port in range(32):
                        prefix = f'{"instruction" if port % 2 == 0 else "data"}_{port//2}_request'
                        if port != 31:
                            guidance += f'    assume({prefix}_valid == {"fabric_read_scenario" if port % 2 == 0 and port // 2 < readers else "0"});\n'
                        guidance += f"    assume({prefix}_bits_cacheOperation == 0 && {prefix}_bits_address == 64'd{base if port == 31 else read_base} && {prefix}_bits_size == {3 if port == 31 else 2} && {prefix}_bits_tag == 0 && {prefix}_bits_data == 0 && {prefix}_bits_mask == 255);\n"
                        guidance += f'    assume({prefix}_bits_atomic == {int(port == 31 and mode == "mutation")} && {prefix}_bits_atomicOperation == 0 && {prefix}_bits_write == {int(port == 31)} && {prefix}_bits_fetch == {int(port != 31)});\n'
                    text = text.replace('\nendmodule', '\n' + guidance + '  end\nendmodule')
                if unit == 'MemoryFabric' and filename == module + '.sv' and mode == 'mutation-cache-routing':
                    base = cache_routing_base
                    guidance = f"  always @* begin assume(data_0_request_valid && data_0_request_bits_cacheOperation == 2 && data_0_request_bits_address == 64'd{base} && data_0_request_bits_size == 3 && !data_0_request_bits_write && !data_0_request_bits_atomic && !data_0_request_bits_fetch);\n"
                    for port in range(2 * manifest['parameters']['hartCount']):
                        if port != 1:
                            guidance += f'    assume(!{"instruction" if port % 2 == 0 else "data"}_{port//2}_request_valid);\n'
                    text = text.replace('\nendmodule', '\n' + guidance + '  end\nendmodule')
                if unit == 'MemoryFabric' and filename == module + '.sv' and mode == 'mutation-data' and manifest['parameters']['hartCount'] > 2:
                    region = next(r for r in manifest['parameters']['memoryRegions'] if r['executable'] and not r['device'] and int(r['size']) >= 4)
                    guidance = f'''  reg fabric_witness_pending = 0;
  always @(posedge clock) if (reset) fabric_witness_pending <= 0;
    else if (axi_ar_valid && axi_ar_ready) fabric_witness_pending <= 1;
    else if (axi_r_valid && axi_r_ready) fabric_witness_pending <= 0;
  always @* begin
    assume(instruction_0_request_valid && !instruction_0_response_ready && axi_ar_ready && fabric_bit == 0);
    assume(!instruction_0_request_bits_write && !instruction_0_request_bits_atomic && instruction_0_request_bits_fetch);
    assume(instruction_0_request_bits_size == 2 && instruction_0_request_bits_address == 64'd{(int(region['base']) + 3) & ~3});
    assume(axi_r_valid == fabric_witness_pending && axi_r_bits_id == 0 && axi_r_bits_last && axi_r_bits_resp == 0);
'''
                    for port in range(1, 2 * manifest['parameters']['hartCount']):
                        guidance += f'    assume(!{"instruction" if port % 2 == 0 else "data"}_{port//2}_request_valid);\n'
                    text = text.replace('\nendmodule', '\n' + guidance + '  end\nendmodule')
                if unit == 'Axi' and filename == module + '.sv' and mode in ('prove-control', 'prove-payload'):
                    def partition_axi(match):
                        expression = match.group()
                        payload = re.search(r'\b(request_data|old_value|axi_w_bits_data|memory_response_bits_data|block)\b', expression)
                        if mode == 'prove-control':
                            return 'assert(1);' if payload else expression
                        return expression if payload else expression.replace('assert(', 'assume(', 1)
                    text = re.sub(r'\bassert\([^;]+;', partition_axi, text)
                if unit == 'ReadQueue' and filename == module + '.sv':
                    read_body = "  (* anyconst *) reg [5:0] rq_bit;\n"
                    for slot, suffix in enumerate(read_suffixes):
                        expression = re.search(r'wire \[63:0\] rq_word_' + str(slot) + r' =[^;]+;', body).group()
                        read_body += expression + '\n'
                        lane_bits = (manifest['parameters']['axiDataBits'] // 8 - 1).bit_length()
                        offset = f'(request_address{suffix}[{lane_bits-1}:0] * 8 + rq_bit)'
                        expected = f"(request_size{suffix} <= 3 && rq_bit < (7'd8 << request_size{suffix}) && {offset} < {manifest['parameters']['axiDataBits']} && r_bits_data[{offset}])"
                        if manifest['parameters'].get('enableBurstRefill') or manifest['parameters'].get('dCacheRefillBytes') == 64:
                            line = f"!request_write{suffix} && !request_atomic{suffix} && request_size{suffix} == 6 && (request_fetch{suffix} ? {int(bool(manifest['parameters'].get('enableBurstRefill')))} : {int(manifest['parameters'].get('dCacheRefillBytes') == 64)})"
                            expected = f"(state{suffix} == 6 ? 1'b0 : (state{suffix} == 3 && {line}) ? r_bits_data[rq_bit] : {expected})"
                        read_body += f'  always @* assert(rq_word_{slot}[rq_bit] == {expected});\n'
                    permission_body = '\n'.join(line for line in body.splitlines() if 'wire rq_permission_' in line or 'wire rq_dut_permission_' in line)
                    permission_body += '\n  always @* begin ' + ' '.join(f'assert(rq_dut_permission_{n} == rq_permission_{n});' for n in range(read_slots)) + ' end\n'
                    if mode in ('prove-schedule', 'cover-schedule', 'mutation-schedule'):
                        text = text.replace(body, read_schedule_case(read_slots) + '\n'.join(re.findall(r'wire (?:rq_dut_permission_\d|\[63:0\] rq_word_\d) =[^;]+;', body)))
                    elif mode in ('prove-permission', 'mutation-permission'):
                        text = text.replace(body, permission_body + '\n'.join(re.findall(r'wire \[63:0\] rq_word_\d =[^;]+;', body)))
                    elif mode == 'prove-permission-hold':
                        hold = '\n'.join(re.findall(r'wire (?:rq_dut_permission_\d|\[63:0\] rq_word_\d) =[^;]+;', body))
                        hold += '\n  reg permission_past = 0;\n  always @(posedge clock) begin\n    permission_past <= 1;\n    if (!permission_past) assume(reset); else assume(!reset);\n'
                        for slot, suffix in enumerate(read_suffixes):
                            hold += f'    if (permission_past && $past(!reset && state{suffix} != 0)) assert($stable(rq_dut_permission_{slot}));\n'
                        text = text.replace(body, hold + '  end\n')
                    elif mode in ('prove-read-data', 'mutation-lane'):
                        text = text.replace(body, read_body)
                    else:
                        for slot, suffix in enumerate(read_suffixes):
                            text = re.sub(r'wire rq_permission_' + str(slot) + r' =[^;]+;',
                                          f'wire rq_permission_{slot} = rq_dut_permission_{slot};', text)
                        if mode == 'prove-control' or mode.startswith(('prove-response', 'prove-storage', 'prove-payload')):
                            for slot, suffix in enumerate(read_suffixes):
                                driver = re.search(r'wire rq_dut_permission_' + str(slot) + r' = (\w+);', body)[1]
                                shape = f'!request_write{suffix} && !request_atomic{suffix} && (request_size{suffix} <= 3 || (request_size{suffix} == 6 && (request_fetch{suffix} ? {int(bool(manifest["parameters"].get("enableBurstRefill")))} : {int(manifest["parameters"].get("dCacheRefillBytes") == 64)})))'
                                text, changed = re.subn(r'wire\s+' + driver + r'\s*=[^;]+;',
                                    f'(* anyseq *) reg rq_grant_{slot}; wire {driver} = rq_grant_{slot} && {shape};', text)
                                assert changed == 1
                                text = text.replace('\nendmodule', f'\n  always @(posedge clock) if (rq_past && $past(!reset && state{suffix} != 0)) assume($stable(rq_dut_permission_{slot}));\nendmodule')
                            def partition(match):
                                expression = match.group()
                                payload = any(token in expression for token in ('rq_address', 'rq_offset', 'rq_data', 'rq_bit',
                                    *(() if manifest['parameters'].get('loadQueueEntries', 1) == 2 else ('rq_tag',))))
                                port = re.search(r'ports_(\d+)_', expression)
                                if mode == 'prove-control':
                                    return 'assert(1);' if payload or response_modes and port else expression
                                if mode.startswith('prove-response-'):
                                    if payload: return 'assert(1);'
                                    if not port: return expression.replace('assert(', 'assume(', 1)
                                    first = int(mode.rsplit('-', 1)[1])
                                    return expression if first <= int(port[1]) < first + 8 else 'assert(1);'
                                if not payload: return expression.replace('assert(', 'assume(', 1)
                                if mode.startswith('prove-storage'):
                                    return 'assert(1);' if 'ports_' in expression else expression
                                if port and '-ports-' in mode:
                                    first = int(mode.rsplit('-', 1)[1])
                                    if not first <= int(port[1]) < first + 8: return 'assert(1);'
                                return expression if 'ports_' in expression else expression.replace('assert(', 'assume(', 1)
                            text = re.sub(r'\bassert\([^;]+;', partition, text)
                        if mode.startswith(('prove-storage-bits-', 'prove-payload-bits-')):
                            declaration = '(* anyconst *) reg [5:0] rq_bit;'
                            assert text.count(declaration) == 1
                            bits = (read_bit_step - 1).bit_length()
                            text = text.replace(declaration, f"(* anyconst *) reg [{bits-1}:0] rq_bit_offset; "
                                                f"wire [5:0] rq_bit = {{{6-bits}'b0, rq_bit_offset}} + 6'd{mode.split('-bits-', 1)[1].split('-')[0]};")
                if unit == 'ReadQueue' and filename == module + '.sv' and mode.startswith('cover-') and mode != 'cover-schedule':
                    first_hart = None if mode == 'cover-global' else int(mode.rsplit('-', 1)[1])
                    def select_cover(match):
                        hart = re.search(r'rq_hart_(\d+)_', match[0])
                        selected = first_hart is not None and first_hart <= int(hart[1]) < first_hart + 4 if hart else first_hart is None
                        return match[0] if selected else ''
                    text = re.sub(r'^\s*cover\([^;\n]+;\n', select_cover, text, flags=re.M)
                    if read_slots > 2 and manifest['parameters']['hartCount'] == 16:
                        harts = [0, 1, 2, 15] if first_hart is None else range(first_hart, first_hart + 4)
                        region = next(r for r in manifest['parameters']['memoryRegions'] if not r['device'] and r['executable'] and
                                      ((int(r['base']) + 63) & ~63) + 64 <= int(r['base']) + int(r['size']))
                        guidance = '  always @* begin\n    assume(r_bits_data == 0 && rq_bit == 0);\n'
                        witnesses = ''
                        if first_hart is None:
                            witnesses = '  reg rq_full_seen = 0;\n  always @(posedge clock) if (reset) rq_full_seen <= 0; else if (&rq_waiting) rq_full_seen <= 1;\n'
                            guidance += '    assume(!r_valid || rq_full_seen);\n'
                        for port in range(32):
                            prefix = f'ports_{port}_request'
                            if port % 2 or port // 2 not in harts:
                                guidance += f'    assume(!{prefix}_valid);\n'
                            else:
                                witnesses += f'  reg rq_cover_sent_{port} = 0;\n  always @(posedge clock) if (reset) rq_cover_sent_{port} <= 0; else if (rq_accept_{port}) rq_cover_sent_{port} <= 1;\n'
                                guidance += f'    assume({prefix}_valid == !rq_cover_sent_{port} && ports_{port}_response_ready);\n'
                                guidance += f'    assume(!{prefix}_bits_write && !{prefix}_bits_atomic && {prefix}_bits_fetch);\n'
                                guidance += f"    assume({prefix}_bits_address == 64'd{(int(region['base']) + 63) & ~63} && {prefix}_bits_tag == 0);\n"
                                if first_hart is None:
                                    guidance += f'    assume({prefix}_bits_size == 2 || {prefix}_bits_size == 6);\n'
                        text = text.replace('\nendmodule', '\n' + witnesses + guidance + '  end\nendmodule')
                if unit == 'ReadQueue' and filename == module + '.sv' and mode in ('mutation', 'mutation-capacity'):
                    base = next((int(r['base']) + 3) & ~3 for r in manifest['parameters']['memoryRegions'] if r['executable'] and r['readable'] and not r['device'] and
                                ((int(r['base']) + 3) & ~3) + 4 <= int(r['base']) + int(r['size']))
                    readers = read_slots if mode == 'mutation-capacity' else 1
                    guidance = f'  always @* begin\n    assume(ar_ready == {int(mode == "mutation")} && !r_valid);\n'
                    for port in range(2 * manifest['parameters']['hartCount']):
                        prefix = f'ports_{port}_request'
                        guidance += f'    assume({prefix}_valid == {int(port < readers)} && !ports_{port}_response_ready);\n'
                        guidance += f"    assume(!{prefix}_bits_write && !{prefix}_bits_atomic && {prefix}_bits_fetch == {int(port % 2 == 0)} && {prefix}_bits_size == 2 && {prefix}_bits_address == 64'd{base});\n"
                    text = text.replace('\nendmodule', '\n' + guidance + '  end\nendmodule')
                if unit == 'ReadQueue' and filename == module + '.sv' and (mode.startswith('mutation-line-') or mode in ('mutation-sticky-fault', 'mutation-fault-release')):
                    line = mode.startswith('mutation-line-')
                    fetch = line and bool(manifest['parameters'].get('enableBurstRefill'))
                    region = next(r for r in manifest['parameters']['memoryRegions'] if not r['device'] and
                                  (r['executable'] if fetch else r['readable'] and (not line or r.get('dataCacheable'))) and int(r['size']) >= 128)
                    base = (int(region['base']) + 63) & ~63
                    size, identity = (6 if line else 2), ('(rq_poison ? 0 : 1)' if mode == 'mutation-fault-release' else '0')
                    last = f'(rq_beats[0] == {512 // manifest["parameters"]["axiDataBits"] - 1})' if line else 'rq_fault[0]' if mode == 'mutation-sticky-fault' else '1'
                    words = sum((part + 1) << (64 * part) for part in range(manifest['parameters']['axiDataBits'] // 64))
                    guidance = f'''  always @* begin
    assume(ports_0_request_valid && ports_0_response_ready && ar_ready);
    assume(!ports_0_request_bits_write && !ports_0_request_bits_atomic && ports_0_request_bits_fetch == {int(fetch)});
    assume(ports_0_request_bits_size == {size} && ports_0_request_bits_address == 64'h{base:x});
    assume(r_valid == (rq_waiting[0] && rq_count[0] == 0));
    assume(r_bits_id == {identity} && r_bits_last == {last} && r_bits_resp == 0);
    assume(r_bits_data == {manifest['parameters']['axiDataBits']}'h{words:x});
'''
                    for port in range(1, 2 * manifest['parameters']['hartCount']):
                        guidance += f'    assume(!ports_{port}_request_valid);\n'
                    text = text.replace('\nendmodule', '\n' + guidance + '  end\nendmodule')
                if unit == 'ReadQueue' and filename == module + '.sv' and mode in ('mutation-route', 'mutation-data', 'mutation-tag', 'mutation-id'):
                    region = next((r for r in manifest['parameters']['memoryRegions'] if r['readable'] and r['executable'] and not r['device'] and int(r['size']) >= 8 and int(r['base']) % 4 == 0), None)
                    if region is not None:
                        peer = min(2, 2 * manifest['parameters']['hartCount'] - 1)
                        constraints = [f'assume(r_valid == ($countones(rq_waiting) == {min(2, read_slots)}) && r_bits_id == 0 && r_bits_resp == 0 && r_bits_last);',
                                       f'assume(ar_ready && ports_0_response_ready && ports_{peer}_response_ready && rq_bit == 0);',
                                       f"assume(r_bits_data == {manifest['parameters']['axiDataBits']}'h{(1 << manifest['parameters']['axiDataBits']) - 1:x});"]
                        for port in range(2 * manifest['parameters']['hartCount']):
                            if port in (0, peer):
                                constraints.append(f'assume(ports_{port}_request_valid && ports_{port}_request_bits_tag == {37+port});')
                                constraints.append(f"assume(!ports_{port}_request_bits_write && !ports_{port}_request_bits_atomic && ports_{port}_request_bits_fetch == {int(port % 2 == 0)} && ports_{port}_request_bits_size == 2 && ports_{port}_request_bits_address == {manifest['parameters']['physicalAddressBits']}'d{int(region['base']) + 4});")
                            else:
                                constraints.append(f'assume(!ports_{port}_request_valid);')
                        guidance = '  always @* begin\n    ' + '\n    '.join(constraints) + '\n  end\n'
                        guidance += ('  always @(posedge clock) if (!reset && r_valid && r_ready)\n'
                                     f'    assert(rq_owned[0] && rq_sent[0]{" && rq_owned[1] && rq_sent[1] && owner != owner_0" if read_slots > 1 else ""});\n')
                        text = text.replace('\nendmodule', '\n' + guidance + 'endmodule')
                if unit == 'Backend' and proving and filename == 'DitDahA1Gpr.sv':
                    text = license + header(text)
                    for lane in range(manifest['parameters']['issueWidth']):
                        for operand in (1, 2):
                            text += f'\n(* anyseq *) reg [63:0] arbitrary_{operand}_{lane};\nassign rdata{operand}_{lane} = raddr{operand}_{lane} == 0 ? 0 : arbitrary_{operand}_{lane};\n'
                    text += '\nendmodule\n'
                if mode.startswith('prove-bits-') and filename == module + '.sv':
                    declaration = '(* anyconst *) reg [6:0] pipeline_bit;'
                    assert text.count(declaration) == 1
                    bit = int(mode.rsplit('-', 1)[1])
                    selector = "wire [6:0] pipeline_bit = 7'd96;" if bit == 96 else (
                        f"(* anyconst *) reg [{1 if manifest['parameters']['issueWidth'] == 3 else 2}:0] pipeline_offset; wire [6:0] pipeline_bit = pipeline_offset + 7'd{bit};")
                    text = text.replace(declaration, selector)
                if name == 'WfiFrontend' and mutating and filename == module + '.sv' and manifest['parameters'].get('enableBranchPrediction'):
                    first = "32'h0080006f" if mode.startswith('mutation-prediction') else "32'h13"
                    words = (1 << (manifest['parameters']['issueWidth'] - 1).bit_length()) if manifest['parameters'].get('iCacheBytes') else 1
                    guidance = f"  always @* assume(_fetch_output_bits_instruction == {first});\n"
                    for lane in range(1, words):
                        guidance += f"  always @* assume(_fetch_output_bits_following_{lane-1} == 32'h13);\n"
                    text = text.replace('endmodule', guidance + 'endmodule', 1)
                if name == 'PipelineBackend' and mutating and filename == module + '.sv':
                    bit = 40 if mode in ('mutation', 'mutation-dual-owner') else 96 if mode == 'mutation-recovery-metadata' else 0
                    text = text.replace('(* anyconst *) reg [6:0] pipeline_bit;', f"wire [6:0] pipeline_bit = 7'd{bit};")
                if name == 'PipelineBackend' and mode.startswith('cover') and filename == module + '.sv':
                    def cover_mode(expression):
                        return 'cover-dual' if expression.startswith('extraCount') else 'cover-drain' if expression.startswith('memoryFault') else 'cover-recovery' if expression.startswith(('earlyRedirect', 'commitResolved')) else 'cover-memory' if expression.startswith('memoryPending') else 'cover-dependency' if 'decodedCount ==' in expression else 'cover'
                    text = re.sub(r'^\s*cover\((.*?)\);\n', lambda match: match[0] if cover_mode(match[1]) == mode else '', text, flags=re.M)
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
    assume(memory_request_valid && memory_request_bits_fetch == {int(bool(manifest['parameters'].get('enableBurstRefill')))} && !memory_request_bits_write && !memory_request_bits_atomic && memory_request_bits_size == 6 && memory_request_bits_address == 0);
    assume(memory_response_ready && axi_ar_ready && !axi_b_valid);
    assume(axi_r_valid == (line_owned && line_address_sent && !line_last_seen && !line_buffered));
    assume(axi_r_bits_last == (line_beat == {512 // width - 1}) && axi_r_bits_id == line_id && axi_r_bits_resp == 0);
    assume(axi_r_bits_data == {width}'h{words:x});
  end
'''
                    text = text.replace('endmodule', guidance + '\nendmodule', 1)
                if unit == 'Lsu' and name != 'LsuReads' and mutating and filename == module + '.sv':
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
                    if manifest['parameters'].get('virtualAddressBits') == 39:
                        guidance += "  always @* begin assume(translation_request_ready && translation_response_valid == (word_translation_sent && !word_translated)); assume(!translation_response_bits_fault && translation_response_bits_address == word_address + 64'h1000); end\n"
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
                if name == 'DataCacheWriteback' and not proving and filename == module + '.sv':
                    base = min(int(r['base']) for r in manifest['parameters']['memoryRegions'] if r.get('dataCacheable') and r['writable'])
                    base = (base + 63) & ~63
                    guidance = f'''
  reg [2:0] wb_witness_completed = 0;
  reg wb_witness_probe = 0, wb_witness_waited = 0;
  (* anyconst *) reg wb_witness_error;
  always @(posedge clock) if (!reset) begin
    if (upstream_response_valid && upstream_response_ready && wb_witness_completed != 7)
      wb_witness_completed <= wb_witness_completed + 1;
    if (wb_probe_accept) wb_witness_probe <= 1;
    if (probe_response_valid) wb_witness_waited <= 1;
  end
  always @* begin
    assume(upstream_request_valid == (state == 0 && wb_witness_completed < 3));
    assume(upstream_response_ready && downstream_request_ready);
    assume(upstream_request_bits_address == (wb_witness_completed == 2 ? 64'h{base+8192:x} : 64'h{base:x}));
    assume(upstream_request_bits_size == 3 && upstream_request_bits_tag == 0);
    assume(upstream_request_bits_write == (wb_witness_completed == 1));
    assume(!upstream_request_bits_fetch && !upstream_request_bits_atomic && upstream_request_bits_privileged);
    assume(upstream_request_bits_refillSize == 0 && upstream_request_bits_mask == 1 && upstream_request_bits_data == 91);
    assume(downstream_response_valid == (wb_bus && !wb_probe_owned &&
      (wb_operation != 2 || !dirtyLines[{(base // 64) % (manifest['parameters']['dCacheBytes'] // 64)}])));
    assume(downstream_response_bits_fault == (wb_witness_error && wb_operation == 1));
    assume(downstream_response_bits_last && downstream_response_bits_tag == 0 && downstream_response_bits_data == 0);
    assume(probe_request_valid == (wb_bus && wb_operation == 2 && !wb_witness_probe));
    assume(probe_request_bits_address == 64'h{base:x} && probe_request_bits_invalidate);
    assume(probe_response_ready == wb_witness_waited);
    assume(_dataTags_ext_R0_data == {base >> ((manifest['parameters']['dCacheBytes'] - 1).bit_length())});
  end
'''
                    text = text.replace('endmodule', guidance + '\nendmodule', 1)
                    if 'storage' in mode:
                        sector = (manifest['parameters']['dCacheBytes'] // 8 - 1).bit_length()
                        watched = (base >> 3) % (1 << sector)
                        text = text.replace('endmodule', f'  always @* assume(auth_watched == {watched});\nendmodule', 1)
                        if mode == 'cover-storage' and manifest['parameters'].get('dCacheRefillBytes', 8) == 64:
                            text = text.replace('upstream_request_bits_refillSize == 0', 'upstream_request_bits_refillSize == 6')
                            text = text.replace('assume(downstream_response_bits_last && downstream_response_bits_tag', 'assume(downstream_response_bits_last == (wb_size != 6 || beat == 7) && downstream_response_bits_tag')
                if name == 'DataCache' and mode == 'mutation' and filename == module + '.sv':
                    text = text.replace('endmodule', '  always @* assume(probe_request_valid && probe_request_bits_invalidate);\nendmodule', 1)
                if name == 'DataCache' and mode.startswith('mutation-store-') and filename == module + '.sv':
                    base = min(int(r['base']) for r in manifest['parameters']['memoryRegions'] if r.get('dataCacheable') and r['writable'])
                    base = (base + 63) & ~63
                    tag_shift = (manifest['parameters']['dCacheBytes'] // 64 - 1).bit_length() + 6
                    guidance = f'''
  reg cache_witness_store = 0;
  always @(posedge clock) if (reset) cache_witness_store <= 0;
  else if (upstream_response_valid && upstream_response_ready) cache_witness_store <= 1;
  always @* begin
    assume(upstream_request_valid && upstream_response_ready && downstream_request_ready);
    assume(upstream_request_bits_address == (cache_witness_store ? 64'h{base+3:x} : 64'h{base:x}));
    assume(upstream_request_bits_size == (cache_witness_store ? 0 : 3) && upstream_request_bits_tag == 0);
    assume(upstream_request_bits_write == cache_witness_store && !upstream_request_bits_fetch && !upstream_request_bits_atomic);
    assume(upstream_request_bits_refillSize == 0 && upstream_request_bits_mask == 1 && upstream_request_bits_data == 91);
    assume(downstream_response_valid == (cache_bus && (!cache_witness_store || {int(mode != 'mutation-store-invalidate')} || cache_killed)));
    assume(downstream_response_bits_fault == (cache_witness_store && {int(mode == 'mutation-store-error')}) && downstream_response_bits_tag == 0);
    assume(downstream_response_bits_last && downstream_response_bits_data == 0);
    assume(invalidate_valid == ({int(mode == 'mutation-store-invalidate')} && cache_witness_store && cache_bus && !cache_killed));
    assume(invalidate_bits == 64'h{base:x} && _dataTags_ext_R0_data == {base >> tag_shift});
    assume(cache_watched == {(base >> 3) % (manifest['parameters']['dCacheBytes'] // 8)});
  end
'''
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
    assume(upstream_request_bits_refillSize == 0);
    assume(!upstream_request_bits_write && !upstream_request_bits_fetch && !upstream_request_bits_atomic);
    assume(downstream_response_valid == cache_bus && !downstream_response_bits_fault && downstream_response_bits_tag == 0);
    assume(_dataTags_ext_R0_data == (state == 1 ? {base >> tag_shift} : {(base >> tag_shift) ^ 1}));
    assume(cache_watched == {(base >> 3) % (manifest['parameters']['dCacheBytes'] // 8)});
  end
'''
                    text = text.replace('endmodule', guidance + '\nendmodule', 1)
                if unit == 'DataCache' and manifest['parameters'].get('dCacheRefillBytes', 8) == 64 and mode.startswith('cover') and filename == module + '.sv':
                    def line_cover(match):
                        selected = match[1].startswith(('cache_publish', 'cache_reply && cache_line', 'state == 5'))
                        return match[0] if selected == (mode == 'cover-line') else ''
                    text = re.sub(r'^\s*cover\((.*?)\);\n', line_cover, text, flags=re.M)
                    if mode == 'cover-line':
                        base = min(int(r['base']) for r in manifest['parameters']['memoryRegions'] if r.get('dataCacheable') and r['readable'] and not r['device'] and int(r['size']) >= 64)
                        base = (base + 63) & ~63
                        guidance = f'''
  (* anyconst *) reg [1:0] cache_scenario;
  always @* begin
    assume(upstream_request_valid && upstream_response_ready && downstream_request_ready);
    assume(upstream_request_bits_address == (cache_scenario == 0 ? 64'h{base+56:x} : 64'h{base:x}));
    assume(upstream_request_bits_size == 3 && upstream_request_bits_refillSize == 6 && upstream_request_bits_tag == 0);
    assume(!upstream_request_bits_write && !upstream_request_bits_fetch && !upstream_request_bits_atomic);
    assume(downstream_response_valid == cache_bus && !downstream_response_bits_fault && downstream_response_bits_tag == 0 && downstream_response_bits_data == 0);
    assume(downstream_response_bits_last == (cache_scenario == 3 ? cache_beats == 8 : cache_beats == 7));
    assume(invalidate_valid == (cache_scenario == 2 && cache_bus && cache_beats == 7) && invalidate_bits == 64'h{base:x});
  end
'''
                        text = text.replace('endmodule', guidance + '\nendmodule', 1)
                if unit == 'Coherence' and mode == 'mutation-acknowledgement' and filename == module + '.sv':
                    text = text.replace('endmodule', "  always @* assume(probe_0_response_bits_mask != 0);\nendmodule", 1)
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
                if unit == 'DataCache' and filename == module + '.sv':
                    for memory, instance, prefix in cache_memories:
                        for pin, expression in instance_ports(text, memory, instance)[0][1].items():
                            text = text.replace(f'FORMAL_{prefix}_{pin}', '(' + expression + ')')
                    assert 'FORMAL_DATA_' not in text and 'FORMAL_TAG_' not in text
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
            task = 'bmc' if mutating else 'prove' if proving else 'cover' if mode.startswith('cover') else mode
            if mode == 'mutation' and name == 'Fetch':
                task = 'prove'
            engine = 'abc pdr' if task == 'prove' and unit not in ('Gpr', 'Multiply', 'Pmp', 'PmpDecode', 'PmpInterval', 'PmpSubset', 'Csr', 'Memory', 'Axi', 'InstructionCache', 'DataCache', 'Coherence', 'Decode', 'Execute', 'LocalInterrupts', 'Translation') and name not in ('SynchronizationBackend', 'WfiBackend') else 'smtbmc z3'
            if unit == 'ReadQueue':
                engine = 'smtbmc z3'
                if (mode == 'prove-control' or mode.startswith('prove-response-') or read_bit_step == 4 and mode.startswith('prove-storage-')) and manifest['parameters']['hartCount'] > 2:
                    engine = 'smtbmc --syn --unroll z3'
            if unit == 'MemoryFabric' and (mode == 'prove-control' or mode.startswith(('prove-ports-', 'prove-tags', 'prove-stability-'))):
                engine = 'smtbmc z3'
            if unit == 'MemoryFabric' and (mode == 'prove-control' or mode.startswith(('prove-ports-', 'prove-tags'))) and manifest['parameters']['hartCount'] > 2:
                engine = 'smtbmc --syn --unroll z3'
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
            if unit == 'Backend' and task == 'prove' and (manifest['parameters']['issueWidth'] > 1 or manifest['parameters'].get('loadQueueEntries', 1) == 2):
                timeout = 180
            if name == 'WideFetch' and task == 'cover' and manifest['parameters'].get('virtualAddressBits') == 39:
                timeout = 180
            if name == 'DataCacheWriteback' and task == 'cover':
                timeout = 180 if mode == 'cover-storage' and manifest['parameters'].get('dCacheRefillBytes', 8) == 64 else 90
            if unit == 'DataCache' and task == 'prove':
                timeout = 180
            if unit == 'ReadQueue' and mode.startswith(('prove-storage-bits-', 'prove-payload-bits-')):
                timeout = 180
            if unit == 'ReadQueue' and mode == 'cover-global' and read_slots > 2:
                timeout = 120
            if unit == 'ReadQueue' and mode == 'prove-control' and read_slots > 2 and manifest['parameters']['hartCount'] == 16:
                timeout = 300
            if unit == 'Axi' and task == 'prove' and manifest['parameters']['axiDataBits'] == 512:
                timeout = 120
            if unit == 'MemoryFabric' and (mode == 'prove-control' or mode.startswith(('prove-ports-', 'prove-tags'))) and manifest['parameters']['hartCount'] > 2:
                timeout = 300 if port_modes else 120
            if unit == 'MemoryFabric' and mode.startswith('prove-stability-') and port_modes:
                timeout = 120
            witness_option = 'aigsmt z3\n' if engine == 'abc pdr' else ''
            preparation = (f'hierarchy -check -top {top}\nproc\nflatten\nopt_expr -keepdc\nopt_clean\nwreduce\nopt_clean\ncheck'
                           if name.startswith('Pmp') else f'prep -top {top} -flatten')
            depth = 6 * manifest['parameters']['hartCount'] + 8 if unit == 'MemoryArbiter' else 72 if task == 'cover' or (unit == 'InstructionCache' and mode in ('mutation', 'mutation-invalidate', 'mutation-count')) else 1 if name.startswith('Pmp') or unit in ('Decode', 'Execute') else (3 if task == 'prove' else 8) if unit == 'Csr' else 6 if unit in ('DataCache', 'Coherence') and task == 'prove' else 4 if name in ('Gpr', 'Multiply', 'Memory', 'Axi', 'SynchronizationBackend', 'WfiBackend', 'InstructionCache', 'LocalInterrupts') and task == 'prove' else 24
            if mode == 'mutation-buffer-stage' and manifest['parameters'].get('enableBurstRefill'):
                depth = 40
            if unit == 'ReadQueue' and task == 'prove':
                depth = 1 if mode in ('prove-permission', 'prove-read-data') else 4
            if unit == 'MemoryFabric' and (mode == 'prove-control' or mode.startswith(('prove-ports-', 'prove-tags', 'prove-stability-'))):
                depth = 4
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
read -formal -sv {'-noautowire ' if name == 'PipelineBackend' else ''}{' '.join(files)}
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
            counted = (work / (module + '.sv')).read_text() if unit in ('ReadQueue', 'Axi', 'DataCache', 'MemoryFabric') or name == 'PipelineBackend' else body
            reports.append(dict(module=module, propertyGroup=name, mode=mode, status=status, engine=engine,
                                assertions=len(re.findall(r'assert\((?!1\);)', counted)), covers=counted.count('cover(')))
            print(f'  {module} [{name}] {mode}: {status}', flush=True)
    assert all((rtl / p).read_text() == text for p, text in (sources | observation_sources).items()), 'RTL changed during proofs'
    assert checker_hash == hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'Checker changed during proofs'
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in manifest['sourceHashes'].items())
    proved = {report['propertyGroup'] for report in reports if report['mode'].startswith('prove') and report['status'] == 'PASS'}
    if mutations is not None:
        assert set(mutations) == {report['mode'] for report in reports}, 'Incomplete negative-control selection'
    if 'DataCacheWriteback' in proved:
        assert {'prove', 'cover', 'mutation', 'mutation-store-missing', 'prove-storage-shape', 'prove-storage-bytes', 'prove-storage', 'cover-storage', 'mutation-storage-mask', 'mutation-storage-word'} <= {r['mode'] for r in reports if r['propertyGroup'] == 'DataCacheWriteback'}, 'Incomplete writeback authorization proof'
    if 'PipelineBackend' in proved:
        covers = {'cover', 'cover-memory', 'cover-recovery'} | ({'cover-dependency'} if manifest['parameters']['issueWidth'] > 1 else set())
        if manifest['parameters'].get('loadQueueEntries', 1) == 2:
            covers |= {'prove-control', 'cover-dual', 'cover-drain', 'mutation-dual-owner', 'mutation-dual-drain'}
            if manifest['parameters']['issueWidth'] == 1:
                covers |= {'prove-identity'}
        assert covers <= {report['mode'] for report in reports if report['propertyGroup'] == 'PipelineBackend'}, 'Incomplete pipeline covers'
    if 'PipelineBackend' in proved and manifest['parameters']['issueWidth'] > 1:
        assert {f'prove-bits-{bit}' for bit in range(0, 97 if manifest['parameters'].get('enableBranchPrediction') else 96, 4 if manifest['parameters']['issueWidth'] == 3 else 8)} <= {report['mode'] for report in reports}, 'Incomplete identity proof'
    if 'ReadQueue' in proved:
        payload_modes = {f'prove-payload-bits-{bit}' for bit in range(0, 64, read_bit_step)} if manifest['parameters']['hartCount'] > 2 or manifest['parameters']['axiDataBits'] > 64 else {'prove-payload'}
        expected = {'prove-permission', 'prove-permission-hold', 'prove-read-data', 'prove-control'} | {mode.replace('payload', 'storage') for mode in payload_modes}
        expected |= {f'{mode}-ports-{port}' for mode in payload_modes for port in range(0, 32, 8)} if read_bit_step == 4 else payload_modes
        cover_modes = {'cover-global'} | {f'cover-harts-{hart}' for hart in range(0, manifest['parameters']['hartCount'], 4)} if manifest['parameters']['hartCount'] > 2 else {'cover'}
        expected |= cover_modes | {'mutation', 'mutation-lane', 'mutation-permission', 'mutation-route', 'mutation-tag', 'mutation-data', 'mutation-id', 'mutation-fault-release', 'mutation-sticky-fault'}
        line = manifest['parameters'].get('enableBurstRefill') or manifest['parameters'].get('dCacheRefillBytes') == 64
        if line:
            expected.add('mutation-line-last')
            if manifest['parameters']['axiDataBits'] < 512:
                expected.add('mutation-line-count')
            if manifest['parameters']['axiDataBits'] > 64:
                expected.add('mutation-line-order')
        if read_slots > 1:
            expected |= {'prove-schedule', 'cover-schedule', 'mutation-schedule'}
        if read_slots > 2:
            expected.add('mutation-capacity')
            if manifest['parameters']['hartCount'] == 16:
                expected |= {f'prove-response-{port}' for port in range(0, 32, 8)}
        assert sum(r['covers'] for r in reports if r['propertyGroup'] == 'ReadQueue' and r['mode'] in cover_modes) == 4 * manifest['parameters']['hartCount'] + (4 if line else 3) + (2 if line else 1) * (read_slots > 1) + int(manifest['parameters'].get('loadQueueEntries', 1) == 2 and read_slots > 1), 'Incomplete read queue covers'
        assert expected <= {r['mode'] for r in reports if r['propertyGroup'] == 'ReadQueue'}, 'Incomplete read queue proof'
    if 'Pmp' in proved:
        assert {'PmpInterval', 'PmpDecode'} <= proved, 'Missing PMP composition prerequisites'
        if manifest['parameters'].get('dCacheRefillBytes', 8) == 64:
            assert 'PmpSubset' in proved, 'Missing PMP containment proof'
    if any(r['propertyGroup'] == 'MemoryFabric' and r['mode'] == 'prove-control' for r in reports):
        tag_modes = {f'prove-tags-{bit}' for bit in range(8)} if read_slots > 2 else {'prove-tags'}
        port_modes = {f'prove-ports-{port}' for port in range(0, 32, 8)} if read_slots > 2 and manifest['parameters']['hartCount'] == 16 else set()
        assert {'prove-control', *port_modes, *tag_modes, 'cover', 'mutation-data', *(f'prove-stability-{i}' for i in range(2 * manifest['parameters']['hartCount']))} <= {r['mode'] for r in reports if r['propertyGroup'] == 'MemoryFabric'}, 'Incomplete fabric proof'
    if 'Axi' in proved and manifest['parameters']['axiDataBits'] == 512:
        assert {'prove-control', 'prove-payload', 'cover'} <= {r['mode'] for r in reports if r['propertyGroup'] == 'Axi'}, 'Incomplete AXI proof'
    summary.write_text(json.dumps(dict(
        scope='selected negative controls only' if mutations is not None else 'module-level safety, cover reachability and mutation detection',
        selectedMutations=mutations, propertyGroups=sorted(proved),
        assumptions='initial reset, then no reset except CSR proofs; Fetch responses require accepted requests and stable blocked payloads; enabled control proofs abstract combinational authorization',
        fabricProbeAssumptions='probe responses require accepted requests and stable held frames; concrete cache endpoint proofs discharge these contracts; controller/physical ownership overlap and retained maintenance tags are checked, including noncacheable-line-base internal releases' if any(r['propertyGroup'] == 'MemoryFabric' and r['mode'] == 'prove-control' for r in reports) and manifest['parameters'].get('dCacheBytes') else None,
        cacheRoutingMutation=dict(applicable=cache_routing_base is not None, lineBase=cache_routing_base,
            scope='internal release whose line base bypasses cacheable and device classification') if 'MemoryFabric' in proved and manifest['parameters'].get('dCacheWriteback') else None,
        fabricComposition='independent ownership ledger at configured capacity; control and exclusive-path/buffer invariants, then captured tags across the queue and exclusive path, then arbitrary-bit stalled data per port; each partition assumes only earlier proved assertions; input data and arbitration unrestricted' if any(r['propertyGroup'] == 'MemoryFabric' and r['mode'] == 'prove-control' for r in reports) else None,
        readQueueComposition='PMA expressions and busy-slot permission stability proved first; arbitrary permission outcomes retain the proved shape and hold conditions; independent ledger at configured capacity tracks accepted requests, RID, RDATA, beats and faults; control, stored values/address and port payload proofs consume only previously proved assertions; exhaustive data/address bit partitions for wide configurations; safety has no request-value restrictions' if 'ReadQueue' in proved else None,
        readQueueWitnessGuidance='For 16 harts and more than two slots, covers drive four selected harts once; global covers wait for all slots before R. Negative controls fix relevant traffic. These witness constraints are absent from safety proofs.' if 'ReadQueue' in proved else None,
        fabricWitnessGuidance='For 16 harts, covers select read pressure or one writer; negative controls direct exclusive reads, held replies, early drain, isolation and bypass faults. These witness constraints are absent from safety proofs.' if 'MemoryFabric' in proved else None,
        pmpComposition='Pmp uses independently proved PmpInterval identities and PmpDecode request spans; no table-value restrictions; data-line configurations also prove that one arbitrary priority-fold entry preserves whole-range permission implying contained-demand permission, assuming only the prior-fold implication whose initial M-mode defaults are equal' if 'Pmp' in proved else None,
        registerFile='arbitrary nonzero architectural register and immutable data bit, exact reset and ordered multiport writes, zero-register isolation and every asynchronous read port; unrestricted addresses, data and same-address writes' if 'Gpr' in proved else None,
        backendAbstraction='arbitrary multiply result and completion delay; safety overapproximates nonzero GPR reads, with actual GPR retained for covers/mutations; resource and register contracts are separately proved',
        resourceWitnessGuidance='cover/mutations only: faulting SD or configured PMP update followed by MUL and NOP, arbitrary response delay and quiescent interrupts' if 'Backend' in proved else None,
        pipelineMutationGuidance='mutations only: legal ADDI forwarding/dependency groups, SD/ALU/JAL or leading-JAL recovery sequences, faulted grouped LD and ALUs, or two loads with reverse returns or an older fault; observed PC/prediction bit selected for identity corruption; actual arithmetic and register storage' if 'PipelineBackend' in proved else None,
        pipelineCoverGuidance='cover only: independent ADDI groups, a leading SD with arbitrary response delay, lane-0-to-lane-1 RAW, recovery, or two loads with reverse returns or an older fault; translated witnesses use retained identity replies' if 'PipelineBackend' in proved else None,
        pipelineComposition='dual-context control, ownership, metadata and architectural write/forwarding contracts proved first; accepted PC/encoding FIFO then consumes only those proved assertions; faulting head discards the younger memory group after draining' if 'PipelineBackend' in proved and manifest['parameters'].get('loadQueueEntries', 1) == 2 else None,
        pipeline='independent FIFO of accepted PC/encoding/prediction bits checks every valid stage lane; multi-issue partitions all identity bits into four- or eight-bit proof domains; prediction provenance covers every pre-issue lane and each later head, whose control operations execute alone; greedy oldest prefix, youngest older writer, scalar effect ownership and every GPR write port; generated observation registers inlined; safety overapproximates nonzero GPR reads, with actual GPR retained for covers/mutations and separately proved' if 'PipelineBackend' in proved else None,
        synchronization='raw barrier encodings, independent accepted-data ownership until retirement, sequential instruction synchronization redirect and younger flush; no data response timing assumptions' if 'SynchronizationBackend' in proved else None,
        synchronizationWitnessGuidance='cover/mutations only: port-driven zero-address SD, FENCE/FENCE.I, one request and response stall, faulted FENCE.I and quiescent interrupts; unrestricted safety proof' if 'SynchronizationBackend' in proved else None,
        instructionCache='control proof at configured geometry; arbitrary native SRAM read outputs; independent ownership, authorization, response fault/tag/last history, native write data, complete publication, invalidation and precise fallback; functional array contents require separate simulation' if 'InstructionCache' in proved else None,
        writebackCache='control safety with arbitrary data, tag and dirty-metadata SRAM outputs; captured request/probe ownership, stable native samples, terminal-only dirty release, required successful-acquire byte merge and dirty-mask union; upstream scalar size<=3 and internal operation zero, replies require owned requests, scalar/acquire replies terminate and held replies/probes persist; no full-cache contents, global coherence, privilege or progress theorem' if 'DataCacheWriteback' in proved else None,
        writebackCacheWitnessGuidance='cover/mutations only: legal refill, store grant or fault, dirty-victim replacement and held probe frames; safety has no witness restrictions' if 'DataCacheWriteback' in proved else None,
        writebackStorage='storage safety consumes the earlier unrestricted control assertions, then proves request/tag shape, stored-byte provenance and frame output in dependency order; arbitrary watched native dirty-metadata word and its line tag preserve emitted registered-address/current-array-value timing; independent accepted store shape/PMA and byte authorization history prove dirty masks and emitted physical-word identity; other rows and data SRAM remain arbitrary; upstream PMP authorization is a producer composition prerequisite, not proved at this cache boundary; storage mutations disable earlier control assertions only to target the authorization properties' if 'DataCacheWriteback' in proved else None,
        dataCache='control safety with arbitrary native SRAM reads; independently captured requests, physical ownership, valid-sector/tag-qualified sampling, fault/tag attribution, index invalidation, byte-masked write-through hit updates and failed-write eviction; line mode adds saturating segment history, terminal-only ownership release and one exact fallback; functional SRAM contents require separate simulation' if 'DataCache' in proved else None,
        dataRefillProtection='largest PMA-qualified read range first, recorded grant and effective privilege, at most two narrower queries, original VA faults and no extra successful-line query; arbitrary PMP outcomes compose with concrete PMP span/priority and containment proofs' if 'Lsu' in proved and manifest['parameters'].get('dCacheRefillBytes', 8) == 64 else None,
        dataCacheWitnessGuidance='store mutations use a permitted refill followed by a byte store with success, invalidation or error; tag-lifetime mutation uses two sectors and unrelated later SRAM output; line covers use first/last-sector demands, immediate service, terminal invalidation or overlong response; safety unrestricted' if 'DataCache' in proved else None,
        coherence='independent accepted-request, probe-issued/completed and physical ownership ledgers; masked dirty-frame writes retain ownership across backpressure, errors and malformed nonterminal responses; only successful terminal completion releases a frame; ownership grants retain original tags; internal requests require cacheable PMA access; endpoint handshake/hold assumptions with arbitrary payloads, delays and errors; no full-cache, reservation, DMA or progress claim' if 'Coherence' in proved else None,
        coherenceWitnessGuidance='acknowledgement mutation only fixes a nonzero dirty mask on probe port zero; unrestricted safety and cover retain arbitrary masks' if 'Coherence' in proved else None,
        cacheWitnessGuidance='cover/mutations only: zero-address demand, successful service, canceled stalls, last-beat/post-fill invalidation, permission denial and demand/speculative fault scenarios; unrestricted safety proof' if 'InstructionCache' in proved else None,
        arbitration='one retained request and owner, hart identity from independent accepted requester/2 through response; at most 2N-1 other completions while continuously requesting; no bound on external service delay' if 'MemoryArbiter' in proved else None,
        interruptProgress='with eligibility held, successful matching data response reaches interrupt entry or priority synchronous trap within three cycles; memory service itself is external' if any(r['propertyGroup'] == 'InterruptBackend' for r in reports) else None,
        witnessGuidance='InterruptBackend cover/mutations drive ADDI and mie/mstatus at clocks 0/8/16, then SD, AMOADD.D, MUL, SD-to-MUL, SD-to-FENCE.I or FENCE.I; fixed PC/tag, successful data service, request stall and read-only ownership events select interrupt timing; unrestricted safety proof' if 'InterruptBackend' in proved else None,
        arbiterWitnessGuidance='cover/mutations hold all requesters valid with zero payloads, one request stall and one response stall then immediate service; unrestricted proof' if 'MemoryArbiter' in proved else None,
        readStreaming='one accepted line and external AR; independent beat/chunk counters, buffered data ordering, response-last ownership, stalled payloads and malformed-last drain; endpoint R data, ID, status, last and delays unrestricted' if 'Axi' in proved and (manifest['parameters'].get('enableBurstRefill') or manifest['parameters'].get('dCacheRefillBytes', 8) == 64) else None,
        cachedFetch='actual cache upstream scalar connections retain request/response ownership; external scalar responses terminate, line responses may fault or end early/late; cancel and invalidate are independent' if 'Fetch' in proved and manifest['parameters'].get('iCacheBytes') else None,
        wideFetch='actual cache connections, captured privilege and permission, full-block and scalar fallback shapes, bounded suffix count, short-return barrier, stable payload and cancellation drain; arbitrary native SRAM read outputs; translation replies require accepted requests and successful replies preserve the page offset' if 'WideFetch' in proved else None,
        frontendQueue='actual queue RTL with abstract single-owner fetch contract; arbitrary stalls, payloads, cancellation and 1-to-demand-suffix returns; independent credit history and complete reference FIFO over an arbitrary immutable packet bit proves conservation of every field through compaction, stable groups and oldest restart; concrete fetch and translation proofs are composition prerequisites' if 'WfiFrontend' in proved else None,
        wideFetchWitnessGuidance='cover only: full-count return uses aligned repeated demand, granted permission, successful immediate service, zero data and matching tag-array reads; other covers retain arbitrary requests and responses with zero native instruction reads; safety and mutations unrestricted' if 'WideFetch' in proved else None,
        atomicTransport='independent request and AXI channel ownership and retained hart identity; LR read-only, one-shot SC status/no-bus failure, ADD/OR/SWAP exclusive retry and error isolation; no external-memory atomicity or eventual-success theorem' if 'Axi' in proved else None,
        axiAssumptions='initial reset only; R requires accepted AR, B requires accepted AW and W; blocked response payloads persist; all request metadata, hart/response IDs, data, responses, last and delays unrestricted' if 'Axi' in proved else None,
        axiComposition='512-bit configurations prove all control first; payload consumes exactly those proved assertions without restricting data, addresses, operations or response timing' if 'Axi' in proved and manifest['parameters']['axiDataBits'] == 512 else None,
        axiMutationGuidance='mutations only: aligned D ADD/OR/SWAP/LR/SC at address8, operand1, values7 then11 after retry, immediate service, per-fault codes, SC eligibility and valid hart1 with changing live sideband for retained-ID check; prove and cover unrestricted' if 'Axi' in proved else None,
        wordMemory='independent decode and execution metadata, accepted LSU ownership, size/mask, alignment, authorization, narrow extension and response fault attribution; metadata inputs unrestricted, functional completion checked for byte/halfword/word/doubleword sizes' if 'Lsu' in proved else None,
        dualReadOwnership='Bare aligned ordinary doubleword reads without PMP; independent two-context acceptance and completion ledger, arbitrary stalls/data/errors/tags/cancellation, all payload bits, in-order completion and held-request retention; no device, translation or progress claim' if 'LsuReads' in proved else None,
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
    parser.add_argument('--mutations', nargs='+')
    parser.add_argument('--modules', nargs='+', choices=('Fetch', 'WideFetch', 'Gpr', 'Multiply', 'Backend', 'PipelineBackend', 'Pmp', 'PmpDecode', 'PmpInterval', 'PmpSubset', 'Csr', 'UserCsr', 'UserExecute', 'SupervisorCsr', 'SupervisorExecute', 'SupervisorFetch', 'Lsu', 'LsuReads', 'InterruptCsr', 'InterruptBackend', 'SynchronizationBackend', 'InstructionCache', 'DataCache', 'DataCacheWriteback', 'Coherence', 'MemoryArbiter', 'ReadQueue', 'MemoryFabric', 'Memory', 'Axi', 'WordDecode', 'WordExecute', 'IntegerDecode', 'IntegerExecute', 'WfiBackend', 'WfiFrontend', 'LocalInterrupts', 'Translation'))
    args = parser.parse_args()
    verify(args.rtl, args.output, args.modules, args.mutations)
