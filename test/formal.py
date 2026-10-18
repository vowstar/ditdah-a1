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
        assume($stable({memory_response_bits_data, memory_response_bits_fault, memory_response_bits_tag}));
      end
      if (memory_request_valid && memory_request_ready) begin
        assert(!outstanding);
        outstanding <= 1;
      end
      if (memory_response_valid && memory_response_ready) begin
        assert(outstanding);
        outstanding <= 0;
        response_seen <= 1;
      end
      if (output_valid && output_ready) have_request <= 0;
      if (cancel) killed <= 1;
      if (request_valid && request_ready) begin
        assert(!have_request || killed);
        have_request <= 1;
        killed <= 0;
        response_seen <= 0;
        accepted_pc <= request_bits_pc;
        accepted_tag <= request_bits_tag;
      end
      assert(!memory_response_ready || outstanding);
      if (memory_request_valid) assert(!memory_request_bits_atomic);
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
          memory_request_bits_write, memory_request_bits_fetch, memory_request_bits_atomic}));
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


def protection_cases(parameters):
    width = parameters['physicalAddressBits'] - 2
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
    pmp = f'''
  wire [1039:0] decoded_low = {{{low_signals}}};
  wire [1039:0] decoded_high = {{{high_signals}}};
  reg expected, any_byte, every_byte, hit;
  reg [64:0] cursor;
  integer i, b;
  always @* begin
    expected = 1; hit = 0; cursor = 0; any_byte = 0; every_byte = 1;
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
      if (any_byte) expected = every_byte && (!state_config[i*8+7] ||
        (atomic ? state_config[i*8] && state_config[i*8+1] :
          fetch ? state_config[i*8+2] : write ? state_config[i*8+1] : state_config[i*8]));
    end
    assert(allowed == (expected && size <= 3 &&
      ({{1'b0, address}} + (65'd1 << size)) <= (65'd1 << {width + 2})));
    cover(allowed && fetch);
    cover(!allowed && write);
    cover(!allowed && size == 3 && !state_config[7]);
    cover(atomic && allowed);
    cover(atomic && !allowed && write);
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
    fetch = FETCH.replace('reg outstanding;', 'reg outstanding;\n  reg local_denied;')
    fetch = fetch.replace('killed', 'observed_killed')
    fetch = fetch.replace('outstanding <= 0;', 'outstanding <= 0;\n      local_denied <= 0;', 1)
    fetch = fetch.replace('accepted_pc <= request_bits_pc;', 'local_denied <= !_pmp_allowed;\n        accepted_pc <= request_bits_pc;')
    fetch = fetch.replace('response_seen || accepted_pc[1:0] != 0', 'response_seen || accepted_pc[1:0] != 0 || local_denied')
    fetch = fetch.replace('if (observed_killed || cancel)', 'if (have_request && local_denied) assert(!memory_request_valid);\n      cover(output_valid && local_denied && output_bits_fault);\n      if (observed_killed || cancel)')
    lsu = '''
  reg past_valid = 0, pending, denied, store, atomic;
  reg [63:0] address;
  always @(posedge clock) begin
    past_valid <= 1;
    if (!past_valid) assume(reset); else assume(!reset);
    if (reset) begin pending <= 0; denied <= 0; end
    else begin
      if (input_valid && input_ready) begin
        pending <= 1;
        denied <= !input_bits_instruction_fault && input_bits_address[2:0] == 0 && !_pmp_allowed;
        address <= input_bits_address; store <= input_bits_store;
        atomic <= input_bits_load && input_bits_store;
      end
      if (output_valid && output_ready) pending <= 0;
      if (pending && denied) begin
        assert(!memory_request_valid && output_valid && output_bits_instruction_fault);
        assert(output_bits_instruction_cause == (store ? 7 : 5) && output_bits_instruction_tval == address);
      end
      if (memory_request_valid) assert(memory_request_bits_atomic == atomic);
      if (past_valid && $past(!reset && memory_request_valid && !memory_request_ready)) begin
        assert(memory_request_valid);
        assert($stable({memory_request_bits_address, memory_request_bits_data, memory_request_bits_tag,
          memory_request_bits_mask, memory_request_bits_size, memory_request_bits_write,
          memory_request_bits_fetch, memory_request_bits_atomic}));
      end
      cover(pending && denied && !output_ready);
      cover(pending && denied && output_ready && store);
      cover(memory_request_valid && !memory_request_ready && !_pmp_allowed);
    end
  end
'''
    backend = BACKEND + '''
  wire permission_update = commit_output_valid_layerCapture && _commit_output_bits_csrWrite &&
    ((_commit_output_bits_csrAddress >= 12'h3a0 && _commit_output_bits_csrAddress <= 12'h3ae) ||
     (_commit_output_bits_csrAddress >= 12'h3b0 && _commit_output_bits_csrAddress <= 12'h3ef));
  always @(posedge clock) if (!reset) begin
    if (permission_update) assert(redirect_0 && !executed && !data_request_valid);
    if (past_valid && $past(!reset && permission_update))
      assert(!decodedValid && !issuedValid && !resultValid && !commitValid);
    cover(permission_update && issuedValid);
    cover(permission_update && decodedValid);
  end
'''
    return [('PmpInterval', interval, 'high > low', "1'b0"),
            ('PmpDecode', decode, "mask = _GEN_0 ^ _GEN_0 + 62'h1;", "mask = _GEN_0 ^ _GEN_0 + 62'h3;"),
            ('Pmp', pmp, 'assign allowed =', "assign allowed = 1'h1 |"),
            ('Csr', csr, '& ~(config_0[5])', "& 1'h1"),
            ('Fetch', fetch, '& ~killed & ~cancel', '& ~cancel'),
            ('Lsu', lsu, '~_pmp_allowed', "1'h0"),
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
    end
  end
'''
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
          data_request_bits_fetch, data_request_bits_atomic}}));
      end
      if (past_valid) begin
        if ($past(reset)) assert(resumePc == 64'h{int(parameters['resetVector']):x});
        else if ($past(takeInterrupt_layerCapture)) begin
          assert(resumePc == $past(csr_trapVector_layerCapture));
          assert(!decodedValid && !issuedValid && !resultValid && !commitValid);
        end else if ($past(commit_output_valid_layerCapture)) assert(resumePc == $past(commit_output_bits_nextPc_layerCapture));
        else assert($stable(resumePc));
      end
      cover(_csr_interruptPending && memoryPending && data_request_valid && !data_request_ready);
      cover(_csr_interruptPending && memoryPending && data_request_valid && data_request_bits_atomic);
      cover(_csr_interruptPending && irq_memory_commit && !memoryPending);
      cover(takeInterrupt_layerCapture && !decodedValid && !issuedValid && !resultValid && !commitValid);
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
          assert(resultValid && resultPacket_instruction_pc == sync_memory_pc && resultPacket_instruction_tag == sync_memory_tag);
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
      if (commitValid) assert(commitPacket_fenceI ==
        (sync_encoding(commitPacket_instruction_instruction) && commitPacket_instruction_instruction[12]));
      if (memoryPending) assert(!_lsu_output_bits_fenceI);
      if (sync_decoded) begin
        assert(decodedPacket_operation == (decodedPacket_instruction_instruction[12] ? 17 : 16));
        assert(decodedPacket_serializing && !decodedPacket_usesRs1 && !decodedPacket_usesRs2 && !decodedPacket_writesRd);
        if (issued) begin
          assert(!sync_memory_owned && !sync_bus_owned && !issuedValid && !resultValid && !commitValid);
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
      if (memoryPending) assert(!sync_encoding(_lsu_output_bits_instruction_instruction));
      if (sync_barrier_owned) begin
        assert(!sync_memory_owned && !sync_bus_owned && !data_request_valid && !lsu_input_valid);
        assert((issuedValid && sync_encoding(issuedPacket_decoded_instruction_instruction) && !issuedPacket_decoded_instruction_fault) ||
          (resultValid && sync_encoding(resultPacket_instruction_instruction) && !resultPacket_instruction_fault) ||
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
        assert(!decodedValid && !issuedValid && !resultValid && !commitValid);
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
    return ('SynchronizationBackend', body, '| _commit_output_bits_fenceI', "| 1'h0 & _commit_output_bits_fenceI")


def instruction_cache_case(parameters):
    index_bits = (parameters['iCacheBytes'] // 64 - 1).bit_length()
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
    assume(!invalidate || cancel);
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
      if (upstream_request_valid && upstream_request_ready) begin
        assert(!cache_owned && !cache_bus);
        cache_owned <= 1; cache_address <= upstream_request_bits_address; cache_tag <= upstream_request_bits_tag;
        cache_killed <= cancel || invalidate; cache_authorized <= 0;
        cache_filled <= 0; cache_sent <= 0; cache_fault <= 0;
      end
      if (cache_owned && (cancel || invalidate)) cache_killed <= 1;
      if (state == 2 && allowed && !cache_abort) begin
        cache_authorized <= 1; cache_permission <= checkAddress;
      end
      if (downstream_request_valid) begin
        assert(cache_owned && cache_authorized && !cache_bus);
        assert(downstream_request_bits_address == cache_permission && downstream_request_bits_tag == cache_tag);
        assert(downstream_request_bits_fetch && !downstream_request_bits_write && !downstream_request_bits_atomic);
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
        assert(cache_owned && !cache_bus && !downstream_request_valid);
        assert(upstream_response_bits_tag == cache_tag && upstream_response_bits_fault == cache_fault);
        if (upstream_response_ready) cache_owned <= 0;
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
            downstream_request_bits_write, downstream_request_bits_atomic}));
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


def synchronization_witness(parameters, mode):
    body = r'''
  (* anyconst *) reg [2:0] sync_scenario;
  reg [1:0] sync_packet = 0;
  reg sync_stalled = 0, sync_waited = 0;
  always @(posedge clock) if (!reset) begin
    if (instruction_valid && instruction_ready && sync_packet != 3) sync_packet <= sync_packet + 1;
    if (data_request_valid && !data_request_ready) sync_stalled <= 1;
    sync_waited <= sync_bus_owned;
  end
  always @* begin
    assume(sync_scenario < 4 && instruction_valid && instruction_bits_length == 4 && instruction_bits_tag == 0);
    assume(instruction_bits_pc == RESET_PC);
    assume(instruction_bits_fault == (sync_scenario == 2 && sync_packet == 0));
    assume(instruction_bits_instruction == (sync_packet == 0 ?
      (sync_scenario >= 2 ? 32'h0000100f : 32'h00003023) :
      sync_packet == 1 ? (sync_scenario == 0 ? 32'h0000000f : 32'h0000100f) : 32'h00003023));
    assume(data_request_ready == (sync_scenario != 0 || sync_stalled));
    assume(data_response_valid == (sync_bus_owned && (sync_scenario != 0 || sync_waited)));
    assume(data_response_bits_tag == 0 && !data_response_bits_fault && data_response_bits_data == 0);
  end
'''.replace('RESET_PC', f"64'h{int(parameters['resetVector']):x}")
    if parameters.get('enableInterrupts'):
        body += '''  always @* begin
    assume(!interrupts_external && !interrupts_timer && !interrupts_software);
  end
'''
    scenario = {'mutation': 3, 'mutation-serialization': 0, 'mutation-flag': 3,
                'mutation-fault': 2, 'mutation-order': 0}.get(mode)
    if scenario is not None:
        body += f'  always @* assume(sync_scenario == {scenario});\n'
    return body


def interrupt_witness(parameters, mode):
    body = r'''
  (* anyconst *) reg [2:0] irq_scenario;
  (* anyconst *) reg irq_delay;
  reg [1:0] irq_setup = 0, irq_packet = 0;
  reg irq_stalled = 0, irq_latched = 0, irq_redirected = 0;
  wire irq_initializing = irq_setup != 3;
  wire [1:0] irq_limit = irq_scenario == 3 || irq_scenario == 4 ? 2 : 1;
  always @(posedge clock) if (!reset) begin
    if (instruction_valid && instruction_ready) begin
      if (irq_initializing) irq_setup <= irq_setup + 1;
      else if (irq_packet != 3) irq_packet <= irq_packet + 1;
    end
    if (data_request_valid && !data_request_ready) irq_stalled <= 1;
    if (irq_memory_owned) irq_latched <= 1;
    if (takeInterrupt_layerCapture) begin irq_latched <= 0; irq_redirected <= 1; end
  end
  always @* begin
    assume(irq_scenario <= 5 && instruction_bits_length == 4 && instruction_bits_tag == 0 && !instruction_bits_fault);
    assume(instruction_bits_pc == RESET_PC);
    assume(instruction_valid == (irq_initializing || irq_packet < irq_limit || irq_redirected));
    assume(instruction_bits_instruction == (irq_initializing ?
      (irq_setup == 0 ? 32'h00800093 : irq_setup == 1 ? 32'h30409073 : 32'h30009073) :
      irq_redirected ? 32'h00000013 : irq_packet == 0 ?
      (irq_scenario == 1 ? 32'h0010302f : irq_scenario == 2 ? 32'h02108133 : irq_scenario == 5 ? 32'h0000100f : 32'h00103023) :
      irq_scenario == 3 ? 32'h02108133 : 32'h0000100f));
    assume(data_request_ready == (irq_stalled || (irq_scenario != 0 && irq_scenario != 4)));
    assume(data_response_valid == (data_response_ready && (irq_scenario != 3 || _multiply_output_valid)));
    assume(data_response_bits_tag == 0 && !data_response_bits_fault && data_response_bits_data == 0);
    assume(!interrupts_external && !interrupts_timer);
    assume(interrupts_software == (irq_memory_owned || irq_latched ||
      (owned && (!irq_delay || _multiply_output_valid)) ||
      (irq_scenario == 5 && issuedValid && issuedPacket_decoded_instruction_instruction[6:0] == 7'h0f)));
  end
'''.replace('RESET_PC', f"64'h{int(parameters['resetVector']):x}")
    if mode.startswith('mutation'):
        body += f"  always @* assume(irq_scenario == {0 if mode == 'mutation' else 2});\n"
    return body


def arbiter_case(parameters):
    count = 2 * parameters['hartCount']
    bits = (count - 1).bit_length()
    fields = ('address', 'data', 'size', 'mask', 'tag', 'write', 'fetch', 'atomic')
    payload = lambda prefix: '{' + ', '.join(prefix + '_bits_' + field for field in fields) + '}'
    vector = lambda suffix: '{' + ', '.join(f'ports_{i}_{suffix}' for i in reversed(range(count))) + '}'
    body = f'''
  reg past_valid = 0;
  reg pending, sent, wrapped;
  reg [{bits-1}:0] expected_owner;
  reg [149:0] captured;
  (* anyconst *) reg [{bits-1}:0] watched;
  reg [{bits}:0] bypassed;
  wire [{count-1}:0] requests = {vector('request_valid')};
  wire [{count-1}:0] ready = {vector('request_ready')};
  wire [{count-1}:0] responses = {vector('response_valid')};
  wire [{count-1}:0] consumers = {vector('response_ready')};
  wire [{count-1}:0] accepted = requests & ready;
  wire completed = downstream_response_valid && downstream_response_ready;
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
        assume($stable({{downstream_response_bits_data, downstream_response_bits_fault, downstream_response_bits_tag}}));
      end
      assert($onehot0(accepted) && $onehot0(responses));
      assert(pending == (state != 0) && sent == (state == 2));
      assert(next < {count});
      if (!pending && |requests) assert(|accepted);
      if (pending) begin
        assert(ready == 0 && expected_owner == owner);
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
      if (ports_{i}_response_valid) assert({{ports_{i}_response_bits_data, ports_{i}_response_bits_fault, ports_{i}_response_bits_tag}} ==
        {{downstream_response_bits_data, downstream_response_bits_fault, downstream_response_bits_tag}});
'''
    body += '    end\n  end\n'
    return ('MemoryArbiter', body, 'assign ports_0_response_valid =',
            "assign ports_0_response_valid = downstream_response_valid |")


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
  wire read_fire = axi_ar_valid && axi_ar_ready;
  wire write_address_fire = axi_aw_valid && axi_aw_ready;
  wire write_data_fire = axi_w_valid && axi_w_ready;
  wire read_reply = axi_r_valid && axi_r_ready;
  wire write_reply = axi_b_valid && axi_b_ready;
  wire [63:0] shifted_value = axi_r_bits_data >> (accepted_address[LANE:0] * 8);
  wire [63:0] loaded_value = accepted_size == 0 ? {56'd0, shifted_value[7:0]} :
    accepted_size == 1 ? {48'd0, shifted_value[15:0]} :
    accepted_size == 2 ? {32'd0, shifted_value[31:0]} : accepted_size == 3 ? shifted_value : 0;
  wire read_bad = expected_fault || axi_r_bits_id || !axi_r_bits_last ||
    axi_r_bits_resp != (is_atomic ? 1 : 0);
  wire [63:0] stored_value = is_atomic ? old_value + addend : addend;
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
        if (memory_request_bits_atomic) assume(memory_request_bits_write && !memory_request_bits_fetch &&
          memory_request_bits_size == 3 && memory_request_bits_mask == 255 && memory_request_bits_address[2:0] == 0);
        held <= 1; complete <= 0; expected_fault <= 0; old_value <= 0; retried <= 0;
        is_atomic <= memory_request_bits_atomic; accepted_address <= memory_request_bits_address;
        addend <= memory_request_bits_data; accepted_size <= memory_request_bits_size;
        accepted_mask <= memory_request_bits_mask; accepted_tag <= memory_request_bits_tag;
        can_read <= !memory_request_bits_write || memory_request_bits_atomic;
        can_write <= memory_request_bits_write && !memory_request_bits_atomic;
      end
      assert(memory_request_ready == !held && memory_response_valid == complete);
      assert(held == (can_read || can_write || complete));
      assert(!(can_read && can_write) && (!read_owned || can_read));
      assert(!(address_sent || data_sent) || can_write);
      if (held) begin
        assert(request_address == accepted_address && request_data == addend && request_size == accepted_size &&
          request_mask == accepted_mask && request_tag == accepted_tag && request_atomic == is_atomic);
        assert(data == old_value && fault == expected_fault);
      end
      if (held && !complete)
        assert(awDone == address_sent && wDone == data_sent && request_write == can_write);
      assert(axi_ar_valid == (can_read && !read_owned));
      assert(axi_aw_valid == (can_write && !address_sent));
      assert(axi_w_valid == (can_write && !data_sent));
      assert(axi_r_ready == read_owned && axi_b_ready == (address_sent && data_sent));
      if (axi_ar_valid) begin
        assert(held && !complete && !can_write);
        assert(axi_ar_bits_addr == accepted_address[PHYSICAL:0] && axi_ar_bits_id == 0 &&
          axi_ar_bits_len == 0 && axi_ar_bits_size == accepted_size && axi_ar_bits_lock == is_atomic);
      end
      if (axi_aw_valid) begin
        assert(held && !complete && !can_read);
        assert(axi_aw_bits_addr == accepted_address[PHYSICAL:0] && axi_aw_bits_id == 0 &&
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
          if (is_atomic && !read_bad) can_write <= 1;
          else complete <= 1;
        end
      end
      if (write_reply) begin
        assert(held && can_write && address_sent && data_sent);
        can_write <= 0; address_sent <= 0; data_sent <= 0;
        if (is_atomic && axi_b_bits_resp == 0 && !axi_b_bits_id) begin
          can_read <= 1; retried <= 1;
        end else begin
          complete <= 1;
          expected_fault <= axi_b_bits_id || axi_b_bits_resp != (is_atomic ? 1 : 0);
        end
      end
      if (memory_response_valid) begin
        assert(held && complete && !can_read && !can_write && !read_owned && !address_sent && !data_sent);
        assert(memory_response_bits_tag == accepted_tag && memory_response_bits_data == old_value);
        assert(memory_response_bits_fault == expected_fault);
        if (memory_response_ready) begin held <= 0; complete <= 0; end
      end
      if ($past(!reset && memory_response_valid && !memory_response_ready)) begin
        assert(memory_response_valid);
        assert($stable({memory_response_bits_data, memory_response_bits_fault, memory_response_bits_tag}));
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
    end
  end
'''
    for channel, fields in (('ar', ('addr', 'id', 'len', 'size', 'burst', 'lock', 'cache', 'prot', 'qos')),
                            ('aw', ('addr', 'id', 'len', 'size', 'burst', 'lock', 'cache', 'prot', 'qos')),
                            ('w', ('data', 'strb', 'last'))):
        payload = ', '.join(f'axi_{channel}_bits_{field}' for field in fields)
        body += f'''  always @(posedge clock) if (checked_past && $past(!reset && axi_{channel}_valid && !axi_{channel}_ready)) begin
    assert(axi_{channel}_valid); assert($stable({{{payload}}}));
  end
'''
    for token, value in (('LANE', lane_bits - 1), ('PHYSICAL', parameters['physicalAddressBits'] - 1),
                         ('WIDTH', width), ('BYTES', width // 8), ('MASKPAD', width // 8 - 8), ('PAD', width - 64)):
        body = body.replace(token, str(value))
    return ('Axi', body, 'request_atomic <= memory_request_bits_atomic;', 'request_atomic <= 0;')


def verify(rtl, directory, modules=None):
    directory.mkdir(parents=True, exist_ok=True)
    summary = directory / 'summary.json'
    summary.unlink(missing_ok=True)
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in manifest['sourceHashes'].items())
    sources = {p.name: p.read_text() for p in rtl.glob('*.sv') if 'DV' not in p.name and not p.name.startswith('ref_')}
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
    cases = [*cases, synchronization_case(manifest['parameters']), arbiter_case(manifest['parameters']), axi_case(manifest['parameters'])]
    if manifest['parameters'].get('iCacheBytes'):
        cases.append(instruction_cache_case(manifest['parameters']))
    if manifest['parameters'].get('enableInterrupts'):
        cases = [*cases, *interrupt_cases(manifest['parameters'])]
    assert not modules or set(modules) <= {case[0] for case in cases}, 'Unsupported proof selection'
    for name, body, before, after in cases:
        if name == 'MemoryArbiter' and not modules and (enabled or manifest['parameters']['enableInterrupts']):
            continue
        if modules and name not in modules and not (name.startswith('Pmp') and 'Pmp' in modules):
            continue
        unit = name.removeprefix('Interrupt').removeprefix('Synchronization')
        if unit == 'Csr':
            body += "\n  always @* if (readAddress == 12'hf14) assert(legal && readData == {60'd0, hartId});\n"
        module = 'DitDahA1' + ('Pmp' if name == 'PmpDecode' else unit)
        if name == 'PmpInterval':
            module = 'formal_interval'
            files = {module + '.sv': license + 'module formal_interval(input [64:0] low, high, input [63:0] address, input [2:0] size);\nendmodule\n'}
        else:
            files = dict(sources) if unit in ('Backend', 'InstructionCache') else {module + '.sv': sources[module + '.sv']}
        if unit == 'InstructionCache':
            for filename in files:
                match = re.fullmatch(r'(?:instructions|tags)_\d+x(\d+)\.sv', filename)
                if match:
                    files[filename] = license + header(sources[filename]) + f'\n(* anyseq *) reg [{int(match[1])-1}:0] arbitrary_read;\nassign R0_data = arbitrary_read;\nendmodule\n'
        if enabled and unit in ('Fetch', 'Lsu', 'Backend'):
            files['DitDahA1Pmp.sv'] = license + header(sources['DitDahA1Pmp.sv']) + '\n(* anyseq *) reg permit;\nassign allowed = permit;\nendmodule\n'
        if unit in ('Backend', 'Multiply', 'Csr', 'MemoryArbiter', 'Axi', 'InstructionCache') or enabled:
            if unit == 'Backend':
                files['DitDahA1Multiply.sv'] = license + header(sources['DitDahA1Multiply.sv']) + RESOURCE + 'endmodule\n'
            if name == 'InterruptBackend':
                observed = files[module + '.sv']
                for port in ('trapPc', 'trapCause', 'trapValue', 'we', 'write'):
                    pattern = rf'\.{port}\s*\(([^()]*)\)'
                    connections = re.findall(pattern, observed)
                    assert len(connections) == 1, (port, connections)
                    observed = re.sub(pattern, f'.{port}(formal_{port})', observed)
                    body += f'\n  wire {"[63:0] " if port.startswith("trap") else ""}formal_{port} = {connections[0]};\n'
                files[module + '.sv'] = observed
            files[module + '.sv'] = files[module + '.sv'].replace('endmodule', body + '\nendmodule', 1)
            top = module
        else:
            top = 'formal_top'
            files['wrapper.sv'] = license + header(files[module + '.sv']).replace(module, top, 1) + f'\n  {module} dut (.*);\n' + body + 'endmodule\n'
        checks = [('prove', before, after), ('cover', before, after), ('mutation', before, after)]
        if name == 'InterruptBackend':
            checks += [('mutation-pc', '? resumePc', "? 64'h0"),
                       ('mutation-write', 'formal_write =', "formal_write = 1'h1 |")]
        if unit == 'MemoryArbiter':
            advance = re.findall(r'next <= [^;]+;', sources[module + '.sv'])[-1]
            checks += [('mutation-release', 'downstream_response_valid & downstream_response_ready_0', 'downstream_response_valid'),
                       ('mutation-priority', advance, "next <= '0;")]
        if unit == 'Axi':
            original = sources[module + '.sv']
            retry_state = re.findall(r"state <= \w+ \? 3'h1 : 3'h4;", original)[0]
            read_update = re.search(r'if \((\w+)\)\n\s+data <=', original).group(0)
            checks += [('mutation-retry', retry_state, "state <= 3'h4;"),
                       ('mutation-stale', read_update, read_update.replace(')', ' && !retried)', 1)),
                       ('mutation-read-error', 'request_atomic & ~readFault', 'request_atomic'),
                       ('mutation-write-error', "axi_b_bits_resp == 2'h0", "axi_b_bits_resp != 2'h1"),
                       ('mutation-old-value', 'assign memory_response_bits_data = data;',
                        'assign memory_response_bits_data = request_atomic ? data + request_data : data;')]
        if name == 'Pmp':
            checks += [('mutation-atomic-read', 'state_config[0] & state_config[1]', 'state_config[1]'),
                       ('mutation-atomic-write', 'state_config[0] & state_config[1]', 'state_config[0]')]
        if name == 'SynchronizationBackend':
            checks += [('mutation-serialization', 'assign output_bits_serializing =',
                        "assign output_bits_serializing = 1'h0 &", 'DitDahA1Decode.sv'),
                       ('mutation-flag', 'assign output_bits_fenceI =',
                        "assign output_bits_fenceI = 1'h0 &", 'DitDahA1Execute.sv'),
                       ('mutation-fault', '~input_bits_instruction_fault & input_bits_fenceI',
                        'input_bits_fenceI', 'DitDahA1Commit.sv'),
                       ('mutation-order', '~memoryOperation | memoryPending & _lsu_output_valid', "1'h1")]
        if unit == 'InstructionCache':
            checks += [('mutation-hold', 'assign downstream_request_valid = downstream_request_valid_0;',
                        'assign downstream_request_valid = downstream_request_valid_0 & ~cancel;'),
                       ('mutation-word', "word <= word + 4'h1;", "word <= word + 4'h2;"),
                       ('mutation-invalidate', 'invalidate\n          ?', "1'h0\n          ?"),
                       ('mutation-denied', '_GEN_10 & ~(abort | allowed) & _GEN_12', "1'h0")]
        for check in checks:
            mode, before, after, *target = check
            mutated_file = target[0] if target else module + '.sv'
            mutating = mode.startswith('mutation')
            work = directory / f'{name.lower()}-{mode}'
            work.mkdir(exist_ok=True)
            for filename, text in files.items():
                if name == 'SynchronizationBackend' and mode != 'prove' and filename == module + '.sv':
                    text = text.replace('endmodule', synchronization_witness(manifest['parameters'], mode) + '\nendmodule', 1)
                if name == 'InterruptBackend' and mode != 'prove' and filename == module + '.sv':
                    text = text.replace('endmodule', interrupt_witness(manifest['parameters'], mode) + '\nendmodule', 1)
                if unit == 'MemoryArbiter' and mode != 'prove' and filename == module + '.sv':
                    guidance = ''.join(f'    assume(ports_{i}_request_valid);\n' + ''.join(
                        f"    assume(ports_{i}_request_bits_{field} == 0);\n"
                        for field in ('address', 'data', 'size', 'mask', 'tag', 'write', 'fetch', 'atomic'))
                        for i in range(2 * manifest['parameters']['hartCount']))
                    guidance += f'''    assume(downstream_request_ready == (witness_age != 1));
    assume(downstream_response_valid == sent);
    assume(consumers == (witness_age == 3 ? 0 : {2 * manifest['parameters']['hartCount']}'d{(1 << (2 * manifest['parameters']['hartCount'])) - 1}));
'''
                    text = text.replace('endmodule', '''  reg [2:0] witness_age = 0;
  always @(posedge clock) if (reset) witness_age <= 0;
  else if (witness_age != 7) witness_age <= witness_age + 1;
  always @* begin
''' + guidance + '  end\nendmodule', 1)
                if unit == 'Axi' and mutating and filename == module + '.sv':
                    width = manifest['parameters']['axiDataBits']
                    read_code = 2 if mode == 'mutation-read-error' else 1
                    write_code = '0' if mode == 'mutation-retry' else '2' if mode == 'mutation-write-error' else '(retried ? 1 : 0)' if mode == 'mutation-stale' else '1'
                    guidance = f'''
  always @* begin
    assume(memory_request_valid && memory_request_bits_atomic && memory_request_bits_write && !memory_request_bits_fetch);
    assume(memory_request_bits_address == 8 && memory_request_bits_data == 1 && memory_request_bits_tag == 37);
    assume(memory_request_bits_size == 3 && memory_request_bits_mask == 255 && memory_response_ready);
    assume(axi_ar_ready && axi_aw_ready && axi_w_ready);
    assume(axi_r_valid == read_owned && axi_b_valid == (address_sent && data_sent));
    assume(!axi_r_bits_id && axi_r_bits_last && !axi_b_bits_id);
    assume(axi_r_bits_resp == {read_code} && axi_b_bits_resp == {write_code});
    assume(axi_r_bits_data == ((retried ? {width}'d11 : {width}'d7) << {8 * (8 % (width // 8))}));
  end
'''
                    text = text.replace('endmodule', guidance + '\nendmodule', 1)
                if unit == 'InstructionCache' and mode != 'prove' and filename == module + '.sv':
                    scenario = {'mutation': 7, 'mutation-hold': 1, 'mutation-word': 0,
                                'mutation-invalidate': 6, 'mutation-denied': 3}.get(mode)
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
                    guidance = guidance.replace('SCENARIO_MAX', '4' if scenario is None else '7')
                    if scenario is not None:
                        guidance += f'  always @* assume(cache_scenario == {scenario});\n'
                    text = text.replace('endmodule', guidance + '\nendmodule', 1)
                if mutating and filename == mutated_file:
                    assert text.count(before) == (2 if name == 'Csr' else 1), (name, before)
                    text = text.replace(before, after, 1)
                (work / filename).write_text(text)
            task = 'bmc' if mutating else mode
            if mode == 'mutation' and name == 'Fetch':
                task = 'prove'
            engine = 'abc pdr' if task == 'prove' and unit not in ('Multiply', 'Pmp', 'PmpDecode', 'PmpInterval', 'Csr', 'Axi', 'InstructionCache') and name != 'SynchronizationBackend' else 'smtbmc z3'
            timeout = 180 if name == 'InterruptBackend' and task == 'cover' else 60
            witness_option = 'aigsmt z3\n' if engine == 'abc pdr' else ''
            preparation = (f'hierarchy -check -top {top}\nproc\nflatten\nopt_expr -keepdc\nopt_clean\nwreduce\nopt_clean\ncheck'
                           if name.startswith('Pmp') else f'prep -top {top} -flatten')
            depth = 6 * manifest['parameters']['hartCount'] + 8 if unit == 'MemoryArbiter' else 72 if task == 'cover' or (unit == 'InstructionCache' and mode in ('mutation', 'mutation-invalidate')) else 1 if name.startswith('Pmp') else (3 if task == 'prove' else 8) if unit == 'Csr' else 4 if name in ('Multiply', 'Axi', 'SynchronizationBackend', 'InstructionCache') and task == 'prove' else 24
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
    assert all((rtl / p).read_text() == text for p, text in sources.items()), 'RTL changed during proofs'
    assert checker_hash == hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'Checker changed during proofs'
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in manifest['sourceHashes'].items())
    proved = {report['propertyGroup'] for report in reports if report['mode'] == 'prove' and report['status'] == 'PASS'}
    if 'Pmp' in proved:
        assert {'PmpInterval', 'PmpDecode'} <= proved, 'Missing PMP composition prerequisites'
    summary.write_text(json.dumps(dict(
        scope='module-level safety, cover reachability and mutation detection', propertyGroups=sorted(proved),
        assumptions='initial reset, then no reset except CSR proofs; Fetch responses require accepted requests and stable blocked payloads; enabled control proofs abstract combinational authorization',
        pmpComposition='Pmp uses independently proved PmpInterval identities and PmpDecode request spans; no table-value restrictions' if 'Pmp' in proved else None,
        backendAbstraction='arbitrary multiply result and completion delay under the separately proved resource protocol',
        synchronization='raw barrier encodings, independent accepted-data ownership until retirement, sequential instruction synchronization redirect and younger flush; no data response timing assumptions' if 'SynchronizationBackend' in proved else None,
        synchronizationWitnessGuidance='cover/mutations only: aligned zero-address SD, FENCE/FENCE.I, one request and response stall, faulted FENCE.I and quiescent interrupts; unrestricted safety proof' if 'SynchronizationBackend' in proved else None,
        instructionCache='control proof at configured geometry; arbitrary native SRAM read outputs; independent upstream/downstream ownership, authorization, cancellation drain, full-fill publication, invalidation and precise fallback; functional array contents require separate simulation' if 'InstructionCache' in proved else None,
        cacheWitnessGuidance='cover/mutations only: zero-address demand, successful service, canceled stalls, last-beat/post-fill invalidation, permission denial and demand/speculative fault scenarios; unrestricted safety proof' if 'InstructionCache' in proved else None,
        arbitration='one retained request and owner; at most 2N-1 other completions while continuously requesting; no bound on external service delay' if 'MemoryArbiter' in proved else None,
        interruptProgress='with eligibility held, successful matching data response reaches interrupt entry or priority synchronous trap within three cycles; memory service itself is external' if any(r['propertyGroup'] == 'InterruptBackend' for r in reports) else None,
        witnessGuidance='InterruptBackend cover/mutations use ADDI and mie/mstatus initialization then SD, AMOADD.D, MUL, SD-to-MUL, SD-to-FENCE.I or FENCE.I, fixed PCs/tag zero, successful data replies, retained request stall and software interrupt scenarios; unrestricted proof' if any(r['propertyGroup'] == 'InterruptBackend' for r in reports) else None,
        arbiterWitnessGuidance='cover/mutations hold all requesters valid with zero payloads, one request stall and one response stall then immediate service; unrestricted proof' if 'MemoryArbiter' in proved else None,
        atomicTransport='independent request and AXI channel ownership; old-value return, exclusive retry and error isolation; no external-memory atomicity or eventual-success theorem' if 'Axi' in proved else None,
        axiAssumptions='initial reset only; atomic inputs are aligned doubleword read-modify-write requests; R requires accepted AR, B requires accepted AW and W; blocked response payloads persist; data, IDs, responses, last and delays unrestricted' if 'Axi' in proved else None,
        axiMutationGuidance='mutations only: aligned address8, addend1, read values7 then11 after retry, immediate service and per-fault response codes; prove and cover unrestricted' if 'Axi' in proved else None,
        configurations=manifest['parameters'], sourceHashes=manifest['sourceHashes'],
        rtlHashes={p: hashlib.sha256(text.encode()).hexdigest() for p, text in sources.items()},
        checkerHash=checker_hash, tools=tools, reports=reports), indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--rtl', type=Path, default=Path('result/production'))
    parser.add_argument('--output', type=Path, default=Path('result/formal'))
    parser.add_argument('--modules', nargs='+', choices=('Fetch', 'Multiply', 'Backend', 'Pmp', 'PmpDecode', 'PmpInterval', 'Csr', 'Lsu', 'InterruptCsr', 'InterruptBackend', 'SynchronizationBackend', 'InstructionCache', 'MemoryArbiter', 'Axi'))
    args = parser.parse_args()
    verify(args.rtl, args.output, args.modules)
