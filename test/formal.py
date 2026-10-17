# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Prove execution and transaction safety on generated RTL."""

import argparse
import hashlib
import json
import os
from pathlib import Path
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
          memory_request_bits_write, memory_request_bits_fetch}));
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
        (fetch ? state_config[i*8+2] : write ? state_config[i*8+1] : state_config[i*8]));
    end
    assert(allowed == (expected && size <= 3 &&
      ({{1'b0, address}} + (65'd1 << size)) <= (65'd1 << {width + 2})));
    cover(allowed && fetch);
    cover(!allowed && write);
    cover(!allowed && size == 3 && !state_config[7]);
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
  reg past_valid = 0, pending, denied, store;
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
      end
      if (output_valid && output_ready) pending <= 0;
      if (pending && denied) begin
        assert(!memory_request_valid && output_valid && output_bits_instruction_fault);
        assert(output_bits_instruction_cause == (store ? 7 : 5) && output_bits_instruction_tval == address);
      end
      if (past_valid && $past(!reset && memory_request_valid && !memory_request_ready)) begin
        assert(memory_request_valid);
        assert($stable({memory_request_bits_address, memory_request_bits_data, memory_request_bits_tag,
          memory_request_bits_mask, memory_request_bits_size, memory_request_bits_write, memory_request_bits_fetch}));
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
          data_request_bits_mask, data_request_bits_size, data_request_bits_write, data_request_bits_fetch}}));
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
      cover(_csr_interruptPending && irq_memory_commit && !memoryPending);
      cover(takeInterrupt_layerCapture && !decodedValid && !issuedValid && !resultValid && !commitValid);
      cover(takeInterrupt_layerCapture && executePending);
      cover(takeInterrupt_layerCapture && $past(commit_output_valid_layerCapture && irq_memory_commit));
      cover(irq_service_age == 3 && takeInterrupt_layerCapture);
    end
  end
'''
    return [('InterruptCsr', csr, 'status[3]\n    &', "1'h1\n    &"),
            ('InterruptBackend', backend, '_csr_interruptPending & ~memoryPending', '_csr_interruptPending')]


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
    if manifest['parameters'].get('enableInterrupts'):
        cases = [*cases, *interrupt_cases(manifest['parameters'])]
    assert not modules or set(modules) <= {case[0] for case in cases}, 'Unsupported proof selection'
    for name, body, before, after in cases:
        if modules and name not in modules and not (name.startswith('Pmp') and 'Pmp' in modules):
            continue
        unit = name.removeprefix('Interrupt')
        module = 'DitDahA1' + ('Pmp' if name == 'PmpDecode' else unit)
        if name == 'PmpInterval':
            module = 'formal_interval'
            files = {module + '.sv': license + 'module formal_interval(input [64:0] low, high, input [63:0] address, input [2:0] size);\nendmodule\n'}
        else:
            files = dict(sources) if unit == 'Backend' else {module + '.sv': sources[module + '.sv']}
        if enabled and unit in ('Fetch', 'Lsu', 'Backend'):
            files['DitDahA1Pmp.sv'] = license + header(sources['DitDahA1Pmp.sv']) + '\n(* anyseq *) reg permit;\nassign allowed = permit;\nendmodule\n'
        if unit in ('Backend', 'Multiply', 'Csr') or enabled:
            if unit == 'Backend':
                files['DitDahA1Multiply.sv'] = license + header(sources['DitDahA1Multiply.sv']) + RESOURCE + 'endmodule\n'
            if name == 'InterruptBackend':
                import re
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
        for mode, before, after in checks:
            mutating = mode.startswith('mutation')
            work = directory / f'{name.lower()}-{mode}'
            work.mkdir(exist_ok=True)
            for filename, text in files.items():
                if name == 'InterruptBackend' and mode != 'prove' and filename == module + '.sv':
                    # Legal initialization narrows witness search, never the safety proof.
                    prefix = '''
  reg [1:0] setup_count = 0;
  always @(posedge clock) if (!reset) begin
    assume(!instruction_bits_fault && instruction_bits_length == 4 && instruction_bits_tag == 0);
    assume(instruction_bits_pc == 64'h100 + {62'd0, setup_count} * 4);
    if (setup_count != 3) begin
      assume(instruction_valid);
      assume(instruction_bits_instruction == (setup_count == 0 ? 32'h00800093 :
        setup_count == 1 ? 32'h30409073 : 32'h30009073));
      if (instruction_ready) setup_count <= setup_count + 1;
    end else assume(instruction_bits_instruction == 32'h02108133 || instruction_bits_instruction == 32'h00103023 ||
      instruction_bits_instruction == 32'h00000113 || instruction_bits_instruction == 0);
  end
'''
                    prefix = prefix.replace("64'h100", f"64'h{int(manifest['parameters']['resetVector']):x}")
                    text = text.replace('endmodule', prefix + '\nendmodule', 1)
                if mutating and filename == module + '.sv':
                    assert text.count(before) == (2 if name == 'Csr' else 1), (name, before)
                    text = text.replace(before, after, 1)
                (work / filename).write_text(text)
            task = 'bmc' if mutating else mode
            if mode == 'mutation' and name == 'Fetch':
                task = 'prove'
            engine = 'abc pdr' if task == 'prove' and unit not in ('Multiply', 'Pmp', 'PmpDecode', 'PmpInterval', 'Csr') else 'smtbmc z3'
            timeout = 180 if name == 'InterruptBackend' and task == 'cover' else 60
            witness_option = 'aigsmt z3\n' if engine == 'abc pdr' else ''
            preparation = (f'hierarchy -check -top {top}\nproc\nflatten\nopt_expr -keepdc\nopt_clean\nwreduce\nopt_clean\ncheck'
                           if name.startswith('Pmp') else f'prep -top {top} -flatten')
            config = f'''[options]
mode {task}
depth {72 if task == 'cover' else 1 if name.startswith('Pmp') else (3 if task == 'prove' else 8) if unit == 'Csr' else 4 if name == 'Multiply' and task == 'prove' else 24}
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
        scope=('machine interrupt state and precise event/transaction ownership' if any(r['propertyGroup'].startswith('Interrupt') for r in reports) else
               'PMP interval/decode/decision composition, CSR locking and transaction safety' if enabled else
               'transaction and execution safety; zero/unit multiply identities; bounded completion'),
        assumptions='initial reset, then no reset except CSR proofs; Fetch responses require accepted requests and stable blocked payloads; enabled control proofs abstract combinational authorization',
        pmpComposition='Pmp uses independently proved PmpInterval identities and PmpDecode request spans; no table-value restrictions' if 'Pmp' in proved else None,
        backendAbstraction='arbitrary multiply result and completion delay under the separately proved resource protocol',
        interruptProgress='with eligibility held, successful matching data response reaches interrupt entry or priority synchronous trap within three cycles; memory service itself is external' if any(r['propertyGroup'] == 'InterruptBackend' for r in reports) else None,
        witnessGuidance='InterruptBackend cover/mutations use ADDI and mie/mstatus initialization, then ADDI/MUL/SD/illegal packets at aligned fixed PCs and tag zero; unrestricted proof' if any(r['propertyGroup'] == 'InterruptBackend' for r in reports) else None,
        configurations=manifest['parameters'], sourceHashes=manifest['sourceHashes'],
        rtlHashes={p: hashlib.sha256(text.encode()).hexdigest() for p, text in sources.items()},
        checkerHash=checker_hash, tools=tools, reports=reports), indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--rtl', type=Path, default=Path('result/production'))
    parser.add_argument('--output', type=Path, default=Path('result/formal'))
    parser.add_argument('--modules', nargs='+', choices=('Fetch', 'Multiply', 'Backend', 'Pmp', 'PmpDecode', 'PmpInterval', 'Csr', 'Lsu', 'InterruptCsr', 'InterruptBackend'))
    args = parser.parse_args()
    verify(args.rtl, args.output, args.modules)
