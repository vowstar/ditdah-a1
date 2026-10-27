# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Compare generated RTL against instruction and bus-level expectations."""

import argparse
from collections import Counter, deque
from concurrent.futures import ProcessPoolExecutor
import hashlib
import importlib.util
from itertools import chain
import json
import os
import re
from pathlib import Path
import subprocess
from types import SimpleNamespace

from contracts import verify as verify_contracts, verify_storage, backend_control_signals
from model import ExclusiveMonitor, Fault, LocalInterrupts, Model, MASK, atomic_value, integer_value, pmp_allowed, sv39_walk
from programs import cases, multicore_cases, platform_program


def run(command, log, cwd=None, timeout=600):
    with log.open('w') as stream:
        result = subprocess.run(list(map(str, command)), cwd=cwd, stdout=stream, stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        with log.open('rb') as stream:
            stream.seek(max(0, log.stat().st_size - 10000))
            tail = stream.read().decode(errors='replace')
        raise RuntimeError(f'{command[0]} failed; see {log}\n' + tail)


def configuration(width):
    base = 0 if width == 64 else 1 << 40
    regions = []
    for offset, size, read, write, execute, device in (
            (0, 0x4000, True, True, True, False),
            (0x4000, 0x1000, True, False, True, False),
            (0x5000, 0x1000, True, True, False, True),
            (0x6000, 0x1000, False, False, False, False),
            (0x7000, 0x1000, True, True, False, False),
            (0x8000, 0x1000, False, False, True, False)):
        regions.append(dict(base=str(base + offset), size=str(size), readable=read,
                            writable=write, executable=execute, device=device, atomic=offset == 0,
                            dataCacheable=False))
    return dict(resetVector=str(base), axiDataBits=width, physicalAddressBits=32 if width == 64 else 56,
                virtualAddressBits=0, iCacheBytes=0, dCacheBytes=0, l2CacheBytes=0, pmpEntries=0,
                memoryRegions=regions)


def local_interrupt_base(config):
    value = config.get('localInterruptBase')
    return int(value) if value is not None else None


def compile_tb(rtl, directory, width, pa, top='core_tb', source=None, extra_files=(), software=None):
    source = source or Path('test/core_tb.sv').resolve()
    files = [(rtl / name).resolve() for name in (rtl / 'filelist.f').read_text().splitlines()]
    parameters = json.loads((rtl / 'ditdah_a1_config.json').read_text())['parameters']
    interrupts, harts = parameters['enableInterrupts'], parameters['hartCount']
    issue_width = parameters['issueWidth']
    probes = dict(re.findall(r'`define ref_DitDahA1Backend_(\w+) (\S+)',
                             (rtl / 'ref_DitDahA1Backend.sv').read_text()))
    fields = dict(pc=64, instruction=32, nextPc=64, rd=5, rdWrite=1,
                  value=64, trap=1, cause=64, tval=64)
    retirement = [f'''  localparam integer ISSUE_WIDTH = {issue_width};
  typedef struct packed {{
    logic traceValid;
    logic [63:0] traceOrder;
''' + '\n'.join(f'    logic [{bits - 1}:0] trace{name[0].upper() + name[1:]};' for name, bits in fields.items()) + f'''
    logic [{((5 + parameters.get('loadQueueEntries', 1)) * issue_width).bit_length() - 1}:0] pipelineOccupancy;
    logic pipelineStall;
  }} trace_t;
  trace_t traces[{harts}][ISSUE_WIDTH];
  wire [7:0] retire_tag[{harts}][ISSUE_WIDTH];
  wire [{issue_width.bit_length() - 1}:0] retire_count[{harts}], issue_count[{harts}];
  function automatic logic retired_pc(input integer hart, input logic [63:0] pc);
    retired_pc = 0;
    for (integer lane = 0; lane < ISSUE_WIDTH; lane++)
      retired_pc |= traces[hart][lane].traceValid && traces[hart][lane].tracePc == pc;
  endfunction''']
    retirement.append(f'''
  bit pipeline_events;
  initial pipeline_events = $test$plusargs("PIPELINE_EVENTS");
  bit work_metrics;
  logic [63:0] work_begin_pc, work_end_pc;
  initial work_metrics = $value$plusargs("WORK_BEGIN=%h", work_begin_pc) && $value$plusargs("WORK_END=%h", work_end_pc);
  longint unsigned metric_cycles = 0;
  longint unsigned metric_stalls[{harts}], metric_occupancy[{harts}], metric_peak[{harts}];
  longint unsigned metric_issue[{harts}][ISSUE_WIDTH + 1], metric_retire[{harts}][ISSUE_WIDTH + 1];
  initial for (integer h = 0; h < {harts}; h++) begin
    metric_stalls[h] = 0; metric_occupancy[h] = 0; metric_peak[h] = 0;
    for (integer n = 0; n <= ISSUE_WIDTH; n++) begin
      metric_issue[h][n] = 0; metric_retire[h][n] = 0;
    end
  end
  task automatic observe_metrics;
    integer retired;
    metric_cycles++;
    {'observe_read_metrics();' if top == 'core_tb' and (parameters.get('fabricReadSlots') or harts > 1) else ''}
    for (integer h = 0; h < {harts}; h++) begin
      if (work_metrics && retired_pc(h, work_begin_pc)) $display("WORK_CYCLE %0d 0 %0d", h, metric_cycles);
      if (work_metrics && retired_pc(h, work_end_pc)) $display("WORK_CYCLE %0d 1 %0d", h, metric_cycles);
      metric_issue[h][issue_count[h]]++;
      retired = 0;
      for (integer lane = 0; lane < ISSUE_WIDTH; lane++)
        if (traces[h][lane].traceValid && !traces[h][lane].traceTrap) retired++;
      metric_retire[h][retired]++;
      metric_stalls[h] += traces[h][0].pipelineStall;
      metric_occupancy[h] += traces[h][0].pipelineOccupancy;
      if (traces[h][0].pipelineOccupancy > metric_peak[h]) metric_peak[h] = traces[h][0].pipelineOccupancy;
    end
  endtask
  final for (integer h = 0; h < {harts}; h++) begin
    $display("METRICS %0d %0d %0d %0d %0d", h, metric_cycles, metric_stalls[h], metric_occupancy[h], metric_peak[h]);
    for (integer n = 0; n <= ISSUE_WIDTH; n++)
      $display("METRIC_WIDTH %0d %0d %0d %0d", h, n, metric_issue[h][n], metric_retire[h][n]);
  end''')
    bindings, ports, platform = [], [], []
    local_base = local_interrupt_base(parameters) if top == 'core_tb' else None
    writeback = bool(parameters.get('dCacheWriteback'))
    observers = [f'  wire [{harts - 1}:0] architectural_fetch_busy;\n  wire [63:0] architectural_fetch_pc[{harts}];']
    read_slots = parameters.get('fabricReadSlots') or 2
    read_suffixes = tuple('' if n == 0 else f'_{n-1}' for n in range(read_slots))
    if top == 'core_tb' and (parameters.get('fabricReadSlots') or harts > 1):
        occupancy = ' + '.join(f"integer'(dut.fabric.readers.state{suffix} != 0)" for suffix in read_suffixes)
        buffered = '(' + ' || '.join(f'dut.fabric.readers.state{suffix} == 5' for suffix in read_suffixes) + ')' if parameters['axiDataBits'] > 64 and (parameters.get('enableBurstRefill') or parameters.get('dCacheRefillBytes') == 64) else "1'b0"
        observers.append(f'''  longint unsigned read_occupancy[0:{read_slots}];
  longint unsigned read_drain_wait = 0, read_buffer_wait = 0;
  initial for (integer n = 0; n <= {read_slots}; n++) read_occupancy[n] = 0;
  task automatic observe_read_metrics;
    read_occupancy[{occupancy}]++;
    if (!dut.fabric.active && !dut.fabric.allowRead && !dut.fabric.readers.empty) read_drain_wait++;
    if ({buffered} && rvalid && !rready) read_buffer_wait++;
  endtask
  final begin
    for (integer n = 0; n <= {read_slots}; n++) $display("READ_OCCUPANCY %0d %0d", n, read_occupancy[n]);
    $display("READ_STALL %0d %0d", read_drain_wait, read_buffer_wait);
  end''')
    for hart in range(harts if top == 'core_tb' else 1):
        fetch = f'dut.core_{hart}.frontend.fetch' if top == 'core_tb' else 'dut.frontend.fetch'
        order = fetch.replace('.frontend.fetch', '.backend.dV.traceOrder')
        prefix = f'$write("HART {hart} "); ' if harts > 1 else ''
        backend = fetch.replace('.frontend.fetch', '.backend')
        decoded = backend + '.decodedPackets_0_instruction'
        issued = backend + '.issuedPackets_0_decoded_instruction'
        _, recovery = backend_control_signals((rtl / 'DitDahA1Backend.sv').read_text())
        observers.append(f'''  always @(posedge clock) if (!reset && pipeline_events && issue_count[{hart}] != 0)
    $display("ISSUE_GROUP {hart} %0d %016h %08h %0d", metric_cycles, {decoded}_pc, {decoded}_instruction, issue_count[{hart}]);''')
        if re.search(r'\bearlyRedirect\b', (rtl / 'DitDahA1Backend.sv').read_text()):
            observers.append(f'''  always @(posedge clock) if (!reset && {"1'b1" if parameters.get('branchPredictorEntries') else 'pipeline_events'} && {backend}.{recovery})
    $display("RECOVERY {hart} %0d %016h %02h %016h", metric_cycles, {issued}_pc, {issued}_tag, {backend}.redirectPc);''')
            observers.append(f'''  always @(posedge clock) if (!reset && pipeline_events && {backend}.redirect && !{backend}.{recovery})
    $display("RETIRE_REDIRECT {hart} %016h %01h", traces[{hart}][0].tracePc, traces[{hart}][0].traceTrap);''')
        for name, probe in (('retire_count', 'count'), ('issue_count', 'issueCount')):
            retirement.append(f'  assign {name}[{hart}] = {backend}.{probes[probe]};')
        if (1 << issue_width.bit_length()) - 1 > issue_width:
            retirement.append(f'  always @(posedge clock) if (!reset && (retire_count[{hart}] > ISSUE_WIDTH || issue_count[{hart}] > ISSUE_WIDTH)) $fatal(1, "Pipeline count");')
        for lane in range(issue_width):
            target = f'traces[{hart}][{lane}]'
            tag_select = f'[{lane * 8} +: 8]' if issue_width > 1 else ''
            retirement += [f'  assign retire_tag[{hart}][{lane}] = {backend}.{probes["fetchTag"]}{tag_select};',
                           f'  assign {target}.traceValid = retire_count[{hart}] > {lane};',
                           f'  assign {target}.traceOrder = {backend}.{probes["order"]} + 64\'d{lane};']
            for name, bits in fields.items():
                select = f'[{lane * bits} +: {bits}]' if issue_width > 1 else ''
                retirement.append(f'  assign {target}.trace{name[0].upper() + name[1:]} = {backend}.{probes[name]}{select};')
            for name in ('pipelineOccupancy', 'pipelineStall'):
                retirement.append(f'  assign {target}.{name} = {backend}.{probes[name]};')
        fetch_words = (1 if issue_width == 1 else 2 if issue_width == 2 else 4) if parameters['iCacheBytes'] else 1
        suffix_format = ' %01h' + ' %08h' * (fetch_words - 1) if fetch_words > 1 else ''
        suffix_values = ', ' + ', '.join([f'{fetch}.output_bits_count',
            *(f'{fetch}.output_bits_following_{lane - 1}' for lane in range(1, fetch_words))]) if fetch_words > 1 else ''
        early = f'{backend}.{recovery}'
        prediction = ''
        if parameters.get('branchPredictorEntries'):
            frontend = fetch.removesuffix('.fetch')
            word = f'{issued}_instruction'
            control = f"({word}[6:0] == 7'h6f || ({word}[6:0] == 7'h67 && {word}[14:12] == 0) || ({word}[6:0] == 7'h63 && ({word}[14:12] == 0 || {word}[14:12] == 1 || {word}[14])))"
            prediction = f'''    if ({backend}.execute.output_valid && {backend}.execute.output_ready &&
        !{backend}.execute.output_bits_instruction_fault && {control}) begin
      {prefix}$display("BRANCH_RESOLVE %016h %02h %08h %01h %016h %016h", {issued}_pc, {issued}_tag,
        {issued}_instruction, {issued}_predictedTaken, {issued}_predictedPc, {backend}.execute.output_bits_nextPc); end
'''
            feedback = f'''    if ({frontend}.prediction_clear) begin {prefix}$display("PREDICT_CLEAR"); end
    else if ({frontend}.prediction_valid) begin
      {prefix}$display("PREDICT_UPDATE %016h %016h %01h %01h", {frontend}.prediction_pc,
        {frontend}.prediction_nextPc, {frontend}.prediction_conditional, {frontend}.prediction_taken); end
'''
        else:
            feedback = ''
        observers.append(f'''  assign architectural_fetch_busy[{hart}] = !{fetch}.request_ready;
  assign architectural_fetch_pc[{hart}] = {fetch}.packet_pc;
  always @(posedge clock) if (!reset) begin
{prediction}
    if ({fetch}.output_valid && {fetch}.output_ready) begin
      {prefix}$display("ARCH_FETCH %016h %01h %08h %02h{suffix_format}", {fetch}.output_bits_pc,
        {fetch}.output_bits_fault, {fetch}.output_bits_instruction, {fetch}.output_bits_tag{suffix_values});
    end
    if ({fetch}.request_valid && {fetch}.request_ready) begin
      {prefix}$display("ARCH_REQUEST %016h %02h", {fetch}.request_bits_pc, {fetch}.request_bits_tag);
    end
    if ({fetch}.cancel) begin {prefix}$display("ARCH_CANCEL %016h %01h %016h %02h %016h", {order},
      {early}, {issued}_pc, {issued}_tag, {backend}.redirectPc); end
{feedback}
  end''')
        translated = parameters.get('virtualAddressBits') == 39
        dual = parameters.get('loadQueueEntries', 1) == 2
        if dual:
            lsu = backend + '.lsu'
            observers.append(f'''  bit lsu_head_{hart} = 0, lsu_tail_{hart} = 0;
  always @(posedge clock) if (reset) begin lsu_head_{hart} <= 0; lsu_tail_{hart} <= 0; end else begin
    if ({lsu}.input_valid && {lsu}.input_ready) begin
      {prefix}$display("LSU_REQUEST %01h %016h %02h %08h", lsu_tail_{hart}, {lsu}.input_bits_instruction_pc,
        {lsu}.input_bits_instruction_tag, {lsu}.input_bits_instruction_instruction);
      lsu_tail_{hart} <= !lsu_tail_{hart};
    end
    if ({lsu}.output_valid && {lsu}.output_ready) begin
      {prefix}$display("LSU_RESPONSE %01h %016h %02h %01h %016h %016h", lsu_head_{hart}, {lsu}.output_bits_instruction_pc,
        {lsu}.output_bits_instruction_tag, {lsu}.output_bits_instruction_fault, {lsu}.output_bits_instruction_cause, {lsu}.output_bits_instruction_tval);
      lsu_head_{hart} <= !lsu_head_{hart};
    end
  end''')
        if translated:
            unit = f'dut.core_{hart}' if top == 'core_tb' else 'dut'
            translation = unit + '.translation'
            for port in range(2):
                observers.append(f'''  always @(posedge clock) if (!reset) begin
    if ({translation}.ports_{port}_request_valid && {translation}.ports_{port}_request_ready) begin
      {prefix}$display("TRANSLATE_REQUEST {port} %016h %01h %01h %01h %016h %01h %01h", {translation}.ports_{port}_request_bits_address,
        {translation}.ports_{port}_request_bits_privilege, {translation}.ports_{port}_request_bits_fetch, {translation}.ports_{port}_request_bits_write,
        {translation}.state_satp, {translation}.state_sum, {translation}.state_mxr);
    end
    if ({translation}.ports_{port}_response_valid && {translation}.ports_{port}_response_ready) begin
      {prefix}$display("TRANSLATE_RESPONSE {port} %016h %01h %016h", {translation}.ports_{port}_response_bits_address,
        {translation}.ports_{port}_response_bits_fault, {translation}.ports_{port}_response_bits_cause);
    end
  end''')
            observers.append(f'''  always @(posedge clock) if (!reset) begin
    if ({translation}.memory_request_valid && {translation}.memory_request_ready) begin
      {prefix}$display("WALK_REQUEST %016h %02h %01h", {translation}.memory_request_bits_address, {"8'd2" if dual else translation + '.memory_request_bits_tag'}, {translation}.owner);
    end
    if ({translation}.memory_response_valid && {translation}.memory_response_ready) begin
      {prefix}$display("WALK_RESPONSE %016h %01h %02h", {translation}.memory_response_bits_data,
        {translation}.memory_response_bits_fault, {"8'd2" if dual else translation + '.memory_response_bits_tag'});
    end
  end''')
        if top == 'core_tb' and parameters['dCacheBytes'] or translated or dual:
            core = backend + '.lsu.memory' if translated or dual else f'dut.core_{hart}.data'
            cache = f'dut.data_cache_{hart}'
            sample = cache + '.dV'
            invalidate = (f'{cache}.probe_response_valid && {cache}.probe_response_ready && {cache}.probe_response_bits_last && {cache}.probeMatch && {cache}.probeRequest_invalidate' if writeback else
                          f'{cache}.probe_request_valid && {cache}.probe_request_ready && {cache}.probe_request_bits_invalidate')
            invalid_address = cache + ('.probeRequest_address' if writeback else '.probe_request_bits_address')
            observers.append(f'''  always @(posedge clock) if (!reset) begin
    if ({core}_request_valid && {core}_request_ready) begin
      {prefix}$display("ARCH_DATA_REQUEST %s %016h %0d %016h %02h %01h %01h",
        {core}_request_bits_atomic ? "atomic" : ({core}_request_bits_write ? "write" : "read"),
        {core}_request_bits_address, 1 << {core}_request_bits_size,
        {core}_request_bits_write ? {core}_request_bits_data & access_mask({core}_request_bits_size) : 64'b0,
        {core}_request_bits_tag, {core}_request_bits_privileged, {core}_request_bits_refillSize);
    end
''' + (f'''    if ({invalidate}) $display("INVALIDATE {hart} %016h %0d", {invalid_address}, cycles);
''' if top == 'core_tb' and parameters.get('dCacheRefillBytes', 8) == 64 else '') + (f'''    if ({sample}.sampleValid) begin
      {prefix}$display("CACHE_SAMPLE %016h %016h %02h %0d", {sample}.sampleAddress,
        {sample}.sampleData & access_mask({sample}.sampleSize), {sample}.sampleTag, 1 << {sample}.sampleSize);
    end
''' if top == 'core_tb' and parameters['dCacheBytes'] else '') + (f'''    if ({cache}.storeUpdating && {cache}.acquiring) begin
      {prefix}$display("CACHE_STORE %016h %016h %02h %0d", {cache}.request_address,
        {cache}.request_data & access_mask({cache}.request_size), {cache}.request_tag, 1 << {cache}.request_size);
    end
''' if top == 'core_tb' and writeback else '') + f'''
    if ({core}_response_valid && {core}_response_ready) begin
      {prefix}$display("ARCH_DATA_RESPONSE %016h %01h %02h", {core}_response_bits_data,
        {core}_response_bits_fault, {core}_response_bits_tag);
    end
  end''')
        if top == 'core_tb' and parameters.get('dCacheRefillBytes', 8) == 64:
            port = f'dut.fabric.data_{hart}_request'
            queued = parameters.get('fabricReadSlots') or harts > 1
            blocked = '!dut.fabric.allowRead' if queued else "1'b1"
            full = '(' + ' && '.join(f'dut.fabric.readers.state{suffix} != 0' for suffix in read_suffixes) + ')' if queued else "1'b0"
            owner = '(' + ' || '.join(f'(dut.fabric.readers.state{suffix} != 0 && dut.fabric.readers.owner{suffix} == {2*hart+1})' for suffix in read_suffixes) + ')' if queued else "1'b0"
            if queued and parameters.get('loadQueueEntries', 1) == 2:
                terms = [f'(dut.fabric.readers.state{suffix} != 0 && dut.fabric.readers.owner{suffix} == {2*hart+1})' for suffix in read_suffixes]
                owner = '(' + ' + '.join(f"integer'({term})" for term in terms) + ' >= 2 || ' + ' || '.join(
                    f'({term} && dut.fabric.readers.request_tag{suffix} == {port}_bits_tag)' for term, suffix in zip(terms, read_suffixes)) + ')'
            observers.append(f'''  longint unsigned data_line_wait_{hart} = 0;
  longint unsigned line_serial_wait_{hart} = 0, line_owner_wait_{hart} = 0, line_full_wait_{hart} = 0, line_arbiter_wait_{hart} = 0;
  always @(posedge clock) if (!reset && {port}_valid && !{port}_ready && {port}_bits_size == 6) begin
    data_line_wait_{hart}++;
    if ({blocked}) line_serial_wait_{hart}++;
    else if ({owner}) line_owner_wait_{hart}++;
    else if ({full}) line_full_wait_{hart}++;
    else line_arbiter_wait_{hart}++;
  end
  final begin
    $display("REFILL_WAIT {hart} %0d", data_line_wait_{hart});
    $display("REFILL_STALL {hart} %0d %0d %0d %0d", line_serial_wait_{hart}, line_owner_wait_{hart}, line_full_wait_{hart}, line_arbiter_wait_{hart});
  end''')
    if top == 'core_tb' and writeback:
        unit = 'dut.fabric.coherence'
        identity = '$write("HART %0d ", dut.fabric._arbiter_hartId);' if harts > 1 else ''
        identity += 'emit_source(bus_owner);'
        observers.append(f'''  always @(posedge clock) if (reset) writeback_pending <= 0; else begin
    if ({unit}.state == 2 && {unit}.downstream_request_valid && {unit}.downstream_request_ready) begin
      if (writeback_pending) $fatal(1, "Overlapping physical writeback");
      writeback_pending <= 1;
      writeback_request.address <= {unit}.downstream_request_bits_address;
      writeback_request.data <= {unit}.downstream_request_bits_data;
      writeback_request.mask <= {unit}.downstream_request_bits_mask;
      {identity}
      $display("WRITEBACK_REQUEST %016h %016h %02h %02h %01h", {unit}.downstream_request_bits_address,
        {unit}.downstream_request_bits_data, {unit}.downstream_request_bits_mask,
        {unit}.downstream_request_bits_tag, {unit}.downstream_request_bits_privileged);
    end
    if ({unit}.state == 3 && {unit}.downstream_response_valid && {unit}.downstream_response_ready) begin
      if (!writeback_pending) $fatal(1, "Unowned physical writeback reply");
      {identity}
      $display("WRITEBACK_RESPONSE %01h %02h %01h", {unit}.downstream_response_bits_fault,
        {unit}.downstream_response_bits_tag, {unit}.downstream_response_bits_last);
      if ({unit}.downstream_response_bits_last) writeback_pending <= 0;
    end
  end''')
    (directory / 'fetch_observers.svh').write_text('\n'.join(observers) + '\n')
    (directory / 'retire_bindings.svh').write_text('\n'.join(retirement) + '\n')
    if top == 'core_tb':
        devices = ' || '.join(f"(request.address >= 64'd{int(region['base'])} && request.address < 64'd{int(region['base']) + int(region['size'])})"
                             for region in parameters['memoryRegions'] if region['device']) or "1'b0"
        coherent = ' || '.join('(' + (f"request.address >= 64'd{int(r['base'])} && " if int(r['base']) else '') +
                              f"request.address < 64'd{int(r['base']) + int(r['size'])})"
                               for r in parameters['memoryRegions'] if r.get('dataCacheable') and r['readable'] and not r['device']) if writeback else "1'b0"
        bindings.append(f'''function automatic bit exclusive_request(input core_request_t request);
    return request.cacheOperation != 0 || ({coherent or "1'b0"}) || request.write || request.atomic || (request.size > 3 && !(request.size == 6 &&
      (request.fetch ? {int(parameters.get('enableBurstRefill', False))} : {int(parameters.get('dCacheRefillBytes') == 64)}))) || {devices};
  endfunction''')
        names = re.findall(r'\bDitDahA1Core\s+(\w+)\s*\(', (rtl / 'DitDahA1.sv').read_text())
        assert names == [f'core_{h}' for h in range(harts)], names
        for hart, name in enumerate(names):
            core = f'dut.{name}'
            bindings.append(f'assign multiply_busy[{hart}] = {core}.backend.multiply.busy;')
            for kind, port in enumerate(('instruction', 'data')):
                index = 2 * hart + kind
                physical = f'dut.fabric.{port}_{hart}'
                for channel in ('request', 'response'):
                    for field in ('valid', 'ready'):
                        bindings.append(f'assign {channel}_{field}[{index}] = {physical}_{channel}_{field};')
                    for field in (('cacheOperation', 'address', 'data', 'size', 'mask', 'tag', 'write', 'fetch', 'atomic', 'atomicOperation', 'scEligible', 'privileged', 'refillSize') if channel == 'request' else ('data', 'fault', 'tag', 'last')):
                        bindings.append(f'assign {channel}s[{index}].{field} = {physical}_{channel}_bits_{field};')
            if interrupts:
                ports += [f'.interrupts_{hart}_{name}(irq_by_hart[{hart}][{index}]),'
                          for index, name in enumerate(('software', 'timer', 'external'))]
                bindings += [f'assign effective_irq[{hart}][{index}] = {core}.interrupts_{name};'
                             for index, name in enumerate(('software', 'timer', 'external'))]
        if local_base is not None:
            ports.append('.timeTick(local_tick),')
            instances = re.findall(r'\bDitDahA1LocalInterrupts\s+(\w+)\s*\(', (rtl / 'DitDahA1MemoryFabric.sv').read_text())
            assert len(instances) == 1, 'Missing local interrupt instance'
            device = f'dut.fabric.{instances[0]}'
            external = '{' + ', '.join(f'irq_by_hart[{h}]' for h in reversed(range(harts))) + '}'
            effective = '{' + ', '.join(f'effective_irq[{h}]' for h in reversed(range(harts))) + '}'
            sleeping = '{' + ', '.join(f'dut.core_{h}.status_sleep' for h in reversed(range(harts))) + '}'
            prefix = '$write("HART %0d ", bus_owner / 2);' if harts > 1 else ''
            platform.append(f'''  task observe_platform;
    $display("CYCLE %0d %01h %h %h %h", cycles, local_tick, {external}, {effective}, {sleeping});
    if ({device}.memory_request_valid && {device}.memory_request_ready) begin
      {prefix}
      $display("LOCAL_REQUEST %s %016h %0d %016h %02h",
        {device}.memory_request_bits_atomic ? "atomic" : ({device}.memory_request_bits_fetch ? "fetch" : ({device}.memory_request_bits_write ? "write" : "read")),
        {device}.memory_request_bits_address, 1 << {device}.memory_request_bits_size,
        {device}.memory_request_bits_write ? {device}.memory_request_bits_data & access_mask({device}.memory_request_bits_size) : 64'b0,
        {device}.memory_request_bits_tag);
    end
    if ({device}.memory_response_valid && {device}.memory_response_ready) begin
      {prefix}
      $display("LOCAL_RESPONSE %016h %01h %02h", {device}.memory_response_bits_data,
        {device}.memory_response_bits_fault, {device}.memory_response_bits_tag);
    end
  endtask''')
    result_sources = []
    if top == 'core_tb' and software and writeback:
        for hart in range(harts):
            cache = f'dut.data_cache_{hart}'
            result_sources.append(f'''
    if ({cache}.dirtyLines[index] && 64'({cache}.dataTags_ext.Memory[index]) == (address >> 13)) begin
      if (dirty_owner) $fatal(1, "Duplicate dirty result line owner");
      dirty_owner = 1;
      if ({cache}.valid[sector])
        for (integer byte_index = 0; byte_index < 8; byte_index++)
          if ({cache}.dataDirty_ext.Memory[sector][byte_index])
            coherent_result[byte_index*8 +: 8] = {cache}.data_ext.Memory[sector][byte_index*8 +: 8];
    end''')
    bindings.append(f'''  localparam bit WRITEBACK_RESULTS = {int(bool(result_sources))};
  function automatic logic [63:0] coherent_result(input logic [63:0] address, physical_data);
    logic [9:0] sector;
    logic [6:0] index;
    bit dirty_owner;
    sector = address[12:3]; index = address[12:6]; dirty_owner = 0;
    coherent_result = physical_data;
{''.join(result_sources)}
  endfunction''')
    (directory / 'core_bindings.svh').write_text('\n'.join(bindings) + '\n')
    (directory / 'core_ports.svh').write_text('\n'.join(ports) + '\n')
    (directory / 'platform_observers.svh').write_text('\n'.join(platform) + '\n')
    if interrupts and top == 'memory_tb':
        extra_files = [*extra_files, Path('test/core_tb.sv').resolve()]
    command = ['verilator', '--binary', '--timing', '--assert', '-j', '2', '--top-module', top,
         '-Wno-TIMESCALEMOD', '-Wno-WIDTHTRUNC', '-Wno-WIDTHEXPAND',
         f'-DAXI_BITS={width}', f'-DPA_BITS={pa}', f'-DHARTS={harts}',
         f'-DFABRIC_READ_SLOTS={parameters.get("fabricReadSlots") or (2 if harts > 1 else 0)}',
         f'-DLOAD_QUEUE_ENTRIES={parameters.get("loadQueueEntries", 1)}',
         '-I' + str(directory.resolve()), *(['-DENABLE_INTERRUPTS'] if interrupts else []), '-I' + str(rtl.resolve()),
         *(['-DICACHE'] if parameters['iCacheBytes'] else []),
         *(['-DLOCAL_INTERRUPTS'] if local_base is not None else []),
         *(['-DSOFTWARE'] if software else []),
         *([f'-DMEMORY_BYTES={software["memoryBytes"]}', f'-DTIME_TICK_CYCLES={software["timeTickCycles"]}'] if software else []),
         '--Mdir', str((directory / 'obj').resolve()), *files, *extra_files, source]
    binary, stamp = (directory / 'obj' / ('V' + top)).resolve(), directory / 'compile-inputs.json'
    inputs = [*files, *extra_files, source, rtl / 'filelist.f', rtl / 'ditdah_a1_config.json', *directory.glob('*.svh')]
    hashes = {str(path): hashlib.sha256(Path(path).read_bytes()).hexdigest() for path in inputs}
    tools = {name: subprocess.check_output([name, '--version'], text=True).splitlines()[0]
             for name in ('verilator', os.environ.get('CXX', 'g++'), 'make')}
    identity = dict(command=list(map(str, command)), inputs=hashes, tools=tools,
                    environment=hashlib.sha256(json.dumps(dict(os.environ), sort_keys=True).encode()).hexdigest())
    if stamp.exists() and binary.exists():
        previous = json.loads(stamp.read_text())
        if previous.get('inputs') == identity and previous.get('binaryHash') == hashlib.sha256(binary.read_bytes()).hexdigest():
            return binary
    stamp.unlink(missing_ok=True)
    run(command, directory / 'compile.log')
    assert all(hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest for path, digest in hashes.items()), 'Inputs changed during compilation'
    stamp.write_text(json.dumps(dict(inputs=identity, binaryHash=hashlib.sha256(binary.read_bytes()).hexdigest()), indent=2) + '\n')
    return binary


def log_lines(source):
    if isinstance(source, Path):
        with source.open() as stream:
            yield from (line.rstrip('\n') for line in stream)
    else:
        yield from source


def event_fields(line):
    fields = line.split()
    for prefix in ('HART', 'SOURCE', 'TAG'):
        if fields[:1] == [prefix]:
            fields = fields[2:]
    return fields


def performance_metrics(lines, config):
    harts, width = config.get('hartCount', 1), config.get('issueWidth', 1)
    samples, histograms, retired, traps = {}, {}, Counter(), Counter()
    elapsed, refill_wait, refill_stall = None, {}, {}
    read_occupancy, read_stalls = {}, None
    for line in log_lines(lines):
        fields, hart = line.split(), 0
        if fields[:1] == ['HART']:
            hart, fields = int(fields[1]), fields[2:]
        if fields[:1] == ['TRACE']:
            (traps if int(fields[8], 16) else retired)[hart] += 1
        elif fields[:1] == ['CYCLES']:
            assert elapsed is None, 'Duplicate hardware cycle count'
            elapsed = int(fields[1])
        elif fields[:1] == ['METRICS']:
            hart, *values = map(int, fields[1:])
            assert hart not in samples and len(values) == 4, 'Duplicate or malformed pipeline metrics'
            samples[hart] = values
        elif fields[:1] == ['METRIC_WIDTH']:
            hart, lanes, issued, completed = map(int, fields[1:])
            assert (hart, lanes) not in histograms, 'Duplicate pipeline histogram'
            histograms[hart, lanes] = issued, completed
        elif fields[:1] == ['REFILL_WAIT']:
            hart, cycles = map(int, fields[1:])
            assert hart not in refill_wait and cycles >= 0, 'Invalid refill wait sample'
            refill_wait[hart] = cycles
        elif fields[:1] == ['REFILL_STALL']:
            hart, *counts = map(int, fields[1:])
            assert hart not in refill_stall and len(counts) == 4 and min(counts) >= 0, 'Invalid refill stall classification'
            refill_stall[hart] = counts
        elif fields[:1] == ['READ_OCCUPANCY']:
            occupied, count = map(int, fields[1:])
            assert occupied not in read_occupancy and count >= 0, 'Invalid read occupancy sample'
            read_occupancy[occupied] = count
        elif fields[:1] == ['READ_STALL']:
            assert read_stalls is None and len(fields) == 3, 'Invalid read stall sample'
            read_stalls = list(map(int, fields[1:]))
    assert set(samples) == set(range(harts)), 'Missing per-hart pipeline metrics'
    assert set(refill_wait) == (set(range(harts)) if config.get('dCacheBytes') and config.get('dCacheRefillBytes', 8) == 64 else set()), 'Missing or unexpected data line wait samples'
    assert set(refill_stall) == set(refill_wait) and all(sum(v) == refill_wait[h] for h, v in refill_stall.items()), 'Refill wait classification does not partition total wait'
    assert set(histograms) == {(hart, lanes) for hart in range(harts) for lanes in range(width + 1)}, 'Missing pipeline histogram'
    cycles = samples[0][0]
    assert elapsed is not None and cycles == elapsed + 1 and cycles > 0, 'Hardware cycles were not sampled exactly once'
    if config.get('fabricReadSlots') or harts > 1:
        assert set(read_occupancy) == set(range((config.get('fabricReadSlots') or 2) + 1)) and sum(read_occupancy.values()) == cycles, 'Read occupancy cycle mismatch'
        assert read_stalls is not None and all(0 <= n <= cycles for n in read_stalls), 'Invalid read stall cycles'
    else:
        assert not read_occupancy and read_stalls is None, 'Serial bridge has no shared read queue'
    reports = []
    for hart, (sampled, stalls, occupancy, peak) in sorted(samples.items()):
        issued, completed = (list(values) for values in zip(*(histograms[hart, lanes] for lanes in range(width + 1))))
        assert sampled == cycles and sum(issued) == sum(completed) == cycles, 'Pipeline histogram cycle mismatch'
        assert sum(lanes * count for lanes, count in enumerate(completed)) == retired[hart], 'Retirement metrics include traps or omit instructions'
        assert 0 <= stalls <= cycles and 0 <= occupancy <= cycles * peak and 0 <= peak <= (5 + config.get('loadQueueEntries', 1)) * width, 'Invalid occupancy or stall metrics'
        assert all(value >= 0 for value in (*issued, *completed)), 'Negative pipeline histogram'
        reports.append(dict(hart=hart, retiredInstructions=retired[hart], trapEvents=traps[hart],
                            dataLineWaitCycles=refill_wait.get(hart, 0),
                            dataLineWait=dict(zip(('serialization', 'owner', 'capacity', 'arbitration'), refill_stall.get(hart, (0, 0, 0, 0)))),
                            issueCycles=issued, retireCycles=completed, dependencyStallCycles=stalls,
                            occupancySum=occupancy, maxOccupancy=peak))
    return dict(sampledCycles=cycles, retiredInstructions=sum(retired.values()),
                instructionsPerCycle=sum(retired.values()) / cycles, harts=reports,
                readOccupancy=read_occupancy, readStallCycles=read_stalls)


def control_offset(instruction):
    if instruction & 127 == 0x6f:
        value = ((instruction >> 31) << 20) | (((instruction >> 12) & 255) << 12) | (((instruction >> 20) & 1) << 11) | (((instruction >> 21) & 1023) << 1)
        return value - (1 << 21) if value & (1 << 20) else value
    if instruction & 127 == 0x63 and (instruction >> 12) & 7 in (0, 1, 4, 5, 6, 7):
        value = ((instruction >> 31) << 12) | (((instruction >> 7) & 1) << 11) | (((instruction >> 25) & 63) << 5) | (((instruction >> 8) & 15) << 1)
        return value - (1 << 13) if value & (1 << 12) else value
    return None


def prediction_target(config, table, pc, instruction):
    if not config.get('enableBranchPrediction'):
        return None
    entries = config.get('branchPredictorEntries', 0)
    row = table.get((pc >> 2) % entries) if entries else None
    hit = row is not None and row[0] == pc >> 2
    offset = control_offset(instruction)
    if offset is not None:
        taken = instruction & 127 == 0x6f or (row[3] >= 2 if hit and row[1] else offset < 0)
        return (pc + offset) & MASK if taken else None
    if instruction & 0x707f == 0x67 and hit and not row[1]:
        return row[2]
    return None


def retirement_group(fields, width):
    order = int(fields[1], 16)
    lane, count = map(int, fields[3:]) if len(fields) == 5 else (0, 1)
    assert 0 <= lane < count <= width, 'Invalid retirement group'
    return order - lane, order - lane + count, lane


def defer_interrupt(record, group, previous, owned, maximum=1):
    assert group and group[0] <= record[0] < group[1], 'Missing pending-memory retirement group'
    if previous is None:
        assert owned and group[2] == 0, 'Interrupt deferred without its memory owner'
        return group[1], 1, record[2] & 127 == 3
    end, owners, ordinary = previous
    if group[1] != end:
        assert owned and group[2] == 0 and group[0] == end and owners < maximum and ordinary and record[2] & 127 == 3, 'Interrupt deferred beyond accepted read groups'
        return group[1], owners + 1, True
    instruction = record[2]
    assert not owned and record[0] < end, 'Interrupt deferred beyond its memory group'
    assert instruction & 127 in (0x13, 0x17, 0x1b, 0x33, 0x37, 0x3b) and not (instruction & 127 in (0x33, 0x3b) and instruction >> 25 == 1), 'Non-ALU follower deferred an interrupt'
    return previous


def fetch_checker(config, faults, local_faults, architectural=None, buffered=()):
    if architectural is None:
        entries = []
        while entry := (yield):
            entries.append(entry)
            if entry[1][0] == 'ARCH_REQUEST':
                break
        if entry is None:
            entries.append(None)
        return (yield from fetch_checker(config, faults, local_faults, entry is not None, iter(entries)))
    def allowed(address, size=4):
        return address % size == 0 and address + size <= 1 << config['physicalAddressBits'] and any(
            int(region['base']) <= address and address + size <= int(region['base']) + int(region['size'])
            and region['executable'] and (size != 64 or not region['device']) for region in config['memoryRegions'])

    pending, requests, demand, physical_demand = None, {}, None, None
    arch_accepted, arch_completed, arch_wraps = 0, 0, 0
    previous_tag = None
    fetched, failed = Counter(), Counter()
    physical_fetched, physical_failed, bus_failed = Counter(), Counter(), Counter()
    cancel_order, retired_order = None, -1
    epochs, retirement_tags, retirement_lanes = deque(), {}, None
    dynamic = config.get('branchPredictorEntries', 0)
    prediction_table, prediction_packets = {}, {}
    resolved_predictions, expected_recoveries, observed_recoveries = Counter(), Counter(), Counter()
    prediction_updates = prediction_clears = prediction_resolutions = 0

    def discard_outputs():
        fetched.clear()
        failed.clear()
        bus_failed.clear()
        epochs.clear()

    def consume(column, identity, tag):
        for counters in [*(epoch[1] for epoch in epochs), (fetched, failed, bus_failed)]:
            candidates = [key for key, count in counters[column].items() if count and key[:-1] == identity]
            if candidates:
                assert tag == candidates[0][-1] if tag is not None else len(candidates) == 1, 'Retirement reordered instruction fetch occurrences'
                counters[column][candidates[0]] -= 1
                if not counters[column][candidates[0]]:
                    del counters[column][candidates[0]]
                return candidates[0][-1]
        raise AssertionError('Retirement lacks an uncancelled instruction fetch occurrence')

    reachable = {int(config['resetVector'])}
    accepted, completed = 0, 0
    buffered, missing = iter(buffered), object()
    while True:
        entry = next(buffered, missing)
        if entry is missing:
            entry = yield
        if entry is None:
            break
        line, fields = entry
        if fields[:1] == ['PREDICT_CLEAR']:
            assert dynamic, 'Prediction clear without a dynamic predictor'
            prediction_table.clear()
            prediction_clears += 1
        elif fields[:1] == ['PREDICT_UPDATE']:
            assert dynamic and len(fields) == 5, 'Unexpected prediction feedback'
            pc, target, conditional, taken = (int(value, 16) for value in fields[1:])
            assert pc % 4 == target % 4 == 0 and conditional in (0, 1) and taken == (target != (pc + 4) & MASK), 'Invalid prediction feedback'
            index = (pc >> 2) % dynamic
            row = prediction_table.get(index)
            count = max(0, min(3, row[3] + (1 if taken else -1))) if row and row[:2] == (pc >> 2, conditional) else 1 + taken
            prediction_table[index] = (pc >> 2, conditional, target, count)
            prediction_updates += 1
        elif fields[:1] == ['BRANCH_RESOLVE']:
            assert dynamic and len(fields) == 7, 'Unexpected branch resolution'
            pc, tag, instruction, taken, target, actual = (int(value, 16) for value in fields[1:])
            word, predicted = prediction_packets.pop((pc, tag), (None, None))
            assert word == instruction and predicted == (target if taken else (pc + 4) & MASK), 'Resolved branch lost its predicted PC or instruction owner'
            resolved_predictions[pc, tag, instruction, actual] += 1
            if actual != predicted:
                expected_recoveries[pc, tag, actual] += 1
            prediction_resolutions += 1
        elif fields[:1] == ['RECOVERY'] and dynamic:
            _, _, pc, tag, target = (int(value, 16 if i >= 2 else 10) for i, value in enumerate(fields[1:]))
            observed_recoveries[pc, tag, target] += 1
        elif fields[:1] == ['ARCH_REQUEST']:
            address, tag = (int(value, 16) for value in fields[1:])
            assert not requests and pending is None and address in reachable, 'Unexpected architectural fetch identity or control flow'
            requests[tag] = address
            demand = address
            physical_demand = address
            arch_wraps += int(previous_tag is not None and tag < previous_tag)
            previous_tag = tag
            arch_accepted += 1
            reachable.add(address + 4)
        elif fields[:2] == ['TRANSLATE_RESPONSE', '0']:
            physical_demand = int(fields[2], 16)
        elif fields[:1] == ['ARCH_CANCEL']:
            requests.clear()
            physical_fetched.clear()
            physical_failed.clear()
            if pending is not None:
                pending[1] = True
            if len(fields) > 2 and int(fields[2], 16):
                pc, tag, target = (int(value, 16) for value in fields[3:])
                candidates = [key for key, count in fetched.items() if count and key[0] == pc and key[-1] == tag]
                assert len(candidates) == 1, 'Early recovery lacks its accepted instruction occurrence'
                instruction = candidates[0][1]
                offset = control_offset(instruction)
                valid = target == (pc + offset) & MASK if offset is not None else instruction & 0x707f == 0x67
                valid |= offset is not None and instruction & 127 == 0x63 and target == pc + 4
                assert valid and target % 4 == 0, 'Early recovery target differs from the standard instruction'
                epochs.append(((pc, tag), (fetched.copy(), failed.copy(), bus_failed.copy())))
                fetched.clear(); failed.clear(); bus_failed.clear()
                reachable.add(target)
            else:
                cancel_order = int(fields[1], 16) if len(fields) >= 2 else -1
                if cancel_order <= retired_order:
                    discard_outputs()
                    cancel_order = None
        elif fields[:1] == ['ARCH_FETCH']:
            address, fault, instruction, tag = (int(value, 16) for value in fields[1:5])
            count = int(fields[5], 16) if len(fields) > 5 else 1
            words = [instruction, *(int(value, 16) for value in fields[6:])]
            width = config.get('issueWidth', 1)
            banks = (1 if width == 1 else 2 if width == 2 else 4) if config['iCacheBytes'] else 1
            assert len(words) == banks and 1 <= count <= banks - (address // 4) % banks, 'Invalid architectural fetch suffix'
            assert not fault or count == 1, 'Fetch fault returned younger instructions'
            assert requests.pop(tag, None) == address, 'Unrequested, repeated or cancelled architectural fetch'
            if not config['iCacheBytes']:
                if not fault:
                    assert physical_fetched[address, instruction], 'Architectural fetch without matching physical response'
                    physical_fetched[address, instruction] -= 1
                elif physical_failed[address]:
                    physical_failed[address] -= 1
                    bus_failed[address, tag] += 1
            arch_completed += 1
            if fault:
                failed[address, tag] += 1
            else:
                if config.get('enableBranchPrediction'):
                    for lane in range(count):
                        target = prediction_target(config, prediction_table, address + 4 * lane, words[lane])
                        if target is not None:
                            count = lane + 1
                            reachable.add(target)
                            break
                for lane in range(count):
                    fetched[address + 4 * lane, words[lane], (tag + lane) & 255] += 1
                    if dynamic:
                        pc = address + 4 * lane
                        target = prediction_target(config, prediction_table, pc, words[lane])
                        prediction_packets[pc, (tag + lane) & 255] = (words[lane], (pc + 4) & MASK if target is None else target)
            reachable.update(address + 4 * lane for lane in range(1, count + 1))
        elif fields[:2] == ['BUS', 'fetch']:
            address, size, data = int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            assert pending is None, 'Overlapping instruction transactions'
            assert size in ((4, 64) if config.get('enableBurstRefill') else (4,)) and data == 0 and allowed(address, size), f'Forbidden fetch: {line}'
            expected = demand is not None and (address & ~63 == physical_demand & ~63 if config['iCacheBytes'] else address == physical_demand)
            assert (expected if architectural else address in reachable), f'Fetch outside current instruction demand: {line}'
            reachable.add(address + 4)
            pending = [address, architectural and not requests, demand, size // 4, size]
            accepted += 1
        elif fields[:1] == ['FETCH']:
            address, response, instruction = (int(value, 16) for value in fields[1:])
            assert pending is not None and pending[0] == address, f'Unrequested fetch response: {line}'
            beat_bytes = (config.get('fetchBeatBytes', config['axiDataBits'] // 8) if pending[4] == 64 else 4)
            beat_base = address & -beat_bytes
            expected_fault = beat_base <= faults.get('fetch', -1) < beat_base + beat_bytes
            assert response == (2 if expected_fault else 0), f'Fetch response: {line}'
            if not architectural:
                (failed if response else fetched)[(address, None) if response else (address, instruction, None)] += 1
            elif not pending[1]:
                virtual = pending[2] if config.get('virtualAddressBits') == 39 else address
                (physical_failed if response else physical_fetched)[virtual if response else (virtual, instruction)] += 1
            pending[3] -= 1
            pending[0] += 4
            if not pending[3]:
                pending = None
                completed += 1
        elif fields[:1] == ['FETCH_RETIRE']:
            order, tag = (int(value, 16) for value in fields[1:3])
            assert len(fields) == 5 or not config.get('requireFetchIdentity', True) or config.get('issueWidth', 1) == 1, 'Missing retirement group identity'
            begin, end, lane = retirement_group(fields, config.get('issueWidth', 1))
            assert retirement_lanes == (begin, end, lane) if lane else retirement_lanes is None, 'Noncontiguous retirement group'
            retirement_lanes = (begin, end, lane + 1) if begin + lane + 1 < end else None
            assert order not in retirement_tags, 'Repeated fetch retirement identity'
            retirement_tags[order] = tag, (begin, end, lane)
        elif fields[:1] == ['TRACE']:
            trace = tuple(int(value, 16) for value in fields[1:])
            pc, instruction, trap, cause = trace[1], trace[2], trace[7], trace[8]
            reachable.add(trace[3])
            assert not config.get('requireFetchIdentity', True) or trace[0] in retirement_tags, 'Missing accepted fetch identity at retirement'
            tag, group = retirement_tags.pop(trace[0], (None, None))
            assert not trap or group is None or group[1] - group[0] == 1 and group[2] == 0, 'Fault retirement included younger lanes'
            if trap and cause >> 63:
                pass
            elif trap and cause in (1, 12):
                if architectural or (trace[0] not in local_faults and allowed(pc)):
                    tag = consume(1, (pc,), tag)
                if cause == 1 and architectural and not config['iCacheBytes'] and trace[0] not in local_faults and allowed(pc):
                    consume(2, (pc,), tag)
            else:
                tag = consume(0, (pc, instruction), tag)
            if dynamic and not trap and instruction & 127 in (0x63, 0x67, 0x6f):
                assert resolved_predictions[pc, tag, instruction, trace[3]], 'Retired control lacks its matching resolution'
                resolved_predictions[pc, tag, instruction, trace[3]] -= 1
            if epochs and epochs[0][0] == (pc, tag):
                epochs.popleft()
            retired_order = trace[0]
            if cancel_order == retired_order:
                discard_outputs()
                cancel_order = None
    assert not retirement_tags and retirement_lanes is None, 'Fetch retirement identity lacks its architectural trace'
    assert not dynamic or observed_recoveries == expected_recoveries, 'Recovery differs from the accepted predicted PCs'
    return dict(accepted=accepted, completed=completed, architecturalAccepted=arch_accepted,
                architecturalCompleted=arch_completed, architecturalTagWraps=arch_wraps,
                discarded=sum(fetched.values()) + sum(failed.values()) + sum(sum(counter.values()) for _, counters in epochs for counter in counters[:2]),
                **(dict(prediction=dict(updates=prediction_updates, clears=prediction_clears, resolutions=prediction_resolutions,
                                       recoveries=sum(observed_recoveries.values()))) if dynamic else {}))


def check_fetches(lines, config, faults, local_faults=()):
    checker = fetch_checker(config, faults, local_faults)
    next(checker)
    for line in lines:
        checker.send((line, line.split()))
    try:
        checker.send(None)
    except StopIteration as result:
        return result.value


def check_fetch_oracle():
    config, word = dict(configuration(64), requireFetchIdentity=False), 0x0400006f
    request = 'ARCH_REQUEST 0 0'
    physical = ['BUS fetch 0 4 0', f'FETCH 0 0 {word:x}']
    output = f'ARCH_FETCH 0 0 {word:x} 0'
    trace = f'TRACE 0 0 {word:x} 40 0 0 0 0 0 0'
    valid = [request, *physical, output, trace]
    check_fetches(valid, config, {})
    local = [request, 'ARCH_FETCH 0 1 0 0', 'TRACE 0 0 0 0 0 0 0 1 1 0']
    check_fetches(local, config, {}, local_faults=(0,))
    fault = [request, 'BUS fetch 0 4 0', 'FETCH 0 2 0', 'ARCH_FETCH 0 1 0 0']
    fault_trace = 'TRACE 0 0 0 0 0 0 0 1 1 0'
    for ending in (['ARCH_CANCEL 0', fault_trace], [fault_trace, 'ARCH_CANCEL 0']):
        check_fetches([*fault, *ending], config, {'fetch': 0})
    rejected = {
        'missingPhysicalResponse': [request, output, trace],
        'unrelatedLine': [*valid, 'ARCH_REQUEST 40 1', *physical],
        'cancelledOutput': [request, *physical, 'ARCH_CANCEL', output],
        'missingFaultResponse': local,
        'cancelledFaultCredit': [*fault, 'ARCH_CANCEL 0', 'TRACE 0 0 0 0 0 0 0 1 800000000000000b 0',
                                 'ARCH_REQUEST 0 1', 'ARCH_FETCH 0 1 0 1', 'TRACE 1 0 0 0 0 0 0 1 1 0'],
    }
    def fetched(pc, tag, instruction):
        return [f'ARCH_REQUEST {pc:x} {tag:x}', f'BUS fetch {pc:x} 4 0', f'FETCH {pc:x} 0 {instruction:x}',
                f'ARCH_FETCH {pc:x} 0 {instruction:x} {tag:x}']
    repeated = [*fetched(0, 0, 0x13), *fetched(4, 1, 0x6f), *fetched(8, 2, 0x13),
                'ARCH_CANCEL 0 1 4 1 4', *fetched(4, 3, 0x6f), 'ARCH_CANCEL 0 1 4 3 4',
                *fetched(4, 4, 0x6f), 'FETCH_RETIRE 0 0', 'TRACE 0 0 13 4 0 0 0 0 0 0',
                'FETCH_RETIRE 1 1', 'TRACE 1 4 6f 4 0 0 0 0 0 0',
                'FETCH_RETIRE 2 3', 'TRACE 2 4 6f 4 0 0 0 0 0 0']
    check_fetches(repeated, dict(config, requireFetchIdentity=True), {})
    predicted = [request, *physical, output, *fetched(0x40, 1, 0x13), 'FETCH_RETIRE 0 0', trace,
                 'FETCH_RETIRE 1 1', 'TRACE 1 40 13 44 0 0 0 0 0 0']
    check_fetches(predicted, dict(config, enableBranchPrediction=True), {})
    wrapped = [*fetched(0, 0, 0x6f), *fetched(0, 1, 0x6f)]
    for order in range(260):
        wrapped += [f'FETCH_RETIRE {order:x} {order & 255:x}', f'TRACE {order:x} 0 6f 0 0 0 0 0 0 0',
                    *fetched(0, (order + 2) & 255, 0x6f)]
    check_fetches(wrapped, dict(config, enableBranchPrediction=True, requireFetchIdentity=True), {})
    rejected['unpredictedTarget'] = predicted
    rejected['missingRetirementIdentity'] = [line for line in repeated if line != 'FETCH_RETIRE 1 1']
    rejected['faultFollowers'] = [*fault, 'FETCH_RETIRE 0 0 0 2', fault_trace]
    for label, before, after in (
            ('earlyTarget', 'ARCH_CANCEL 0 1 4 1 4', 'ARCH_CANCEL 0 1 4 1 c'),
            ('earlyIdentity', 'ARCH_CANCEL 0 1 4 1 4', 'ARCH_CANCEL 0 1 4 3 4'),
            ('reorderedOccurrence', 'FETCH_RETIRE 1 1', 'FETCH_RETIRE 1 3'),
            ('killedOccurrence', 'FETCH_RETIRE 2 3', 'FETCH_RETIRE 2 2')):
        rejected[label] = [after if line == before else line for line in repeated]
    for name, lines in rejected.items():
        profiles = ((dict(config, issueWidth=2, requireFetchIdentity=True),) if name == 'faultFollowers' else
                    (dict(config, requireFetchIdentity=True),) if name == 'missingRetirementIdentity' else
                    (config, dict(config, iCacheBytes=8192)) if name in ('unrelatedLine', 'cancelledOutput') else (config,))
        for profile in profiles:
            try:
                check_fetches(lines, profile, {'fetch': 0} if name in ('cancelledFaultCredit', 'faultFollowers') else {})
            except AssertionError as error:
                assert name != 'faultFollowers' or str(error) == 'Fault retirement included younger lanes'
                continue
            raise AssertionError(f'Fetch oracle accepted {name}')
    recovery = SimpleNamespace(stop=16, pipeline_recovery={0: [8], 8: [16]},
                               recovery_counts={0: (1, 1), 8: (1, 0)})
    records = ['RECOVERY 0 1 0 0 8', 'FETCH_RETIRE 0 0 0 1', 'TRACE 0 0 463 8 0 0 0 0 0 0',
               'FETCH_RETIRE 1 1 0 1', 'TRACE 1 8 80006f 10 0 0 0 0 0 0']
    predicted_config = dict(config, iCacheBytes=8192, enableBranchPrediction=True)
    check_pipeline_events(records, predicted_config, recovery)
    try:
        check_pipeline_events(['RECOVERY 0 1 8 1 10', *records], predicted_config, recovery)
    except AssertionError as error:
        assert str(error) == 'Recovery counts differ from the configured prediction policy'
    else:
        raise AssertionError('Pipeline oracle accepted disabled prediction')
    return [*rejected, 'disabledPrediction']


def check_burst_guards(lines, config, program, name):
    guards = []
    beat = next(index for index, line in enumerate(lines) if event_fields(line)[:1] == ['LINE_BEAT'])
    response = next(index for index in range(beat + 1, len(lines)) if event_fields(lines[index])[:1] == ['RESPONSE'])
    mutations = [('beatData', beat, 3, 1), ('beatOrder', beat, 1, 8),
                 ('beatLast', beat, 4, 1), ('chunkLast', response, 5, 1), ('chunkTag', response, 4, 1)]
    certificate = next((index for index, line in enumerate(lines[:beat]) if event_fields(line)[:2] == ['ARCH_DATA_REQUEST', 'read'] and line.split()[-1] == '6'), None)
    if certificate is not None:
        mutations.append(('refillSpan', certificate, 7, 5))
    invalidation = next((index for index, line in enumerate(lines) if line.startswith('INVALIDATE ')), None)
    if invalidation is not None:
        mutations += [('invalidationAddress', invalidation, 2, 64),
                      ('invalidationRecipient', invalidation, 1, config['hartCount']),
                      ('duplicateInvalidation', invalidation, None, 2)]
        if not config.get('dCacheWriteback'):
            mutations.append(('missingInvalidation', invalidation, None, 0))
    return check_event_guards(lines, config, program, name, mutations)


def check_event_guards(lines, config, program, name, mutations):
    software = hasattr(program, 'software')
    check_multicore(lines, config, program, name, atomic_metadata=True, software_output=software)
    guards = []
    for label, index, field, mask in mutations:
        changed = list(lines)
        if field is None:
            changed[index:index + 1] = [changed[index]] * mask
        else:
            fields = changed[index].split()
            offset = len(fields) - len(event_fields(changed[index]))
            decimal = label == 'invalidationRecipient'
            value = int(fields[offset + field], 10 if decimal else 16) ^ mask
            fields[offset + field] = str(value) if decimal else f'{value:x}'
            changed[index] = ' '.join(fields)
        try:
            check_multicore(changed, config, program, name, atomic_metadata=True, software_output=software)
        except AssertionError:
            guards.append(label)
            continue
        raise AssertionError(f'Event oracle accepted {label}')
    return guards


def check_writeback_guards(lines, config, program, name):
    events = [' '.join(event_fields(line)) for line in lines]
    mutations = []
    for event, label, field, mask in (
            ('CACHE_STORE', 'cachedStoreData', 2, 1), ('CACHE_STORE', 'cachedStoreTag', 3, 1),
            ('CACHE_STORE', 'missingCachedStore', None, 0),
            ('WRITEBACK_REQUEST', 'writebackData', 2, None),
            ('WRITEBACK_REQUEST', 'writebackPrivilege', 5, 1),
            ('WRITEBACK_RESPONSE', 'writebackTag', 2, 1),
            ('WRITEBACK_RESPONSE', 'missingWritebackReply', None, 0),
            ('RESULT', 'coherentResult', 2, 1), ('PHYSICAL_RESULT', 'physicalResult', 2, 1),
            ('BUS writeback', 'writebackStrobes', 5, 1)):
        index = next((i for i, line in enumerate(events) if line.startswith(event + ' ')), None)
        if index is None:
            continue
        if mask is None:
            dirty = int(events[index].split()[3], 16)
            mask = 1 << (8 * ((dirty & -dirty).bit_length() - 1))
        mutations.append((label, index, field, mask))
    return check_event_guards(lines, config, program, name, mutations)


def check_access_privileges(lines, modes, requests, privileges, required):
    expected = iter(privilege != 0 for request, privilege in zip(requests, privileges) if request[0] != 'fetch')
    mode, demand, retired, pending = 3, 3, 0, None
    for line in lines:
        fields = line.split()
        if fields[:1] == ['ARCH_REQUEST']:
            demand = mode
        elif fields[:1] == ['REQUEST']:
            assert pending is None or not required, 'Missing accepted access privilege'
            pending = demand != 0 if fields[1] == 'fetch' else next(expected)
        elif fields[:1] == ['ACCESS_PRIVILEGE']:
            assert pending is not None and int(fields[1], 16) == pending, 'Accepted access privilege differs from architectural context'
            pending = None
        elif fields[:1] == ['TRACE']:
            retired += 1
            mode = modes[retired]
    assert pending is None or not required, 'Missing final accepted access privilege'
    assert not required or next(expected, None) is None, 'Missing architectural data request privilege'


def translation_maintenance(trace):
    instruction = trace[2]
    funct3, address = (instruction >> 12) & 7, instruction >> 20
    write = instruction & 127 == 0x73 and funct3 in (1, 2, 3, 5, 6, 7) and (funct3 & 3 == 1 or (instruction >> 15) & 31)
    return not trace[7] and (instruction & 0xfe007fff == 0x12000073 or write and
        (address == 0x180 or 0x3a0 <= address <= 0x3ae or 0x3b0 <= address <= 0x3ef))


def permitted_table_read(config, model, address):
    return address % 8 == 0 and 0 <= address <= (1 << config['physicalAddressBits']) - 8 and any(
        int(region['base']) <= address and address + 8 <= int(region['base']) + int(region['size']) and
        region['readable'] and not region['device'] for region in config['memoryRegions']) and pmp_allowed(
        [model.pmp_config(i) for i in range(config['pmpEntries'])],
        [model.csrs[0x3b0+i] for i in range(config['pmpEntries'])], address, 8, 'read', config['physicalAddressBits'], 1)


def check_translation_result(walk, result, config, model, history):
    def read_pte(address, reads):
        entry = next(reads, None)
        if entry is None:
            if walk.get('cancelled') or result is None:
                raise StopIteration
            assert not permitted_table_read(config, model, address), 'Permitted PTE omitted physical service'
            raise Fault(5, address)
        assert entry[0] == address, 'PTE address differs from independent walk'
        if entry[2]:
            raise Fault(5, address)
        return entry[1]
    paged = walk['privilege'] != 3 and walk['satp'] >> 60 == 8
    cached = [reads for satp, vpn, bits, reads in walk.get('acceptedHistory', history) if satp == walk['satp'] and walk['address'] >> bits == vpn]
    candidates = [walk['reads']] if walk['reads'] or not paged else cached or [[]]
    matches = bool(walk.get('cancelled'))
    for candidate in candidates:
        reads = iter(candidate)
        expected, fault, cause = walk['address'], False, 0
        try:
            expected = sv39_walk(walk['address'], walk['kind'], walk['privilege'], walk['satp'], walk['status'], lambda address: read_pte(address, reads))
        except StopIteration:
            continue
        except Fault as error:
            fault, cause = True, error.cause
        matches |= result == (expected, fault, cause) and next(reads, None) is None
        if config.get('tlbEntries') and paged and walk['reads'] and not fault and not (walk.get('stale') or walk.get('cancelled')):
            bits = 12 + 9 * (3 - len(walk['reads']))
            entry = walk['satp'], walk['address'] >> bits, bits, tuple(walk['reads'])
            if entry not in history:
                history.append(entry)
    assert result is None or matches, 'Translation result lacks a matching walk or authorized cached leaf'
    return paged and not walk['reads'] and bool(cached)


def check_core_translations(lines, config, program, expected_requests):
    model, walks, request, architectural = Model(config, program.memory, program.faults), [None, None], None, []
    walker = None
    history = []
    for line in lines:
        fields = line.split()
        if fields[:1] == ['TRANSLATE_REQUEST']:
            port, address, privilege, fetch, write, satp, sum_enabled, mxr = (int(value, 16) for value in fields[1:])
            assert port in (0, 1) and walks[port] is None, 'Overlapping Core translation port'
            walks[port] = dict(port=port, address=address, privilege=privilege, kind='fetch' if fetch else 'write' if write else 'read',
                        satp=satp, status=(sum_enabled << 18) | (mxr << 19), reads=[], acceptedHistory=tuple(history))
        elif fields[:1] == ['ARCH_CANCEL'] and walks[0]:
            walks[0]['cancelled'] = True
        elif fields[:1] == ['WALK_REQUEST']:
            address, tag, port = (int(value, 16) for value in fields[1:])
            assert port in (0, 1) and walks[port] and request is None and walker in (None, port), 'Unowned Core page-table request'
            assert permitted_table_read(config, model, address), 'Core page walk escaped S-mode physical protection'
            request, walker = (address, tag, port), port
        elif fields[:1] == ['WALK_RESPONSE']:
            data, fault, tag = (int(value, 16) for value in fields[1:])
            assert request and tag == request[1], 'Core page-table response identity'
            expected = sum(model.memory.get(request[0] + byte, 0) << (8 * byte) for byte in range(8))
            assert fault == (request[0] <= program.faults.get('read', -1) < request[0] + 8) and (fault or data == expected), 'Core PTE response differs from independent memory'
            walk = walks[request[2]]
            walk['reads'].append((request[0], data, bool(fault)))
            check_translation_result(walk, None, config, model, history)
            request = None
        elif fields[:1] == ['TRANSLATE_RESPONSE']:
            port, physical, fault, cause = (int(value, 16) for value in fields[1:])
            assert port in (0, 1) and walks[port] and (request is None or request[2] != port), 'Unowned Core translation response'
            walk = walks[port]
            check_translation_result(walk, (physical, fault, cause), config, model, history)
            walks[port] = None
            if walker == port:
                walker = None
        elif fields[:1] == ['ARCH_DATA_REQUEST']:
            architectural.append((fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)))
        elif fields[:1] == ['IRQ']:
            model.set_interrupts(int(fields[1], 16))
        elif fields[:1] == ['TRACE']:
            if translation_maintenance(tuple(int(v, 16) for v in fields[1:])):
                history.clear()
                for walk in walks:
                    if walk:
                        walk['stale'] = True
            (model.interrupt if int(fields[9], 16) >> 63 else model.step)()
    assert architectural == [event for event in expected_requests if event[0] != 'fetch'], 'Core LSU physical requests differ from architectural translation'


def check_pipeline_events(lines, config, program):
    groups, recoveries = {}, []
    retirement_tags = {int(fields[1], 16): int(fields[2], 16) for line in lines if (fields := line.split())[:1] == ['FETCH_RETIRE']}
    for index, line in enumerate(lines):
        fields = line.split()
        if fields[:1] == ['ISSUE_GROUP']:
            hart, cycle, pc, instruction, count = (int(value, 16 if column in (2, 3) else 10) for column, value in enumerate(fields[1:]))
            assert hart == 0 and 0 < count <= config['issueWidth']
            assert instruction == sum(program.memory.get(pc + byte, 0) << (8 * byte) for byte in range(4)), 'Issue group head differs from instruction memory'
            groups.setdefault(pc, []).append(count)
        elif fields[:1] == ['RECOVERY']:
            hart, cycle, pc, tag, target = (int(value, 16 if column >= 2 else 10) for column, value in enumerate(fields[1:]))
            if hasattr(program, 'pipeline_recovery'):
                targets = program.pipeline_recovery | {program.stop: [program.stop]}
                assert hart == 0 and pc in targets and target in targets[pc], 'Early recovery resolved the wrong branch or target'
                later = [tuple(int(value, 16) for value in record.split()[1:]) for record in lines[index + 1:] if record.startswith('TRACE ')]
                assert any(record[1] == pc and retirement_tags[record[0]] == tag and not record[7] or record[1] == getattr(program, 'recovery_fault_pc', None) and record[7] and record[8] == 5 for record in later), 'Recovery preceded neither its branch occurrence retirement nor its older memory fault'
                if pc != program.stop:
                    recoveries.append(pc)
        elif fields[:1] == ['RETIRE_REDIRECT'] and hasattr(program, 'pipeline_recovery'):
            hart, pc, trap = (int(value, 16) for value in fields[1:])
            assert hart == 0 and (trap or pc not in program.pipeline_recovery), 'Resolved branch redirected again at retirement'
    for pc, maximum in getattr(program, 'pipeline_groups', {}).items():
        assert pc in groups and max(groups[pc]) <= maximum, 'Memory group crossed a dependency'
        if config['iCacheBytes']:
            assert max(groups[pc]) == min(maximum, config['issueWidth']), 'Memory operation did not issue with independent ALU followers'
    if hasattr(program, 'pipeline_recovery') and config['iCacheBytes']:
        if not hasattr(program, 'recovery_fault_pc') or config['issueWidth'] > 1:
            assert recoveries, 'No early control recovery was observed'
    if hasattr(program, 'recovery_counts') and not config.get('branchPredictorEntries'):
        expected = Counter({pc: counts[bool(config.get('enableBranchPrediction'))] for pc, counts in program.recovery_counts.items()})
        assert Counter(recoveries) == expected, 'Recovery counts differ from the configured prediction policy'
    window = {}
    if hasattr(program, 'branch_window'):
        work = [tuple(map(int, fields[1:])) for line in lines if (fields := line.split())[:1] == ['WORK_CYCLE']]
        assert [sample[:2] for sample in work] == [(0, 0), (0, 1)] and work[1][2] > work[0][2], 'Invalid branch measurement window'
        window['workCycles'] = work[1][2] - work[0][2]
    return dict(groupWidths={str(pc): max(counts) for pc, counts in groups.items() if pc in getattr(program, 'pipeline_groups', {})},
                earlyRecoveries=len(recoveries), **window)


def compare(binary, directory, config, transport='axi', selected=()):
    base = int(config['resetVector'])
    coverage = [0] * 6
    coverage_names = (('awBeforeW', 'wBeforeAw', 'awWithW', 'arStall', 'awStall', 'wStall') if transport == 'axi'
                      else ('overlap', 'instructionStall', 'dataStall', 'responseDelay', 'permissionReject', 'architecturalTagWrap' if config['iCacheBytes'] else 'tagWrap'))
    count = 0
    reports, burst_guards = [], []
    pipeline_max, dependency_stalls = 0, 0
    for name, program in cases(base, config['pmpEntries'] != 0, config['enableInterrupts'], config.get('enableUserMode', False), local_interrupt_base(config), config.get('enableSupervisorMode', False), config.get('virtualAddressBits') == 39, config.get('dCacheWriteback', False)):
        if selected and name not in selected:
            continue
        image = directory / (name + '.hex')
        image.write_text('\n'.join(f'{program.memory.get(base + i, 0):02x}' for i in range(65536)) + '\n')
        model = Model(config, program.memory, program.faults)
        expected, expected_atomics, expected_modes = [], [], [3]
        def advance():
            first = len(model.requests)
            record = model.step()
            expected_modes.append(getattr(model, 'privilege', 3))
            if any(event[0] == 'atomic' for event in model.requests[first:]):
                expected_atomics.append((model.atomic_operation, int(model.sc_eligible)))
            return record
        for _ in range(2000):
            if hasattr(program, 'interrupts'):
                break
            record = advance()
            expected.append(record)
            if not record[7] and record[1] == program.stop:
                break
        else:
            raise AssertionError(f'{name}: reference program did not finish')
        if hasattr(program, 'translation'):
            assert all(model.registers[index] == value for index, value in program.translation.items()), 'Translation context did not select distinct physical data'
        for seed in (1, 17, 2026):
            log = directory / f'{name}-{seed}.log'
            command = [binary, f'+IMAGE={image.resolve()}', f'+BASE={base:x}',
                       f'+STOP={program.stop:x}', f'+SEED={seed}']
            command.extend(f'+FAULT_{kind.upper()}={address:x}' for kind, address in program.faults.items())
            command += [f'+{key.upper()}={getattr(program, key, 0)}' for key in ('exclusive_failures', 'interference')]
            if hasattr(program, 'data_cache') and 'work' in program.data_cache:
                command += [f'+WORK_{key.upper()}={program.data_cache["work"][key]:x}' for key in ('begin', 'end')]
            if hasattr(program, 'branch_window'):
                command += [f'+WORK_{key.upper()}={program.branch_window[key]:x}' for key in ('begin', 'end')]
            if getattr(program, 'load_window', False):
                command.append('+REORDER_READS=1')
            if name == 'load_cancel':
                command.append('+FIXED_READ_DELAY=128')
            if hasattr(program, 'pipeline_groups') or hasattr(program, 'pipeline_recovery'):
                command.append('+PIPELINE_EVENTS')
            if hasattr(program, 'interrupts'):
                command.extend(f'+IRQ_{key.upper()}={value:x}' if key == 'target' else f'+IRQ_{key.upper()}={value}'
                               for key, value in program.interrupts.items())
            run(command, log)
            raw_lines = log.read_text().splitlines()
            lines = [re.sub(r'^SOURCE \d+ (?:TAG [0-9a-f]+ )?', '', line) for line in raw_lines]
            assert 'PASS' in lines, f'{name}: simulation did not complete'
            if hasattr(program, 'interrupts'):
                model = Model(config, program.memory, program.faults)
                expected, expected_atomics, causes, deferred, expected_modes = [], [], [], None, [3]
                group, accepted_memory = None, None
                request_event = 'ARCH_DATA_REQUEST' if config.get('virtualAddressBits') == 39 or transport == 'axi' and config.get('dCacheBytes') else 'REQUEST'
                for line in lines:
                    fields = line.split()
                    if fields[:1] == ['IRQ']:
                        model.set_interrupts(int(fields[1], 16))
                    elif fields[:1] == [request_event] and fields[1] != 'fetch':
                        assert accepted_memory is None, 'Second accepted memory operation before retirement'
                        accepted_memory = fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)
                    elif fields[:1] == ['FETCH_RETIRE']:
                        group = retirement_group(fields, config['issueWidth'])
                    elif fields[:1] == ['TRACE']:
                        observed = tuple(int(v, 16) for v in fields[1:])
                        pending = model.interrupt_cause()
                        first = len(model.requests)
                        record = model.interrupt() if observed[8] >> 63 else advance()
                        owned = accepted_memory is not None and [event for event in model.requests[first:] if event[0] != 'fetch'] == [accepted_memory]
                        if owned:
                            accepted_memory = None
                        if observed[8] >> 63:
                            expected_modes.append(getattr(model, 'privilege', 3))
                        if pending and not record[8] >> 63 and not record[7]:
                            deferred = defer_interrupt(record, group, deferred, owned, config.get('loadQueueEntries', 1))
                        else:
                            deferred = None
                        if record[8] >> 63:
                            causes.append(record[8] & 63)
                        expected.append(record)
                assert accepted_memory is None, 'Accepted memory operation lacks retirement'
                wanted_causes = [bit for index, bit in ((2, 11), (0, 3), (1, 7)) if program.interrupts['mask'] & (1 << index)]
                assert causes == wanted_causes, f'{name}: interrupt delivery or priority {causes} != {wanted_causes}'
                start = next((i for i, line in enumerate(lines) if line.startswith('IRQ_START ')), None)
                assert start is not None, f'{name}: stimulus never activated'
                if program.interrupts['mode'] == 7:
                    assert any(line.startswith('TRACE ') and int(line.split()[2], 16) == program.interrupts['target']
                               and int(line.split()[8], 16) == 0 for line in lines[:start]), f'{name}: target did not retire before interrupt assertion'
            actual = [tuple(int(v, 16) for v in line.split()[1:]) for line in lines if line.startswith('TRACE ')]
            bus = [(v[1], int(v[2], 16), int(v[3]), int(v[4], 16))
                   for line in lines if line.startswith('BUS ') for v in [line.split()]]
            assert len(actual) == len(expected), f'{name}: trace length {len(actual)} != {len(expected)}'
            for index, (observed, wanted) in enumerate(zip(actual, expected)):
                assert observed == wanted, f'{name} trace {index}:\nactual {observed}\nexpected {wanted}'
            assert all(model.registers[register] == value for register, value in getattr(program, 'expected_registers', {}).items()), 'Directed program register result'
            pipeline_events = check_pipeline_events(lines, config, program) if hasattr(program, 'pipeline_groups') or hasattr(program, 'pipeline_recovery') else None
            data_bus = [event for event in bus if event[0] != 'fetch']
            expected_bus = [event for event in model.bus if event[0] != 'fetch']
            cache_report = None
            translation_report = None
            if config.get('virtualAddressBits') == 39 and transport == 'memory':
                check_core_translations(lines, config, program, model.requests)
            elif transport == 'axi' and (config.get('virtualAddressBits') == 39 or config.get('dCacheBytes') or any(event[0] == 'atomic' for event in model.requests) or config.get('enableBurstRefill') or name in ('fence_ordering', 'synchronization')):
                checked = check_multicore(raw_lines, config, program, name, atomic_metadata=True)
                if not burst_guards and any('LINE_BEAT ' in line for line in lines):
                    burst_guards = check_burst_guards(raw_lines, config, program, name)
                if config.get('enableBurstRefill') and name == 'pmp_fetch':
                    fault_trace = next(tuple(int(value, 16) for value in line.split()[1:]) for line in lines
                                       if line.startswith('TRACE ') and int(line.split()[9], 16) == 1)
                    index = next(index for index, line in enumerate(lines) if line.startswith('ARCH_REQUEST ') and int(line.split()[1], 16) == fault_trace[1])
                    tag = int(lines[index].split()[2], 16)
                    forged = [*lines[:index + 1], f'REQUEST fetch {fault_trace[1] & ~63:x} 64 0 {tag:x}', *lines[index + 1:]]
                    try:
                        check_multicore(forged, config, program, name, atomic_metadata=True)
                    except AssertionError as error:
                        assert str(error) == 'Line escaped whole-range PMP authorization', 'Protection control failed for a different reason'
                        if 'lineProtection' not in burst_guards:
                            burst_guards.append('lineProtection')
                    else:
                        raise AssertionError('Line oracle accepted an unauthorized range')
                cache_report = checked.get('dataCache')
                translation_report = checked.get('translation')
                if name == 'sv39_reuse':
                    assert translation_report['pteReads'] == (3 if config.get('tlbEntries') else 99), 'Repeated page walk count'
            else:
                assert data_bus == expected_bus, f'{name}: unexpected data accesses\nactual {data_bus}\nexpected {expected_bus}'
            if transport == 'memory':
                assert [tuple(int(value, 16) for value in line.split()[1:]) for line in lines if line.startswith('ATOMIC ')] == expected_atomics, 'Memory atomic metadata differs from independent instructions'
                requests = [(v[1], int(v[2], 16), int(v[3]), int(v[4], 16)) for line in lines
                            if line.startswith('REQUEST ') for v in [line.split()] if v[1] != 'fetch']
                if config.get('virtualAddressBits') != 39:
                    assert requests == [r for r in model.requests if r[0] != 'fetch'], f'{name}: unexpected Core requests'
            if not config.get('dCacheBytes') and config.get('virtualAddressBits') != 39 and (config.get('enableUserMode') or any(line.startswith('ACCESS_PRIVILEGE ') for line in lines)):
                check_access_privileges(lines, expected_modes, model.requests, model.request_privileges, config.get('enableUserMode', False))
            fetches = check_fetches(lines, dict(config, fetchBeatBytes=8) if transport == 'memory' else config, program.faults, model.local_fetch_faults)
            if name == 'pipeline_redirect':
                fault = program.faults['fetch']
                assert any(line.startswith(f'FETCH {fault:016x} 2 ') for line in lines), 'Wrong-path fetch fault was not exercised'
            if name == 'pipeline_reuse':
                assert fetches['architecturalTagWraps'] > 0, 'Instruction identity wraparound was not exercised'
            for line in lines:
                if line.startswith('COVER '):
                    observed_coverage = list(map(int, line.split()[1:]))
                    if transport == 'memory' and config['iCacheBytes']:
                        observed_coverage[5] = fetches['architecturalTagWraps']
                    coverage = [a + b for a, b in zip(coverage, observed_coverage)]
                elif line.startswith('PIPELINE '):
                    occupancy, stalls = map(int, line.split()[1:])
                    pipeline_max = max(pipeline_max, occupancy)
                    dependency_stalls += stalls
            count += len(actual)
            elapsed = next(int(line.split()[1]) for line in lines if line.startswith('CYCLES '))
            issue_streak, retire_streak = next(tuple(map(int, line.split()[1:])) for line in lines if line.startswith('THROUGHPUT '))
            full_width = name in ('pipeline_integer_stream', 'pipeline_dependency_stream', *(['pipeline_dependency_chain'] if config.get('issueWidth', 1) == 1 else [])) and config.get('virtualAddressBits') != 39
            full_width |= name == 'sv39_integer_stream' and bool(config.get('tlbEntries'))
            if full_width and config['iCacheBytes']:
                assert min(issue_streak, retire_streak) >= 64, f'{name}: native cached pipeline did not sustain the configured issue and retirement width'
            metric_config = config if transport == 'axi' else dict(config, fabricReadSlots=0)
            reports.append(dict(test=name, seed=seed, events=len(actual), cycles=elapsed, performance=performance_metrics(lines, metric_config),
                                busTransactions=len(bus), axiReadBeats=sum(line.startswith(('READ ', 'LINE_BEAT ')) for line in lines), fetches=fetches,
                                issueStreak=issue_streak, retireStreak=retire_streak,
                                **(dict(pipeline=pipeline_events) if pipeline_events is not None else {}),
                                **(dict(translation=translation_report) if translation_report is not None else {}),
                                **(dict(dataCache=cache_report) if cache_report is not None else {})))
        print(f'  {name}: {len(expected)} events, three bus schedules', flush=True)
    assert reports, 'No selected scalar program'
    if not selected:
        assert all(coverage), f'{transport} coverage missing: {dict(zip(coverage_names, coverage))}'
        assert pipeline_max >= 2 and dependency_stalls, f'Pipeline coverage missing: {pipeline_max}, {dependency_stalls}'
    return dict(events=count, cases=reports, lineOracleGuards=burst_guards, pipelineCoverage=dict(maxOccupancy=pipeline_max, dependencyStalls=dependency_stalls),
                **{('busCoverage' if transport == 'axi' else 'portCoverage'): dict(zip(coverage_names, coverage))})


def check_multicore(lines, config, program, name, atomic_metadata=False, software_output=False):
    harts, base = config['hartCount'], int(config['resetVector'])
    read_slots = config.get('fabricReadSlots') or (2 if harts > 1 else 0)
    covers, results, physical_results, passed = [], [], [], False
    memory, active = dict(program.memory), None
    writeback = bool(config.get('dCacheWriteback'))
    physical_memory = dict(memory) if writeback else memory
    maintenance, cached_writes = None, set()
    owners = {}
    dual = config.get('loadQueueEntries', 1) == 2
    lsu_slots, lsu_order = [{} for _ in range(harts)], [deque() for _ in range(harts)]
    recent_source = [2 * hart + 1 for hart in range(harts)]
    read_order, read_peak, read_serial, read_reordered, read_observed = {}, 0, 0, 0, None
    data_read_peak, data_read_reordered = [0] * harts, [0] * harts
    line_ids, line_peak, line_observed = set(), 0, None
    failures = getattr(program, 'exclusive_failures', 0)
    models = [Model(config, {}, program.faults, hart_id=h) for h in range(harts)]
    local_base = local_interrupt_base(config)
    device = LocalInterrupts(local_base, harts) if local_base is not None else None
    software = getattr(program, 'software', None)
    console, console_events, successful_stores = [bytearray() for _ in range(harts)], deque(), Counter()
    for model in models:
        model.memory = memory
    pending, finished = [None] * harts, set()
    architectural, cache_counts = [None] * harts, [Counter() for _ in range(harts)]
    work_samples = {}
    hit_addresses = [Counter() for _ in range(harts)]
    data_cache = bool(config.get('dCacheBytes'))
    translated = config.get('virtualAddressBits') == 39
    observed_data = data_cache or translated or dual
    implicit, walkers = [None] * harts, [None] * harts
    walks = [[None, None] for _ in range(harts)]
    translation_history = [[] for _ in range(harts)]
    translation_counts = Counter()
    fetch_privileges, retired_privileges = [3] * harts, [3] * harts
    fetch_protection = [None] * harts
    fetch_checks = [fetch_checker(config, program.faults, model.local_fetch_faults) for model in models]
    for checker in fetch_checks:
        next(checker)
    collisions, tags, sources, events, effects = set(), {}, set(), 0, Counter()
    interrupts, causes, overtaken = Counter(), Counter(), 0
    deferred, retirement_groups = [None] * harts, [None] * harts
    waiting, sleep_cycles, wake = [False] * harts, [0] * harts, [False] * harts
    wait_started, waiting_mask, wake_mask = [0] * harts, 0, 0
    interrupt_dirty, previous_external, previous_time, next_timer, expected_levels = True, None, 0, 0, 0
    concurrent = Counter()
    monitor, reservation_max, sc_results = ExclusiveMonitor(), 0, Counter()
    observed_reservations = None
    elapsed_cycles, transactions, axi_transactions, line_beats = None, 0, 0, 0

    def physical_write(address, size, value, mask=None):
        for byte in range(size):
            if mask is None or mask >> byte & 1:
                physical_memory[address + byte] = value >> (8 * byte) & 255

    def no_service(*args):
        raise AssertionError('Architectural data access without bus service')

    for model in models:
        model.external_access = no_service

    def ordinary(event):
        line = event[2] == 64 and (config.get('enableBurstRefill') if event[0] == 'fetch' else config.get('dCacheRefillBytes') == 64)
        return not (writeback and cacheable(event[1], 1)) and event[0] in ('read', 'fetch') and (event[2] <= 8 or line) and not any(
            region['device'] and int(region['base']) <= event[1] < int(region['base']) + int(region['size'])
            for region in config['memoryRegions'])

    def read_started(source):
        nonlocal read_peak, read_serial, line_peak
        assert source not in read_order, 'Repeated AXI read before terminal response'
        read_order[source] = read_serial
        read_serial += 1
        read_peak = max(read_peak, len(read_order))
        owner = owners[source]
        if owner['event'][0] == 'read' and not owner.get('walk'):
            data_read_peak[owner['hart']] = max(data_read_peak[owner['hart']], sum(
                owners[key]['hart'] == owner['hart'] and owners[key]['event'][0] == 'read' and not owners[key].get('walk') for key in read_order))
        if owners[source]['event'][2] == 64:
            line_ids.add(source)
            line_peak = max(line_peak, len(line_ids))

    def read_completed(source):
        nonlocal read_reordered
        assert source in read_order, 'Read data lacks an accepted AXI address'
        owner = owners[source]
        if owner['event'][0] == 'read' and not owner.get('walk'):
            data_read_reordered[owner['hart']] += int(any(
                owners[key]['hart'] == owner['hart'] and owners[key]['event'][0] == 'read' and not owners[key].get('walk') and order < read_order[source]
                for key, order in read_order.items()))
        read_reordered += int(read_order[source] != min(read_order.values()))
        del read_order[source]
        line_ids.discard(source)

    def service(hart, event, atomic_fault=False, local=False, read_value=None, replay=False):
        nonlocal interrupt_dirty
        if dual and event[0] == 'read' and not replay:
            _, address, size, _ = event
            if local:
                try:
                    return device.access(address, size, 'read', 0), 0
                except Fault:
                    return 0, 1
            value = sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(size)) if read_value is None else read_value
            return value, int(address <= program.faults.get('read', -1) < address + size)
        assert pending[hart] is None, 'Second memory operation before retirement'
        accesses, response = [], None

        def access(address, size, kind, data):
            nonlocal response, interrupt_dirty
            wanted = kind, address, size, data if kind in ('write', 'atomic') else 0
            assert event == wanted, f'{name}: data service {event} != independent instruction {wanted}'
            accesses.append(wanted)
            operation = models[hart].atomic_operation if kind == 'atomic' else None
            if kind == 'atomic':
                assert (operation, models[hart].sc_eligible) == (active['operation'], active['eligible']), 'Atomic operation or local reservation differs from raw instruction'
                assert not atomic_metadata or active.get('atomicMetadata'), 'Missing atomic request metadata'
                if operation == 3 and not active.get('scSuccess', False) and not atomic_fault:
                    return 1
            if local:
                try:
                    value = device.access(address, size, kind, data)
                except Fault:
                    response = (0, 1)
                    raise
                response = (value, 0)
                if kind == 'write':
                    interrupt_dirty = True
                    effects[hart, address] += 1
                    monitor.write(address, size)
                return value
            if atomic_fault or (address <= program.faults.get(kind, -1) < address + size if kind == 'read' else address == program.faults.get(kind)):
                raise Fault(5 if kind == 'read' or operation == 2 else 7, address)
            if kind == 'write':
                monitor.write(address, size)
            if software and software['console'] <= address < software['console'] + 4 * harts:
                assert kind == 'write' and size == 4 and address == software['console'] + 4 * hart, 'Console access width, direction or hart'
                assert 0 <= data < 128, 'Console requires ASCII bytes'
                console[hart].append(data)
                console_events.append((hart, data))
                return 0
            old = sum(memory.get(address + byte, 0) << (byte * 8) for byte in range(size))
            if kind == 'read':
                if read_value is not None:
                    old = read_value
                response = (old, 0)
            if kind == 'write' or (kind == 'atomic' and operation != 2):
                value = atomic_value(operation, old, data, size) if kind == 'atomic' and operation != 3 else data
                for byte in range(size):
                    memory[address + byte] = (value >> (byte * 8)) & 255
                effects[hart, address] += 1
                if software and address == software['results'] + 8 * hart and size == 8 and data == 1:
                    successful_stores[hart] += 1
            return 0 if kind == 'write' or operation == 3 else old

        models[hart].external_access = access
        pending[hart] = models[hart].step()
        models[hart].external_access = no_service
        assert len(accesses) == 1, 'Bus service did not match an architectural access'
        return response

    def complete_data(hart):
        access = architectural[hart]
        if 'lineValue' in access and 'response' in access:
            access['expected'] = service(hart, access['event'], read_value=access.pop('lineValue'))
            cache_counts[hart]['expandedReads'] += 1
        if 'expected' not in access or 'response' not in access:
            return
        data, fault, tag = access['response']
        expected, expected_fault = access['expected']
        assert tag == access['tag'] and fault == expected_fault and (fault or data == expected), 'Architectural data response differs from independent service'
        if dual:
            assert not access.get('complete'), 'Duplicate data completion'
            access['complete'] = True
        architectural[hart] = None
        cache_counts[hart]['completed'] += 1

    def complete_walk(hart):
        access = implicit[hart]
        if access is None or 'expected' not in access or 'response' not in access:
            return
        data, fault, tag = access['response']
        expected, expected_fault = access['expected']
        assert tag == access['tag'] and fault == expected_fault and (fault or data == expected), 'PTE response differs from physical service'
        if hasattr(program, 'dirty_pte') and access['event'][1] == program.dirty_pte[0] and cache_counts[hart]['dirtyPteStores']:
            assert translation_counts['dirtyPteBarriers'] == 1 and not fault and data == program.dirty_pte[1], 'Dirty PTE was not consumed after its synchronization'
            translation_counts['dirtyPteReads'] += 1
        walk = walks[hart][access['port']]
        assert walk, 'PTE completion lost its translation owner'
        walk['reads'].append((access['event'][1], data, bool(fault)))
        check_translation_result(walk, None, config, models[hart], translation_history[hart])
        implicit[hart] = None

    def cacheable(address, size=8):
        return any(region.get('dataCacheable', False) and not region['device'] and region['readable']
                   and int(region['base']) <= address and address + size <= int(region['base']) + int(region['size'])
                   for region in config['memoryRegions'])

    def protected_read(hart, address, size):
        return address % size == 0 and 0 <= address <= (1 << config['physicalAddressBits']) - size and pmp_allowed(
            [models[hart].pmp_config(i) for i in range(config['pmpEntries'])],
            [models[hart].csrs[0x3b0+i] for i in range(config['pmpEntries'])], address, size, 'read',
            config['physicalAddressBits'], models[hart].data_privilege())

    def invalidating_write(owner):
        return owner and cacheable(owner['event'][1], 1) and (owner['event'][0] == 'write' or
            owner['event'][0] == 'atomic' and owner['operation'] != 2)

    def data_owner(hart, event, tag, expanded=False):
        candidates = [access for access in ([implicit[hart], *lsu_slots[hart].values()] if dual else (implicit[hart], architectural[hart]))
                      if access and access['tag'] == tag and 'expected' not in access and
                      'event' in access and
                      (access['event'] == event or expanded and event[2] in (8, 64) and
                       event[2] <= 1 << access.get('refillSize', 0) and
                       event == ('read', access['event'][1] & -event[2], event[2], 0))]
        assert len(candidates) == 1, 'Physical data service lacks unique LSU or page-table owner'
        return candidates[0]

    for line in log_lines(lines):
        fields = line.split()
        if fields[:1] == ['COVER']:
            covers.append(list(map(int, fields[1:])))
            continue
        if fields[:1] == ['WORK_CYCLE']:
            hart, terminal, cycle = map(int, fields[1:])
            assert 0 <= hart < harts and terminal in (0, 1) and (hart, terminal) not in work_samples, 'Duplicate or malformed work interval'
            work_samples[hart, terminal] = cycle, dict(cache_counts[hart])
            continue
        if fields[:1] == ['INVALIDATE']:
            recipient, address, cycle = int(fields[1]), int(fields[2], 16), int(fields[3])
            assert data_cache and config.get('dCacheRefillBytes', 8) == 64 and 0 <= recipient < harts and cycle >= 0 and address % 64 == 0, 'Invalid cache invalidation recipient'
            writers = [owner for owner in owners.values() if owner and owner['event'][1] // 64 == address // 64 and (writeback or invalidating_write(owner))]
            assert len(writers) == 1, 'Invalidation lacks a unique accepted CPU write'
            assert writeback or writers[0]['event'][0] == 'atomic' or recipient != writers[0]['hart'], 'Ordinary writer invalidated its retained copy'
            recipients = writers[0].setdefault('invalidated', set())
            assert recipient not in recipients and not writers[0]['bus'], 'Duplicate or late write invalidation'
            recipients.add(recipient)
            for access in (lsu_slots[recipient].values() if dual else (architectural[recipient],)):
                if access and 'event' in access and access['event'][0] == 'read' and 'lineValue' not in access and (
                        address // 64) % (config['dCacheBytes'] // 64) == (access['event'][1] // 64) % (config['dCacheBytes'] // 64):
                    access['invalidated'] = True
            continue
        if fields[:1] == ['RESULT']:
            results.append((int(fields[1]), int(fields[2], 16)))
            continue
        if fields[:1] == ['PHYSICAL_RESULT']:
            assert writeback and software, 'Unexpected physical result snapshot'
            physical_results.append((int(fields[1]), int(fields[2], 16)))
            continue
        if fields == ['PASS']:
            passed = True
            continue
        if fields[:1] == ['CYCLE']:
            assert device is not None, 'Unexpected platform event'
            cycle, tick = int(fields[1]), int(fields[2], 16)
            external, effective, sleeping = (int(value, 16) for value in fields[3:])
            device.begin_cycle(cycle, tick)
            assert tick == int(cycle % (software['timeTickCycles'] if software else 1) == 0), 'Platform timebase divider mismatch'
            if interrupt_dirty or external != previous_external or device.time < previous_time or device.time >= next_timer:
                expected_levels, wake_mask = 0, 0
                for hart, model in enumerate(models):
                    levels = device.levels(hart) | ((external >> (3 * hart)) & 7)
                    expected_levels |= levels << (3 * hart)
                    model.set_interrupts(levels)
                    wake[hart] = bool(model.csrs[0x304] & model.csrs[0x344])
                    wake_mask |= int(wake[hart]) << hart
                next_timer = min((value for value in device.compare if value > device.time), default=MASK + 1)
                interrupt_dirty, previous_external = False, external
            previous_time = device.time
            assert effective == expected_levels, f'Platform interrupt mismatch at cycle {cycle}'
            assert sleeping == waiting_mask, f'Architectural wait mismatch at cycle {cycle}'
            waking = waiting_mask & wake_mask
            waiting_mask &= ~waking
            while waking:
                bit = waking & -waking
                hart = bit.bit_length() - 1
                sleep_cycles[hart] += cycle - wait_started[hart] + 1
                waiting[hart] = False
                waking ^= bit
            continue
        if fields[:1] == ['CONSOLE']:
            assert software and console_events and console_events.popleft() == (int(fields[1]), int(fields[2], 16)), 'Console byte without matching software service'
            continue
        if fields[:1] == ['EXCLUSIVE']:
            assert observed_reservations is None
            observed_reservations = int(fields[1])
            continue
        if fields[:1] == ['CYCLES']:
            assert elapsed_cycles is None
            elapsed_cycles = int(fields[1])
            continue
        if fields[:1] == ['READ_CONCURRENCY']:
            assert read_observed is None, 'Duplicate read-concurrency summary'
            read_observed = tuple(map(int, fields[1:]))
            continue
        if fields[:1] == ['LINE_CONCURRENCY']:
            assert line_observed is None, 'Duplicate line-concurrency summary'
            line_observed = tuple(map(int, fields[1:]))
            assert len(line_observed) == 2 and min(line_observed) >= 0
            continue
        if fields[:1] == ['RECOVERY']:
            hart = int(fields[1])
            assert 0 <= hart < harts
            fetch_checks[hart].send((line, fields))
            continue
        if fields[:1] == ['HART']:
            hart, fields = int(fields[1]), fields[2:]
        elif harts == 1 and fields and fields[0] in ('LSU_REQUEST', 'LSU_RESPONSE', 'SOURCE', 'REQUEST', 'ACCESS_PRIVILEGE', 'ATOMIC', 'BUS', 'READ', 'LINE_BEAT', 'WRITE', 'INTERFERE', 'RESPONSE', 'FETCH', 'IRQ', 'TRACE', 'FETCH_RETIRE', 'ARCH_REQUEST', 'ARCH_FETCH', 'ARCH_CANCEL', 'LOCAL_REQUEST', 'LOCAL_RESPONSE', 'ARCH_DATA_REQUEST', 'ARCH_DATA_RESPONSE', 'CACHE_SAMPLE', 'CACHE_STORE', 'WRITEBACK_REQUEST', 'WRITEBACK_RESPONSE', 'TRANSLATE_REQUEST', 'TRANSLATE_RESPONSE', 'WALK_REQUEST', 'WALK_RESPONSE', 'PREDICT_CLEAR', 'PREDICT_UPDATE', 'BRANCH_RESOLVE', 'RECOVERY'):
            hart = 0
        else:
            continue
        assert 0 <= hart < harts
        explicit_source = int(fields[1]) if fields[:1] == ['SOURCE'] else None
        if explicit_source is not None:
            fields = fields[2:]
        transport_tag = int(fields[1], 16) if fields[:1] == ['TAG'] else None
        if transport_tag is not None:
            fields = fields[2:]
        kind = fields[0]
        if kind in ('PREDICT_CLEAR', 'PREDICT_UPDATE', 'BRANCH_RESOLVE', 'RECOVERY'):
            fetch_checks[hart].send((line, fields))
            continue
        client = int(fields[1]) if kind == 'RESPONSE' else int(fields[1] != 'fetch') if kind in ('REQUEST', 'BUS') else 0 if kind in ('FETCH', 'ARCH_REQUEST', 'ARCH_FETCH', 'ARCH_CANCEL') else 1
        source = explicit_source if explicit_source is not None else recent_source[hart] if kind == 'ACCESS_PRIVILEGE' else 2 * hart + client
        assert 0 <= source < 2 * harts and source // 2 == hart, 'Source disagrees with hart'
        if explicit_source is not None and kind in ('REQUEST', 'BUS', 'RESPONSE', 'FETCH') and not (kind == 'BUS' and fields[1] == 'writeback'):
            assert source % 2 == client, 'Source disagrees with client'
        physical_source = source
        if dual:
            candidates = [key for key in owners if key[0] == source]
            source = (source, transport_tag) if transport_tag is not None else candidates[0] if len(candidates) == 1 else (source, None)
        if explicit_source is None and (kind in ('WRITEBACK_REQUEST', 'WRITEBACK_RESPONSE') or kind == 'BUS' and fields[1] == 'writeback'):
            candidates = [index for index, owner in owners.items() if owner and owner['hart'] == hart]
            assert len(candidates) == 1, 'Legacy writeback event lacks unique ownership'
            source = candidates[0]
        if explicit_source is None and kind in ('READ', 'LINE_BEAT'):
            candidates = [index for index, owner in owners.items() if owner and owner['hart'] == hart and owner['bus']]
            assert len(candidates) == 1, 'Legacy read event lacks unique ownership'
            source = candidates[0]
        active = owners.get(source)
        if kind == 'REQUEST':
            recent_source[hart] = physical_source
        if dual:
            tag = (int(fields[5], 16) if kind in ('ARCH_DATA_REQUEST', 'REQUEST') else int(fields[3], 16) if kind in ('ARCH_DATA_RESPONSE', 'CACHE_SAMPLE', 'CACHE_STORE') else
                   active['tag'] if active and source[0] % 2 else None)
            architectural[hart] = lsu_slots[hart].get(tag)
        if kind != 'TRACE':
            fetch_checks[hart].send((line, fields))
        if kind == 'FETCH_RETIRE':
            retirement_groups[hart] = retirement_group(fields, config.get('issueWidth', 1))
            continue
        if kind in ('ARCH_REQUEST', 'ARCH_FETCH', 'ARCH_CANCEL'):
            if kind == 'ARCH_REQUEST':
                assert active is None or active['hart'] != hart or active['event'][0] != 'fetch', 'New fetch replaced an undrained instruction owner'
                fetch_privileges[hart] = retired_privileges[hart]
                fetch_protection[hart] = (int(fields[2], 16),
                    [models[hart].pmp_config(index) for index in range(config['pmpEntries'])],
                    [models[hart].csrs[0x3b0 + index] for index in range(config['pmpEntries'])])
            assert kind != 'ARCH_REQUEST' or not waiting[hart], 'New architectural fetch while waiting'
            if kind == 'ARCH_CANCEL' and walks[hart][0]:
                walks[hart][0]['cancelled'] = True
            if kind == 'ARCH_CANCEL':
                local = [owner for owner in owners.values() if owner['hart'] == hart]
                concurrent['instructionCancelDuringDataService'] += int(any(owner['event'][0] == 'fetch' for owner in local) and
                    any(owner['event'][0] != 'fetch' for owner in local))
            continue
        assert kind in ('LSU_REQUEST', 'LSU_RESPONSE', 'REQUEST', 'ACCESS_PRIVILEGE', 'ATOMIC', 'BUS', 'READ', 'LINE_BEAT', 'WRITE', 'INTERFERE', 'RESPONSE', 'FETCH', 'IRQ', 'TRACE', 'LOCAL_REQUEST', 'LOCAL_RESPONSE', 'ARCH_DATA_REQUEST', 'ARCH_DATA_RESPONSE', 'CACHE_SAMPLE', 'CACHE_STORE', 'WRITEBACK_REQUEST', 'WRITEBACK_RESPONSE', 'TRANSLATE_REQUEST', 'TRANSLATE_RESPONSE', 'WALK_REQUEST', 'WALK_RESPONSE'), 'Unknown hart event'
        if kind == 'LSU_REQUEST':
            tag, pc, fetch_tag, instruction = (int(value, 16) for value in fields[1:])
            assert dual and tag in (0, 1) and tag not in lsu_slots[hart] and len(lsu_order[hart]) < 2, 'LSU context reused before retirement'
            access = dict(tag=tag, pc=pc, fetchTag=fetch_tag, instruction=instruction)
            lsu_slots[hart][tag] = access
            lsu_order[hart].append(access)
        elif kind == 'LSU_RESPONSE':
            tag, pc, fetch_tag, fault, cause, tval = (int(value, 16) for value in fields[1:])
            access = lsu_slots[hart].get(tag)
            assert access and not access.get('done') and (pc, fetch_tag) == (access['pc'], access['fetchTag']), 'LSU completion identity'
            assert all(value.get('done') for value in list(lsu_order[hart])[:list(lsu_order[hart]).index(access)]), 'LSU completed out of accepted order'
            access.update(done=True, completion=(fault, cause, tval))
        elif kind == 'TRANSLATE_REQUEST':
            port, address, privilege, fetch, write, satp, sum_enabled, mxr = (int(value, 16) for value in fields[1:])
            assert translated and port in (0, 1) and walks[hart][port] is None, 'Overlapping translation port ownership'
            assert privilege == (fetch_privileges[hart] if port == 0 else models[hart].data_privilege()), 'Translation effective privilege'
            assert (satp, sum_enabled, mxr) == (models[hart].csrs[0x180], bool(models[hart].csrs[0x300] & (1 << 18)), bool(models[hart].csrs[0x300] & (1 << 19))), 'Translation context snapshot'
            walks[hart][port] = dict(port=port, address=address, privilege=privilege, kind='fetch' if fetch else 'write' if write else 'read',
                               satp=satp, status=(sum_enabled << 18) | (mxr << 19), reads=[], acceptedHistory=tuple(translation_history[hart]))
            translation_counts['requests'] += 1
        elif kind == 'TRANSLATE_RESPONSE':
            port, physical, fault, cause = (int(value, 16) for value in fields[1:])
            assert port in (0, 1), 'Unknown translation response port'
            walk = walks[hart][port]
            assert translated and walk and (implicit[hart] is None or implicit[hart]['port'] != port), 'Unowned translation response'
            translation_counts['hits'] += check_translation_result(walk, (physical, fault, cause), config, models[hart], translation_history[hart])
            translation_counts['responsesDuringPeerWalk'] += int(walkers[hart] is not None and walkers[hart] != port)
            walks[hart][port] = None
            if walkers[hart] == port:
                walkers[hart] = None
            translation_counts['responses'] += 1
        elif kind == 'WALK_REQUEST':
            address, tag, port = (int(value, 16) for value in fields[1:])
            assert translated and port in (0, 1) and walks[hart][port] and implicit[hart] is None and walkers[hart] in (None, port), 'Unowned page-table access'
            assert permitted_table_read(config, models[hart], address), 'Page walk escaped S-mode physical protection'
            implicit[hart] = dict(event=('read', address, 8, 0), tag=tag, walk=True, port=port)
            walkers[hart] = port
            translation_counts['pteReads'] += 1
        elif kind == 'WALK_RESPONSE':
            assert implicit[hart] and 'response' not in implicit[hart], 'Unowned PTE response'
            implicit[hart]['response'] = tuple(int(value, 16) for value in fields[1:])
            complete_walk(hart)
        elif kind == 'ARCH_DATA_REQUEST':
            access = architectural[hart]
            assert observed_data and (access is not None and 'event' not in access if dual else access is None and pending[hart] is None), 'Overlapping architectural data requests'
            event = fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            assert event[0] in ('read', 'write', 'atomic') and int(fields[6], 16) == (models[hart].data_privilege() != 0), 'Architectural access context'
            certificate = int(fields[7], 16)
            assert certificate in (0, 3, 6), 'Invalid refill certificate'
            if certificate:
                size = 1 << certificate
                assert data_cache and event[0] == 'read' and event[2] in (1, 2, 4, 8) and cacheable(event[1] & -size, size), 'Refill certificate has no cacheable demand'
                assert size <= config.get('dCacheRefillBytes', 8), 'Refill certificate exceeds configured span'
                assert protected_read(hart, event[1], event[2]) and protected_read(hart, event[1] & -size, size), 'Refill certificate escaped PMP authorization'
            if dual:
                access.update(event=event, refillSize=certificate)
                if any(region['device'] and int(region['base']) <= event[1] < int(region['base']) + int(region['size']) for region in config['memoryRegions']):
                    assert lsu_order[hart][0] is access and models[hart].pc == access['pc'], 'Device access preceded architectural authorization'
            else:
                architectural[hart] = dict(event=event, tag=int(fields[5], 16), refillSize=certificate)
            cache_counts[hart]['accepted'] += 1
            cache_counts[hart]['reads'] += int(event[0] == 'read')
        elif kind in ('CACHE_SAMPLE', 'CACHE_STORE'):
            address, value, tag = (int(field, 16) for field in fields[1:4])
            size = int(fields[4])
            store = kind == 'CACHE_STORE'
            assert not store or writeback, 'Unexpected cache-local store'
            access = data_owner(hart, ('write' if store else 'read', address, size, value if store else 0), tag)
            assert data_cache and access and not access.get('physical') and 'expected' not in access, 'Unowned, duplicate or physically serviced cache sample'
            assert size in (1, 2, 4, 8) and address % size == 0 and cacheable(address & ~7), 'Cache sample outside permitted cacheable RAM'
            assert store or access.get('walk') or protected_read(hart, address, size), 'Cache sample bypassed demand protection'
            reserved = sum(address < base + length and base < address + size for base, length in monitor.reservations.values()) if store else 0
            expected = (sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(size)), 0) if access.get('walk') else service(hart, access['event'])
            if store:
                assert pending[hart] and not pending[hart][7], 'Cache-local store bypassed architectural authorization'
                expected = (0, 0)
            assert expected == (0 if store else value, 0), 'Cache sample differs from independent shared memory'
            if store:
                cached_writes.update(range(address, address + size))
                cache_counts[hart]['cachedStores'] += 1
                cache_counts[hart]['reservedStores'] += reserved
                if address == getattr(program, 'synchronization', {}).get('code'):
                    cache_counts[hart]['dirtyInstructionStores'] += 1
                if hasattr(program, 'dirty_pte') and address == program.dirty_pte[0]:
                    cache_counts[hart]['dirtyPteStores'] += 1
                if address == getattr(program, 'dirty_permission', None):
                    cache_counts[hart]['dirtyPermissionStores'] += 1
            access['expected'] = expected
            cache_counts[hart]['hits'] += int(not store and not access.get('walk'))
            hit_addresses[hart][address] += int(not store and not access.get('walk'))
            cache_counts[hart]['hitsDuringPeerService'] += int(not store and not access.get('walk') and any(owner is not None for owner in owners.values() if owner and owner['hart'] != hart))
            (complete_walk if access.get('walk') else complete_data)(hart)
        elif kind == 'WRITEBACK_REQUEST':
            address, data, mask, tag, privileged = (int(v, 16) for v in fields[1:])
            assert writeback and maintenance is None and active and tag == active['tag'], 'Unowned or overlapping writeback'
            if address == getattr(program, 'dirty_permission', None):
                assert cache_counts[hart]['permissionChanges'] == 1 and cache_counts[hart]['permissionRejected'] == 1, 'Dirty recall preceded permission revocation or denied demand'
                cache_counts[hart]['permissionWritebacks'] += 1
            assert address % 8 == 0 and 0 < mask < 256 and cacheable(address, 8), 'Writeback outside cacheable words'
            assert any(r['writable'] and int(r['base']) <= address and address + 8 <= int(r['base']) + int(r['size']) for r in config['memoryRegions']), 'Writeback escaped physical write permission'
            assert privileged == 1, 'Writeback escaped trusted maintenance context'
            for byte in range(8):
                if mask >> byte & 1:
                    assert address + byte in cached_writes and data >> (8 * byte) & 255 == memory.get(address + byte, 0), 'Writeback lacks a cached store or carries stale bytes'
            if active['event'][0] == 'fetch' and address == getattr(program, 'synchronization', {}).get('code'):
                cache_counts[hart]['instructionWritebacks'] += 1
            maintenance = dict(hart=hart, address=address, data=data, mask=mask, tag=tag, bus=False)
        elif kind == 'WRITEBACK_RESPONSE':
            fault, tag, last = (int(v, 16) for v in fields[1:])
            assert maintenance and maintenance['hart'] == hart and maintenance['bus'] and tag == maintenance['tag'] and last, 'Writeback completion identity'
            assert fault == int(maintenance['address'] == program.faults.get('write')), 'Writeback physical fault attribution'
            maintenance = None
        elif kind == 'ARCH_DATA_RESPONSE':
            access = architectural[hart]
            assert observed_data and access and 'response' not in access, 'Unowned or duplicate architectural response'
            access['response'] = tuple(int(field, 16) for field in fields[1:])
            if not access.get('physical') and 'expected' not in access:
                assert access['response'][1] and pending[hart] is None, 'Architectural response without a cache sample or physical service'
                if not dual:
                    first = len(models[hart].requests)
                    pending[hart] = models[hart].step()
                    assert pending[hart][7] and [event for event in models[hart].requests[first:] if event[0] != 'fetch'] == [access['event']], 'Unexpected cache-local rejection'
                access['expected'] = (0, 1)
                cache_counts[hart]['rejectedReads'] += int(access['event'][0] == 'read')
            complete_data(hart)
        elif kind == 'REQUEST':
            assert active is None, 'Overlapping source ownership'
            event = fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            peers = [owner for owner in owners.values() if owner is not None]
            cache_operation = int(fields[6], 16) if len(fields) > 6 else 0
            assert cache_operation in (0, 1, 2) and (writeback or cache_operation == 0), 'Unexpected internal cache operation'
            assert not peers or read_slots > 0 and not cache_operation and len(peers) < read_slots and ordinary(event) and all(not owner.get('cacheOperation') and ordinary(owner['event']) for owner in peers), 'Exclusive request overlapped physical service or exceeded read slots'
            tag = int(fields[5], 16)
            assert not dual or transport_tag == tag, 'Physical context tag disagrees with payload'
            same_client = [owner for key, owner in owners.items() if (key[0] if dual else key) == physical_source]
            assert len(same_client) < (2 if dual and physical_source % 2 else 1), 'Client context capacity exceeded'
            previous = architectural[hart]
            if previous and 'lineValue' in previous and event[0] != 'fetch':
                assert previous.get('invalidated') and not previous.get('retry') and event == previous['event'] and tag == previous['tag'], 'Clean line retried without matching write invalidation'
                del previous['lineValue']
                previous['physical'], previous['retry'] = False, True
                cache_counts[hart]['refillRetries'] += 1
            access = data_owner(hart, event, tag, expanded=True) if observed_data and event[0] != 'fetch' and cache_operation != 2 else None
            privilege = 1 if access and access.get('walk') else fetch_privileges[hart] if event[0] == 'fetch' else models[hart].data_privilege() if hasattr(models[hart], 'data_privilege') else 3
            active = dict(hart=hart, event=event, tag=tag, cacheOperation=cache_operation, bus=False, response=None, expectedPrivileged=privilege != 0)
            owners[source] = active
            if event[0] == 'fetch' and event[2] == 64:
                assert config.get('enableBurstRefill') and event[1] % 64 == 0, 'Unconfigured or unaligned line read'
                context = fetch_protection[hart]
                assert context and context[0] == tag, 'Line lacks its architectural protection owner'
                assert pmp_allowed(context[1], context[2], event[1], 64, 'fetch',
                                   config['physicalAddressBits'], privilege), 'Line escaped whole-range PMP authorization'
            if event[2] == 64:
                if event[0] == 'read':
                    assert config.get('dCacheRefillBytes', 8) == 64 and access and not access.get('walk'), 'Unconfigured data line or page-table expansion'
                active.update(chunks=deque(), beat=0, chunk=0, lineFault=False)
            if access and not cache_operation:
                expanded = event != access['event']
                assert 'expected' not in access and not access.get('physical'), 'Physical request lacks unique architectural ownership'
                assert not expanded or not access.get('retried'), 'Expanded refill repeated after retry'
                if access.get('retry'):
                    assert not expanded and not access.get('retried'), 'Refill fault did not retry the exact demand once'
                    access['retried'] = True
                if expanded:
                    assert cacheable(event[1], event[2]) and protected_read(hart, event[1], event[2]), 'Expanded read lacks complete physical authorization'
                access['physical'] = True
                active['walk'] = access.get('walk', False)
                active['expanded'] = expanded
                active['access'] = access
                cache_counts[hart]['physicalReads'] += int(event[0] == 'read' and not active['walk'])
                if event[0] == 'read' and not active['walk']:
                    cache_counts[hart]['lineReads'] += int(event[2] == 64)
            if event[0] == 'atomic':
                instruction_address = models[hart].translate(models[hart].pc, 'fetch')
                instruction = sum(memory.get(instruction_address + byte, 0) << (8 * byte) for byte in range(4))
                operation = instruction >> 27
                assert instruction & 127 == 47 and (instruction >> 12) & 7 == 3 and operation in (0, 1, 2, 3, 8)
                assert operation != 2 or (instruction >> 20) & 31 == 0
                active.update(operation=operation, eligible=operation == 3 and models[hart].local_reservation == event[1:3])
            sources.add(2 * hart + int(event[0] != 'fetch'))
            if tag in tags and tags[tag] != hart:
                collisions.add(tag)
            tags[tag] = hart
        elif kind == 'ACCESS_PRIVILEGE':
            assert active and active['hart'] == hart and not active.get('privilegeMetadata'), 'Unowned access privilege'
            assert int(fields[1], 16) == active['expectedPrivileged'], 'Accepted access privilege differs from architectural context'
            active['privilegeMetadata'] = True
        elif kind == 'ATOMIC':
            assert active and active['hart'] == hart and active['event'][0] == 'atomic' and not active.get('atomicMetadata')
            assert tuple(int(value, 16) for value in fields[1:]) == (active['operation'], int(active['eligible'])), 'Atomic request metadata differs from instruction/local LR pair'
            active['atomicMetadata'] = True
        elif kind == 'LOCAL_REQUEST':
            assert device is not None and active and active['hart'] == hart and not active['bus']
            event = fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            assert event == active['event'] and int(fields[5], 16) == active['tag'], 'Local request identity'
            assert device.base <= event[1] < device.base + 65536, 'Local request outside platform window'
            active.update(bus=True, local=True, response=service(hart, event, local=True))
        elif kind == 'LOCAL_RESPONSE':
            assert device is not None and active and active['hart'] == hart and active.get('local') and not active.get('localResponse')
            data, fault, tag = (int(value, 16) for value in fields[1:])
            assert (data, fault) == active['response'] and tag == active['tag'], 'Local response value or identity'
            active['localResponse'] = True
        elif kind == 'BUS':
            axi_transactions += 1
            event = fields[1], int(fields[2], 16), int(fields[3]), int(fields[4], 16)
            if event[0] == 'writeback':
                assert writeback and maintenance and maintenance['hart'] == hart and not maintenance['bus'], 'Unowned physical writeback'
                assert event[1:] == (maintenance['address'], 8, maintenance['data']) and int(fields[5], 16) == maintenance['mask'], 'Physical writeback payload or strobes changed'
                maintenance['bus'] = True
                if event[1] != program.faults.get('write'):
                    physical_write(event[1], 8, event[3], maintenance['mask'])
                    monitor.write(event[1], 8)
                continue
            if not writeback and config.get('dCacheRefillBytes', 8) == 64 and invalidating_write(active):
                targets = set(range(harts)) - ({hart} if active['event'][0] == 'write' else set())
                assert active.get('invalidated', set()) == targets, 'CPU write escaped required cache invalidations'
            assert device is None or not device.base <= event[1] < device.base + 65536, 'Platform request escaped to AXI'
            if event[0] in ('exclusive_read', 'exclusive_write'):
                assert active and active['hart'] == hart and active['event'][0] == 'atomic'
                _, address, size, addend = active['event']
                assert event[1:3] == (address, size) and size == 8
                if event[0] == 'exclusive_read':
                    assert active['operation'] != 3 and active.get('phase') in (None, 'retry') and event[3] == 0
                    active.update(bus=True, phase='read')
                    read_started(source)
                else:
                    if active['operation'] == 3:
                        assert active.get('phase') is None and active['eligible'] and event[3] == addend, 'SC without a matching local LR or incorrect operand'
                        active.update(bus=True, old=sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(size)))
                    else:
                        assert active['operation'] in (0, 1, 8) and active['phase'] == 'write' and event[3] == atomic_value(active['operation'], active['old'], addend, size)
                    active['phase'] = 'response'
                continue
            assert active and active['hart'] == hart and active['event'] == event and not active['bus']
            active['bus'] = True
            if event[0] in ('read', 'fetch'):
                read_started(source)
            if event[0] == 'read' and not active.get('walk'):
                cache_counts[hart]['axiReadAddresses'] += 1
                cache_counts[hart]['axiReadBytes'] += event[2]
            if event[0] == 'write':
                service(hart, event)
                if writeback and event[1] != program.faults.get('write'):
                    physical_write(event[1], event[2], event[3])
                active['response'] = (0, int(event[1] == program.faults.get('write')))
        elif kind == 'LINE_BEAT':
            assert active and active['hart'] == hart and active['bus'] and active['event'][0] in ('read', 'fetch') and active['event'][2] == 64, 'Unowned line beat'
            address, response, data, last = (int(value, 16) for value in fields[1:])
            bus_bytes = config['axiDataBits'] // 8
            expected_address = active['event'][1] + bus_bytes * active['beat']
            expected = sum(physical_memory.get(expected_address + byte, 0) << (8 * byte) for byte in range(bus_bytes))
            fault = expected_address <= program.faults.get(active['event'][0], -1) < expected_address + bus_bytes
            assert (address, response, data, last) == (expected_address, 2 if fault else 0, expected, int(active['beat'] == 64 // bus_bytes - 1)), 'Line beat data, order, error or last differs from independent memory'
            for byte in range(0, bus_bytes, 8):
                active['chunks'].append(((data >> (8 * byte)) & MASK, int(fault or active['lineFault'])))
            active['lineFault'] |= fault
            active['beat'] += 1
            line_beats += 1
            cache_counts[hart]['lineBeats'] += int(active['event'][0] == 'read')
            if last:
                read_completed(source)
        elif kind == 'READ':
            assert active and active['hart'] == hart and active['bus'] and active['response'] is None
            access, address, size, _ = active['event']
            read_completed(source)
            expected = sum(physical_memory.get(address + byte, 0) << (byte * 8) for byte in range(size))
            if writeback and cacheable(address, size):
                assert expected == sum(memory.get(address + byte, 0) << (byte * 8) for byte in range(size)), 'Physical read preceded required dirty recall'
            if access == 'atomic':
                assert active['phase'] == 'read'
                response = 2 if address <= program.faults.get('read', -1) < address + size else 0 if address == program.faults.get('exclusive') else 1
                assert tuple(int(v, 16) for v in fields[1:]) == (address, response, expected)
                active.update(old=expected, phase='write' if response == 1 else 'complete')
                if response == 1:
                    monitor.reserve(hart, address, size)
                    reservation_max = max(reservation_max, len(monitor.reservations))
                    if active['operation'] == 2:
                        service(hart, active['event'])
                        active.update(response=(expected, 0), phase='complete')
                if response != 1:
                    service(hart, active['event'], atomic_fault=True)
                    active['response'] = (expected, 1)
                continue
            fault = address <= program.faults.get(access, -1) < address + size if access == 'read' else address == program.faults.get(access)
            assert tuple(int(v, 16) for v in fields[1:]) == (address, 2 if fault else 0, expected)
            if access == 'read' and not active.get('walk'):
                overtaken += sum(record is not None for h, record in enumerate(pending) if h != hart)
                if not active.get('expanded') or not fault:
                    service(hart, architectural[hart]['event'] if active.get('expanded') else active['event'])
            active['response'] = (expected, int(fault))
        elif kind == 'INTERFERE':
            assert active and active['hart'] == hart and active['phase'] == 'response' and failures > 0
            address, value = (int(v, 16) for v in fields[1:])
            assert address == active['event'][1] and value == (active['old'] + program.interference) & MASK
            for byte in range(8):
                memory[address + byte] = (value >> (8 * byte)) & 255
            if writeback:
                physical_write(address, 8, value)
            failures -= 1
            monitor.write(address, 8)
            active['phase'] = 'interference'
        elif kind == 'WRITE':
            assert active and active['hart'] == hart and active['phase'] in ('response', 'interference')
            address, response = (int(v, 16) for v in fields[1:])
            assert address == active['event'][1]
            fault = address == program.faults.get('write')
            success = not fault and monitor.conditional(hart, address, active['event'][2])
            assert response == (2 if fault else 1 if success else 0), 'Exclusive response differs from independent endpoint monitor'
            if writeback and success:
                value = active['event'][3] if active['operation'] == 3 else atomic_value(active['operation'], active['old'], active['event'][3], active['event'][2])
                physical_write(address, active['event'][2], value)
            active['phase'] = 'retry' if response == 0 and active['operation'] != 3 else 'complete'
            if active['operation'] == 3:
                active['scSuccess'] = success
                sc_results[hart, success] += int(not fault)
                service(hart, active['event'], atomic_fault=fault)
                active['response'] = (0 if success else 1, int(fault))
            elif response:
                service(hart, active['event'], atomic_fault=fault)
                active['response'] = (active['old'], int(fault))
        elif kind == 'RESPONSE':
            assert active and active['hart'] == hart, 'Response to the wrong hart'
            assert not config.get('enableUserMode') or active.get('privilegeMetadata'), 'Missing accepted access privilege'
            channel, data, fault, tag = (int(v, 16) for v in fields[1:5])
            last = int(fields[5], 16) if len(fields) > 5 else 1
            if active.get('cacheOperation'):
                assert channel == 1 and tag == active['tag'] and last and not fault and data == 0 and maintenance is None, 'Internal cache operation completion'
                transactions += 1
                owners.pop(source); active = None
                continue
            if active['event'][2] == 64 and active['bus']:
                assert channel == int(active['event'][0] != 'fetch') and tag == active['tag'] and active['chunks'], 'Line chunk has wrong owner or precedes physical service'
                expected_data, expected_fault = active['chunks'].popleft()
                assert (data, fault, last) == (expected_data, expected_fault, int(active['chunk'] == 7)), 'Line chunk value, fault or terminal placement'
                if channel and active['chunk'] == (architectural[hart]['event'][1] & 63) // 8:
                    active['demandData'] = expected_data
                active['chunk'] += 1
                if not last:
                    continue
                assert active['beat'] == 64 // (config['axiDataBits'] // 8) and not active['chunks'], 'Incomplete line completion'
                transactions += 1
                if channel:
                    access = architectural[hart]
                    if active['lineFault']:
                        assert pending[hart] is None and 'response' not in access and not access.get('retry'), 'Line fault published or retried more than once'
                        access['physical'], access['retry'] = False, True
                        cache_counts[hart]['refillRetries'] += 1
                    else:
                        access['lineValue'] = (active['demandData'] >> (8 * (access['event'][1] & 7))) & ((1 << (8 * access['event'][2])) - 1)
                        complete_data(hart)
                owners.pop(source); active = None
                continue
            assert last, 'Scalar completion must be terminal'
            transactions += 1
            assert channel == int(active['event'][0] != 'fetch') and tag == active['tag']
            if not active['bus']:
                assert not active.get('expanded'), 'Authorized expanded read was locally rejected'
                if not fault and active['event'][0] == 'atomic' and active['operation'] == 3 and not active['eligible']:
                    service(hart, active['event'])
                    assert data == 1, 'SC without local reservation must fail without bus traffic'
                    sc_results[hart, False] += 1
                else:
                    assert fault, 'Locally rejected request did not fault'
                if channel and fault and not (dual and active['event'][0] == 'read'):
                    assert pending[hart] is None
                    first = len(models[hart].requests)
                    pending[hart] = models[hart].step()
                    requests = [event for event in models[hart].requests[first:] if event[0] != 'fetch']
                    assert requests == [active['event']], 'Unexpected locally rejected request'
                    assert pending[hart][7]
                    if active['event'][0] == 'atomic':
                        assert (models[hart].atomic_operation, models[hart].sc_eligible) == (active['operation'], active['eligible'])
                        assert not atomic_metadata or active.get('atomicMetadata'), 'Missing rejected atomic metadata'
            else:
                expected_data, expected_fault = active['response']
                assert fault == expected_fault and (fault or data == expected_data), 'Response data or fault mismatch'
                assert not active.get('local') or active.get('localResponse'), 'Core response preceded local service'
            if observed_data and channel:
                access = implicit[hart] if active.get('walk') else architectural[hart]
                assert access and access.get('physical') and 'expected' not in access
                if active.get('expanded') and fault:
                    assert pending[hart] is None and 'response' not in access and not access.get('retry'), 'Expanded fault published or retried more than once'
                    access['physical'], access['retry'] = False, True
                    cache_counts[hart]['refillRetries'] += 1
                    owners.pop(source); active = None
                    continue
                access['expected'] = (((data >> (8 * (access['event'][1] & 7))) & ((1 << (8 * access['event'][2])) - 1)), 0) if active.get('expanded') else active['response'] if active['bus'] else (1, 0) if not fault else (0, 1)
                cache_counts[hart]['expandedReads'] += int(active.get('expanded', False))
                (complete_walk if active.get('walk') else complete_data)(hart)
            owners.pop(source); active = None
        elif kind == 'IRQ':
            if device is None:
                models[hart].set_interrupts(int(fields[1], 16))
                if models[hart].csrs[0x304] & models[hart].csrs[0x344]:
                    waiting[hart] = False
            else:
                assert int(fields[1], 16) == sum((bool(models[hart].csrs[0x344] & (1 << bit)) << index)
                                               for index, bit in enumerate((3, 7, 11))), 'Retirement IRQ disagrees with cycle sample'
        elif kind == 'TRACE':
            assert not waiting[hart], 'Architectural event while waiting without a wakeup'
            observed = tuple(int(v, 16) for v in fields[1:])
            if dual and lsu_order[hart] and lsu_order[hart][0]['pc'] == observed[1]:
                access = lsu_order[hart][0]
                assert access.get('done') and access['instruction'] == observed[2], 'Retirement preceded its LSU completion'
                assert access['completion'] == (observed[7], observed[8], observed[9]), 'Retirement changed the LSU fault context'
                if access.get('event', (None,))[0] == 'read':
                    assert access.get('complete'), 'Retirement preceded its data response'
                    service(hart, access['event'], read_value=access['expected'][0], replay=True)
                elif 'event' not in access:
                    assert access['completion'][0] and pending[hart] is None, 'Unserviced LSU operation did not fault'
                    pending[hart] = models[hart].step()
                    assert pending[hart][7], 'LSU-local rejection differs from instruction model'
                lsu_order[hart].popleft()
                del lsu_slots[hart][access['tag']]
            if translated and translation_maintenance(observed):
                translation_history[hart].clear()
                for walk in walks[hart]:
                    if walk:
                        walk['stale'] = True
            eligible, owned = models[hart].interrupt_cause(), pending[hart] is not None
            if pending[hart] is not None:
                assert dual or active is None or active['hart'] != hart or active['event'][0] == 'fetch', 'Memory operation retired before its response'
                assert dual or not observed_data or architectural[hart] is None, 'Memory operation retired before architectural response'
                wanted, pending[hart] = pending[hart], None
            elif observed[8] >> 63:
                wanted = models[hart].interrupt()
                interrupts[hart] += 1
                causes[hart, wanted[8] & 63] += 1
            else:
                first = len(models[hart].requests)
                wanted = models[hart].step()
                assert not observed_data or not any(event[0] != 'fetch' for event in models[hart].requests[first:]), 'Retirement omitted an architectural data request'
            if eligible and not wanted[7]:
                deferred[hart] = defer_interrupt(wanted, retirement_groups[hart], deferred[hart], owned, config.get('loadQueueEntries', 1))
            else:
                deferred[hart] = None
            fetch_checks[hart].send((line, fields))
            models[hart].requests.clear()
            models[hart].bus.clear()
            if hasattr(models[hart], 'request_privileges'):
                models[hart].request_privileges.clear()
            retired_privileges[hart] = getattr(models[hart], 'privilege', 3)
            assert observed == wanted, f'{name} hart {hart}:\nactual {observed}\nexpected {wanted}'
            if wanted[1] == getattr(program, 'permission_update_pc', None):
                assert cache_counts[hart]['dirtyPermissionStores'] == 1 and not wanted[7], 'Permission update lacks a prior authorized cached store'
                cache_counts[hart]['permissionChanges'] += 1
            if wanted[7] and wanted[8] == 7 and wanted[9] == getattr(program, 'dirty_permission', None):
                cache_counts[hart]['permissionRejected'] += 1
            if hasattr(program, 'dirty_pte') and wanted[2] == 0x12000073 and cache_counts[hart]['dirtyPteStores']:
                translation_counts['dirtyPteBarriers'] += 1
            wake[hart] = bool(models[hart].csrs[0x304] & models[hart].csrs[0x344])
            wake_mask = (wake_mask & ~(1 << hart)) | (int(wake[hart]) << hart)
            if wanted[7]:
                waiting[hart] = False
                if dual:
                    assert all(access.get('done') for access in lsu_order[hart]), 'Trap changed context before accepted reads drained'
                    lsu_order[hart].clear(); lsu_slots[hart].clear()
            elif wanted[2] == 0x10500073:
                waiting[hart] = config['enableInterrupts'] and not wake[hart]
                if waiting[hart]:
                    wait_started[hart] = device.cycle + 1 if device is not None else 0
            waiting_mask = (waiting_mask & ~(1 << hart)) | (int(waiting[hart]) << hart)
            events += 1
            if any(owner is not None for owner in owners.values() if owner and owner['hart'] != hart):
                concurrent['trapDuringPeerService'] += int(bool(wanted[7]))
                concurrent['redirectDuringPeerService'] += int(wanted[3] != wanted[1] + 4)
            if not wanted[7] and wanted[1] == program.stop:
                finished.add(hart)
    assert len(covers) == 1 and len(covers[0]) == 6 and (harts == 1 or all(covers[0])), 'Missing AXI scheduling coverage'
    if software_output:
        assert passed, 'Software simulation did not finish'
        assert results == [(hart, 1) for hart in range(harts)], 'Test memory did not contain per-hart success'
        if writeback:
            assert physical_results == [(hart, sum(physical_memory.get(software['results'] + 8 * hart + byte, 0) << (8 * byte) for byte in range(8))) for hart in range(harts)], 'Physical result snapshot differs from bus memory'
    if device is not None:
        for hart in range(harts):
            if waiting[hart]:
                sleep_cycles[hart] += device.cycle - wait_started[hart] + 1
    assert finished == set(range(harts)) and all(record is None for record in pending)
    assert all(owner is None or owner['event'][0] == 'fetch' for owner in owners.values()), 'Unretired data access at completion'
    assert all(not slots for slots in lsu_slots) if dual else all(access is None for access in architectural), 'Uncompleted architectural data access'
    assert failures == 0, 'Exclusive failure stimulus was not consumed'
    if hasattr(program, 'dirty_pte'):
        assert sum(c['dirtyPteStores'] for c in cache_counts) == 1 and translation_counts['dirtyPteReads'] == 1, 'Missing dirty PTE store or synchronized page walk'
    if hasattr(program, 'dirty_permission'):
        assert sum(c['permissionWritebacks'] for c in cache_counts) == 1, 'Missing dirty recall after permission revocation'
    assert not atomic_metadata or observed_reservations == reservation_max, 'Exclusive monitor coverage differs from independent reservations'
    if harts > 1:
        assert sources == set(range(2 * harts)) and collisions, 'Missing source or cross-hart tag collision'
    expected_interrupts = (Counter({hart: 2 * program.platform['rounds'] for hart in range(harts)}) if hasattr(program, 'platform') else
                           Counter({program.interrupts.get('hart', 0): program.interrupts['mask'].bit_count()}) if hasattr(program, 'interrupts') else Counter())
    if software and software['kind'] == 'zephyr':
        assert all(causes[hart, 3] and causes[hart, 7] and not causes[hart, 11] for hart in range(harts)), 'Missing per-hart software/timer progress'
    elif software:
        expected_causes = Counter((hart, cause) for hart in range(harts) for cause in software['expectedInterruptCauses'])
        assert causes == expected_causes, f'Software interrupt causes: {causes} != {expected_causes}'
    else:
        assert interrupts == expected_interrupts, f'Interrupt isolation: {interrupts} != {expected_interrupts}'
    if hasattr(program, 'lrsc'):
        job = program.lrsc
        word = lambda address: sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8))
        witnesses = [[word(job['witnesses'] + hart * job['stride'] + 8 * round) for round in range(job['rounds'])] for hart in range(harts)]
        if job['shared']:
            assert word(job['counter']) == job['rounds'] * harts
            assert sorted(value for group in witnesses for value in group) == list(range(job['rounds'] * harts)), 'Lost or duplicate conditional store'
        else:
            assert all(word(job['counter'] + 8 * hart) == job['rounds'] and witnesses[hart] == list(range(job['rounds'])) for hart in range(harts)), 'Private LR/SC result mismatch'
            assert reservation_max >= min(harts, 2), 'Independent exclusive IDs were not simultaneously live'
        assert all(sc_results[hart, True] == job['rounds'] for hart in range(harts)), 'Missing per-hart successful SC'
    elif harts > 1 and 'atomic' in name:
        word = lambda address: sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8))
        assert word(base + 0x1800) == 4 * harts + 14, 'Lost or duplicate atomic update'
        old = [word(base + 0x2000 + hart * 64 + i * 8) for hart in range(harts) for i in range(4)]
        assert sorted(old) == list(range(14, 14 + 4 * harts)), 'Atomic old-value uniqueness'
    for hart, model in enumerate(models):
        if software:
            word = lambda address: sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8))
            assert word(software['results'] + 8 * hart) == 1 and successful_stores[hart] == 1, 'Software did not publish success exactly once'
            assert console[hart].decode('ascii') == software['expectedConsole'][hart], 'Missing or incorrect per-hart software console'
        elif hasattr(program, 'parallel_reads'):
            job = program.parallel_reads
            for offset, expected in ((0, job['rounds'] * (hart + 1)), (8, hart + 1)):
                address = job['results'] + 16 * hart + offset
                assert sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8)) == expected, 'Concurrent read checksum'
                assert effects[hart, address] == 1, 'Repeated concurrent read publication'
        elif hasattr(program, 'platform'):
            rounds, tasks = program.platform['rounds'], program.platform['rounds'] * harts
            word = lambda address: sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8))
            assert model.registers[23:25] == [rounds, rounds], 'Missing per-hart software or timer interrupt'
            assert causes[hart, 3] == rounds and causes[hart, 7] == rounds, 'Wrong platform interrupt causes'
            assert word(base + 0x1810) == tasks and model.registers[19] == tasks * (tasks + 1) // 2, 'Distributed task checksum'
            assert [word(base + 0x2400 + 8 * ticket) for ticket in range(tasks)] == list(range(1, tasks + 1)), 'Lost platform work'
            assert all(sum(effects[h, base + 0x2400 + 8 * ticket] for h in range(harts)) == 1 for ticket in range(tasks)), 'Repeated platform work'
            assert device.software[hart] == 0 and device.compare[hart] == MASK, 'Interrupt sources left asserted'
            assert not program.platform.get('wait') or sleep_cycles[hart] >= program.platform['rounds'], 'Missing real per-hart wait cycles'
        elif hasattr(program, 'synchronization'):
            word = lambda address: sum(memory.get(address + byte, 0) << (8 * byte) for byte in range(8))
            tasks = program.synchronization['rounds'] * harts
            if program.synchronization.get('dirtyCode'):
                assert sum(c['dirtyInstructionStores'] for c in cache_counts) == 1 and sum(c['instructionWritebacks'] for c in cache_counts) == 1, 'Missing dirty instruction write and fetch-triggered recall'
            assert word(base + 0x1810) == tasks, 'Work allocation count'
            assert [word(base + 0x2000 + 8 * ticket) for ticket in range(tasks)] == list(range(1, tasks + 1)), 'Lost or duplicate work'
            assert all(sum(effects[h, base + 0x2000 + 8 * ticket] for h in range(harts)) == 1 for ticket in range(tasks)), 'Repeated task execution'
            assert effects[hart, base + 0x1810] == program.synchronization['rounds'], 'Hart did not execute every work round'
            assert all(word(base + offset) == harts for offset in (0x1800, 0x1818, 0x1820, 0x1828, 0x1830)), 'Incomplete repeated barrier'
            assert word(base + 0x2400 + 64 * hart) == 3 and word(base + 0x2408 + 64 * hart) == 9, 'Instruction publication did not replace warmed code'
            assert model.registers[19] == tasks * (tasks + 1) // 2, 'Distributed work checksum'
        elif harts > 1 and 'atomic' in name and not hasattr(program, 'lrsc'):
            assert model.registers[18] == harts * (harts + 1) // 2, 'Release/acquire publication'
        elif harts > 1 and not hasattr(program, 'lrsc') and not hasattr(program, 'data_cache') and not name.startswith('user_'):
            assert model.registers[8] == (hart + 1) % harts + 1, 'Mailbox exchange did not complete'
            assert model.registers[12] == 1 and effects[hart, base + 0x5100] == 1, 'Private data or device effect'
            assert model.registers[17] == hart and (name == 'interrupt' or model.registers[19] == hart), 'Hart identity or read-only CSR'
        if name == 'protection':
            assert effects[hart, base + 0x1800] == int(hart != 0), 'PMP isolation'
        try:
            fetch_checks[hart].send(None)
        except StopIteration:
            pass
    if data_cache:
        assert all(count['accepted'] == count['completed'] and count['reads'] == count['hits'] + count['physicalReads'] - count['refillRetries'] + count['rejectedReads'] for count in cache_counts), 'Cached read accounting differs from architectural requests'
    if data_cache and hasattr(program, 'data_cache'):
        job = program.data_cache
        assert sum(count['reservedStores'] for count in cache_counts) >= job.get('minReservedStores', 0), 'Missing cache-local store overlapping a live reservation'
        for hart, count in enumerate(cache_counts):
            addresses = job.get('addresses', ())
            count['witnessHits'] = sum(hit_addresses[hart][address] for address in addresses) if addresses else count['hits']
            assert count['witnessHits'] >= job['minHits'] and all(hit_addresses[hart][address] for address in addresses), 'Missing target-address private-cache hits'
            assert count['expandedReads'] >= job.get('minExpandedReads', 0) and count['refillRetries'] >= job.get('minRefillRetries', 0), 'Missing authorized refill or exact-demand retry'
            assert count['expandedReads'] <= job.get('maxExpandedReads', count['expandedReads']), 'Unexpected widened data read'
            assert count['lineReads'] <= job.get('maxLineReads', count['lineReads']), 'Data line crossed a restricted subrange'
            if 'work' in job:
                begin, before = work_samples[hart, 0]
                end, after = work_samples[hart, 1]
                assert end > begin, 'Missing forward work interval'
                count['workCycles'] = end - begin
                for key in ('axiReadAddresses', 'axiReadBytes', 'hits'):
                    count['work' + key[0].upper() + key[1:]] = after.get(key, 0) - before.get(key, 0)
                wanted = job['work']['reads'][config.get('dCacheRefillBytes', 8)]
                assert count['workAxiReadAddresses'] == wanted, 'Fixed-work data address count differs from expected refill behavior'
                assert count['workAxiReadBytes'] == wanted * config.get('dCacheRefillBytes', 8), 'Fixed-work overfetch byte count'
        for hart, registers in enumerate(job.get('finalRegisters', [job.get('expectedRegisters', {})] * harts)):
            assert all(models[hart].registers[int(register)] == value for register, value in registers.items()), 'Cache program register result'
        if 'witnesses' in job:
            assert all(sum(memory.get(job['witnesses'] + hart * job['stride'] + 8 * index + byte, 0) << (8 * byte) for byte in range(8)) == value
                       for hart in range(harts) for index, value in enumerate(job['values'])), 'Coherence publication witness'
    assert maintenance is None, 'Unfinished physical writeback'
    assert not console_events, 'Console service was not printed'
    assert read_observed is None or read_observed == (read_peak, read_reordered), 'Read-concurrency counters differ from independent bus events'
    assert line_observed is None or line_observed[0] == line_peak, 'Line concurrency differs from independent accepted addresses'
    if getattr(program, 'parallel_reads', False):
        assert read_peak == 2 and read_reordered > 0, 'Missing simultaneous addresses or reordered read completion'
    if dual and getattr(program, 'load_window', False) and not writeback and read_slots:
        assert max(data_read_peak) == min(2, read_slots) and (read_slots == 1 or sum(data_read_reordered) > 0), 'Missing data-read capacity or reversed return'
    if dual and name == 'load_cancel' and not config.get('iCacheBytes') and read_slots >= 2:
        assert concurrent['instructionCancelDuringDataService'], 'No instruction cancellation with outstanding I/D owners'
    return dict(**(dict(results=results) if software_output else {}), **(dict(dataCache=[dict(count) for count in cache_counts]) if data_cache else {}), **(dict(translation=dict(translation_counts)) if translated else {}), events=events, activeHarts=len(finished), sources=sorted(sources),
                cycles=elapsed_cycles, transactions=transactions, axiTransactions=axi_transactions, lineReadBeats=line_beats,
                readConcurrency=dict(maxOutstanding=read_peak, reorderedResponses=read_reordered),
                dataReadConcurrency=dict(maxOutstanding=data_read_peak, reorderedResponses=data_read_reordered),
                lineConcurrency=dict(maxOutstanding=line_peak, overlapCycles=line_observed[1] if line_observed else 0),
                collidingTags=len(collisions), readsBeforePeerRetirement=overtaken, concurrency=dict(concurrent),
                platformCycles=device.cycle + 1 if device is not None else 0,
                sleepCycles=sleep_cycles,
                exclusiveReservations=reservation_max,
                conditionalStores={str(hart): dict(success=sc_results[hart, True], failure=sc_results[hart, False]) for hart in range(harts)},
                interrupts={str(hart): {str(bit): causes[hart, bit] for bit in (1, 3, 5, 7, 9, 11)} for hart in range(harts)},
                console=[text.decode('ascii') for text in console] if software else [],
                busCoverage=dict(zip(('awBeforeW', 'wBeforeAw', 'awWithW', 'arStall', 'awStall', 'wStall'), covers[0])))


def compare_multicore(binary, directory, config, selected=(), platform=False):
    harts, base = config['hartCount'], int(config['resetVector'])
    reports = []
    programs = ((name, platform_program(base, harts, local_interrupt_base(config), wait=name == 'platform_wait'))
                for name in ('platform', 'platform_wait')) if platform else multicore_cases(
        base, harts, bool(config['pmpEntries']), config['enableInterrupts'], config.get('enableUserMode', False), config.get('dCacheWriteback', False))
    if platform and config.get('enableUserMode'):
        programs = chain(programs,
            ((name, program) for name, program in multicore_cases(base, harts, bool(config['pmpEntries']), config['enableInterrupts'], True) if name == 'user_isolation'),
            ((name, program) for name, program in cases(base, bool(config['pmpEntries']), config['enableInterrupts'], True, local_interrupt_base(config)) if name == 'user_device'))
    for name, program in programs:
        if selected and name not in selected:
            continue
        image = directory / (name + '.hex')
        image.write_text('\n'.join(f'{program.memory.get(base + i, 0):02x}' for i in range(65536)) + '\n')
        first = len(reports)
        for seed in (1, 17, 2026):
            log = directory / f'{name}-{seed}.log'
            command = [binary, f'+IMAGE={image.resolve()}', f'+BASE={base:x}', f'+STOP={program.stop:x}', f'+SEED={seed}']
            command += [f'+FAULT_{kind.upper()}={address:x}' for kind, address in program.faults.items()]
            command += [f'+{key.upper()}={getattr(program, key, 0)}' for key in ('exclusive_failures', 'interference')]
            if hasattr(program, 'parallel_reads') or getattr(program, 'load_window', False):
                command.append('+REORDER_READS=1')
            if hasattr(program, 'data_cache') and 'work' in program.data_cache:
                command += [f'+WORK_{key.upper()}={program.data_cache["work"][key]:x}' for key in ('begin', 'end')]
            if name == 'load_cancel':
                command.append('+FIXED_READ_DELAY=128')
            if hasattr(program, 'interrupts'):
                command += [f'+IRQ_{key.upper()}={value:x}' if key == 'target' else f'+IRQ_{key.upper()}={value}'
                            for key, value in program.interrupts.items()]
            run(command, log)
            lines = log.read_text().splitlines()
            assert 'PASS' in lines, f'{name}: incomplete multicore run'
            reports.append(dict(test=name, seed=seed, performance=performance_metrics(lines, config),
                                **check_multicore(lines, config, program, name, atomic_metadata=True)))
        if harts > 1 and 'atomic' not in name and not any(hasattr(program, key) for key in ('synchronization', 'data_cache', 'parallel_reads')) and not platform and not name.startswith('user_'):
            concurrent = Counter()
            for report in reports[first:]:
                concurrent.update(report['concurrency'])
            assert concurrent['trapDuringPeerService'] and concurrent['redirectDuringPeerService'], f'{name}: missing concurrent trap or redirect {dict(concurrent)}'
        print(f'  {harts} harts, {name}: three shared-memory schedules', flush=True)
    assert reports, 'No selected multicore program'
    return dict(events=sum(report['events'] for report in reports), cases=reports)


def check_data_oracle():
    limit = defer_interrupt((0, 0, 0x3003), (0, 3, 0), None, True)
    assert defer_interrupt((1, 0, 0x13), (0, 3, 1), limit, False) == limit
    second = defer_interrupt((3, 0, 0x3003), (3, 5, 0), limit, True, 2)
    assert second == (5, 2, True) and defer_interrupt((4, 0, 0x13), (3, 5, 1), second, False, 2) == second
    interrupt_guards = []
    for label, record, group, previous, owned, maximum in (
            ('interruptNextGroup', (3, 0, 0x13), (3, 4, 0), limit, False, 1),
            ('interruptWithoutOwner', (0, 0, 0x13), (0, 1, 0), None, False, 1),
            ('interruptMultiplyFollower', (1, 0, 0x02000033), (0, 3, 1), limit, False, 1),
            ('interruptSingleReadLimit', (3, 0, 0x3003), (3, 5, 0), limit, True, 1),
            ('interruptThirdRead', (5, 0, 0x3003), (5, 6, 0), second, True, 2),
            ('interruptYoungerStore', (3, 0, 0x3023), (3, 4, 0), limit, True, 2),
            ('interruptDualMultiply', (5, 0, 0x02000033), (5, 6, 0), second, False, 2)):
        try:
            defer_interrupt(record, group, previous, owned, maximum)
        except AssertionError:
            interrupt_guards.append(label)
            continue
        raise AssertionError(f'Data oracle accepted {label}')
    config = dict(configuration(64), hartCount=2, enableInterrupts=False, dCacheBytes=8192, requireFetchIdentity=False)
    config['memoryRegions'][0]['dataCacheable'] = True
    instructions = (0x10000093, 0x0000b103, 0x0000b183, 0x00000013)
    memory = {4 * index + byte: (word >> (8 * byte)) & 255 for index, word in enumerate(instructions) for byte in range(4)}
    memory[0x100] = 42
    program = SimpleNamespace(memory=memory, faults={}, stop=12,
                              data_cache=dict(minHits=1, addresses=[0x100], expectedRegisters={'2': 42, '3': 42}))
    models = [Model(config, memory, {}) for _ in range(2)]
    lines = []

    def emit(hart, event):
        lines.append(f'HART {hart} {event}')

    def fetch(hart, index, complete=True):
        address, word = index * 4, instructions[index]
        emit(hart, f'REQUEST fetch {address:x} 4 0 {index:x}')
        emit(hart, 'ACCESS_PRIVILEGE 1')
        emit(hart, f'BUS fetch {address:x} 4 0')
        if complete:
            fetch_response(hart, index)

    def fetch_response(hart, index):
        address, word = index * 4, instructions[index]
        emit(hart, f'READ {address:x} 0 {word:x}')
        emit(hart, f'FETCH {address:x} 0 {word:x}')
        emit(hart, f'RESPONSE 0 {word:x} 0 {index:x}')

    def trace(hart):
        emit(hart, 'TRACE ' + ' '.join(f'{field:x}' for field in models[hart].step()))

    for hart in range(2):
        fetch(hart, 0)
        trace(hart)
        fetch(hart, 1)
        emit(hart, 'ARCH_DATA_REQUEST read 100 8 0 1 1 0')
        emit(hart, 'REQUEST read 100 8 0 1')
        emit(hart, 'ACCESS_PRIVILEGE 1')
        emit(hart, 'BUS read 100 8 0')
        emit(hart, 'READ 100 0 2a')
        emit(hart, 'RESPONSE 1 2a 0 1')
        emit(hart, 'ARCH_DATA_RESPONSE 2a 0 1')
        trace(hart)
        fetch(hart, 2)
        emit(hart, 'ARCH_DATA_REQUEST read 100 8 0 2 1 0')
    fetch(1, 3, complete=False)
    for hart in range(2):
        emit(hart, 'CACHE_SAMPLE 100 2a 2 8')
        emit(hart, 'ARCH_DATA_RESPONSE 2a 0 2')
        trace(hart)
    fetch(0, 3)
    fetch_response(1, 3)
    trace(0)
    trace(1)
    lines += ['COVER 1 1 1 1 1 1', 'EXCLUSIVE 0', 'PASS']
    report = check_multicore(lines, config, program, 'data_oracle', atomic_metadata=True)
    assert report['dataCache'][0]['hitsDuringPeerService'] == 1
    assert report['readConcurrency'] == dict(maxOutstanding=2, reorderedResponses=1)
    line_log = []
    for line in lines:
        hart = int(line.split()[1]) if line.startswith('HART ') else 0
        if line.endswith('ARCH_DATA_REQUEST read 100 8 0 1 1 0'):
            line = line[:-1] + '6'
        elif line.endswith('REQUEST read 100 8 0 1') or line.endswith('BUS read 100 8 0'):
            line = line.replace('read 100 8 ', 'read 100 64 ')
        elif line.endswith('READ 100 0 2a'):
            for chunk in range(8):
                address, value, last = 0x100 + 8 * chunk, 42 if chunk == 0 else 0, int(chunk == 7)
                line_log += [f'HART {hart} LINE_BEAT {address:x} 0 {value:x} {last:x}',
                             f'HART {hart} RESPONSE 1 {value:x} 0 1 {last:x}']
            continue
        elif line.endswith('RESPONSE 1 2a 0 1'):
            continue
        line_log.append(line)
    line_config = dict(config, dCacheRefillBytes=64)
    assert all(count['lineReads'] == 1 and count['lineBeats'] == 8 for count in
               check_multicore(line_log, line_config, program, 'data_oracle', atomic_metadata=True)['dataCache'])
    line_guards = check_burst_guards(line_log, line_config, program, 'data_oracle')
    completion = line_log.index('HART 0 ARCH_DATA_RESPONSE 2a 0 1')
    for label, inserted in (('unownedInvalidation', 'INVALIDATE 0 100 0'),
                            ('unjustifiedRetry', 'HART 0 REQUEST read 100 8 0 1')):
        try:
            check_multicore([*line_log[:completion], inserted, *line_log[completion:]], line_config, program, 'data_oracle', atomic_metadata=True)
        except AssertionError:
            line_guards.append(label)
            continue
        raise AssertionError(f'Line oracle accepted {label}')
    sample = lines.index('HART 0 CACHE_SAMPLE 100 2a 2 8')
    request = lines.index('HART 0 ARCH_DATA_REQUEST read 100 8 0 2 1 0')
    response = sample + 1
    physical = lines.index('HART 0 REQUEST fetch c 4 0 3')
    bus_response = lines.index('HART 0 READ c 0 13')
    mutations = dict(
        staleSample=(sample, ['HART 0 CACHE_SAMPLE 100 29 2 8']),
        sampleTag=(sample, ['HART 0 CACHE_SAMPLE 100 2a 3 8']),
        sampleSize=(sample, ['HART 0 CACHE_SAMPLE 100 2a 2 4']),
        duplicateSample=(sample, [lines[sample], lines[sample]]),
        missingRequest=(request, []),
        invalidRefillSpan=(request, ['HART 0 ARCH_DATA_REQUEST read 100 8 0 2 1 1']),
        unconfiguredLineGrant=(request, ['HART 0 ARCH_DATA_REQUEST read 100 8 0 2 1 6']),
        missingSample=(sample, []),
        wrongResponse=(response, ['HART 0 ARCH_DATA_RESPONSE 29 0 2']),
        missingResponse=(response, []),
        responseTag=(response, ['HART 0 ARCH_DATA_RESPONSE 2a 0 3']),
        repeatedPhysicalOwner=(physical, [lines[physical], lines[physical]]),
        overlappingWrite=(physical, ['HART 0 REQUEST write c 8 0 3']),
        earlyOwnerReuse=(bus_response, [lines[bus_response], lines[physical]]),
        wrongReadOwner=(bus_response, ['HART 1 READ c 0 12']))
    for name, (index, replacement) in mutations.items():
        try:
            check_multicore([*lines[:index], *replacement, *lines[index + 1:]], config, program, 'data_oracle', atomic_metadata=True)
        except AssertionError:
            continue
        raise AssertionError(f'Data oracle accepted {name}')
    program.data_cache['addresses'] = [0x108]
    try:
        check_multicore(lines, config, program, 'data_oracle', atomic_metadata=True)
    except AssertionError:
        return [*mutations, 'missingTargetHit', *interrupt_guards, *('dataLine' + label for label in line_guards)]
    raise AssertionError('Data oracle credited unrelated cache hits')


def load_software(image, config_path):
    from elftools.elf.elffile import ELFFile

    document = json.loads(config_path.read_text())
    config = document.get('parameters', document)
    for region in config['memoryRegions']:
        region.setdefault('dataCacheable', False)
    manifest = json.loads(image.with_name('manifest.json').read_text())
    assert hashlib.sha256(config_path.read_bytes()).hexdigest() == manifest['configurationHash'], 'Software configuration changed'
    assert hashlib.sha256(image.read_bytes()).hexdigest() == manifest['imageHash'], 'Software image changed'
    assert all(hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest for name, digest in manifest['sourceHashes'].items()), 'Stale software sources'
    base, harts, memory, spans, payloads = int(config['resetVector']), config['hartCount'], {}, [], []
    ram = next(r for r in config['memoryRegions'] if int(r['base']) == base and r['readable'] and r['writable'] and r['executable'] and not r['device'])
    memory_bytes = max(65536, int(ram['size']))
    assert memory_bytes <= 524288, 'Software RAM exceeds supported test profile'
    layout, code = manifest.get('layout', {}), []
    kind = layout.get('kind', 'runtime')
    assert kind in ('runtime', 'arch-test', 'zephyr'), 'Unknown software layout'
    with image.open('rb') as stream:
        elf = ELFFile(stream)
        assert elf.elfclass == 64 and elf.little_endian and elf['e_machine'] == 'EM_RISCV' and elf['e_type'] == 'ET_EXEC', 'Unsupported executable format'
        assert not elf['e_flags'] & 6 and (kind == 'arch-test' or not elf['e_flags'] & 1), 'Unsupported compressed or floating-point ABI'
        table = elf.get_section_by_name('.symtab')
        assert table is not None, 'Software symbols are missing'
        all_symbols = {symbol.name: symbol for symbol in table.iter_symbols() if symbol['st_shndx'] != 'SHN_UNDEF'}
        symbols = {name: symbol['st_value'] for name, symbol in all_symbols.items() if symbol['st_info']['bind'] in ('STB_GLOBAL', 'STB_WEAK')}
        assert symbols == manifest['symbols'], 'Software symbols changed'
        entry, alias = layout.get('entrySymbol', '_start'), layout.get('entryAlias', '_start')
        assert symbols[entry] == symbols[alias] == elf['e_entry'] == base, 'Invalid software entry'
        for segment in elf.iter_segments():
            if segment['p_type'] != 'PT_LOAD':
                continue
            address, size, files, flags = (segment[key] for key in ('p_paddr', 'p_memsz', 'p_filesz', 'p_flags'))
            assert segment['p_vaddr'] == address and files <= size and segment['p_offset'] + files <= image.stat().st_size, 'Invalid load segment'
            assert base <= address <= address + size <= base + memory_bytes, 'Load segment exceeds test memory'
            assert any(not r['device'] and int(r['base']) <= address and address + size <= int(r['base']) + int(r['size'])
                       and (not flags & 4 or r['readable']) and (not flags & 2 or r['writable']) and (not flags & 1 or r['executable'])
                       for r in config['memoryRegions']), 'Load segment violates memory attributes'
            assert all(address + size <= low or high <= address for low, high, _ in spans), 'Overlapping load segments'
            payload = segment.data()
            assert len(payload) == files, 'Truncated load segment'
            memory.update((address + offset, payload[offset] if offset < files else 0) for offset in range(size))
            spans.append((address, address + size, flags))
            payloads.append((address, address + files))
        if kind in ('arch-test', 'zephyr'):
            spec = importlib.util.spec_from_file_location('architecture_image', 'scripts/build_arch_tests.py')
            builder = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(builder)
            integer = 'rv64i2p1_zicsr2p0_zifencei2p0'
            architecture = 'rv64i2p1_a2p1_zicsr2p0_zifencei2p0_zaamo1p0_zalrsc1p0' if kind == 'zephyr' else integer
            code = builder.code_spans(elf, architecture, (integer,) if kind == 'zephyr' else ())
            if kind == 'arch-test':
                assert code == manifest['codeSpans'] and hashlib.sha256(table.data()).hexdigest() == manifest['symbolTableHash'], 'Executable mappings changed'
            implemented_csrs = Model(config, {}, {}).csrs
            for span in code:
                section = elf.get_section_by_name(span['section'])
                data = section.data()
                for address in range(span['start'], span['end'], 4):
                    word = int.from_bytes(data[address - section['sh_addr']:address - section['sh_addr'] + 4], 'little')
                    opcode, funct3, funct7 = word & 127, (word >> 12) & 7, word >> 25
                    assert opcode in (3, 15, 19, 23, 27, 35, 47, 51, 55, 59, 99, 103, 111, 115), 'Unsupported software instruction family'
                    assert not (opcode in (51, 59) and funct7 == 1), 'Software requires multiplication or division'
                    if opcode in (19, 27, 51, 59):
                        try:
                            integer_value(word, 0, 0)
                        except Fault as error:
                            raise AssertionError('Unsupported software integer encoding') from error
                    elif opcode in (3, 15, 35, 99, 103):
                        assert funct3 in {3: range(7), 15: (0, 1), 35: range(4), 99: (0, 1, 4, 5, 6, 7), 103: (0,)}[opcode], 'Unsupported software memory/control encoding'
                    elif opcode == 47:
                        assert kind == 'zephyr' and funct3 == 3 and word >> 27 in (0, 1, 2, 3, 8) and (word >> 27 != 2 or (word >> 20) & 31 == 0), 'Unsupported software atomic instruction'
                    elif opcode == 115:
                        update = funct3 & 3 == 1 or (word >> 15) & 31 != 0
                        assert word in (0x73, 0x30200073, 0x10500073) or (funct3 in (1, 2, 3, 5, 6, 7) and word >> 20 in implemented_csrs and (not update or word >> 30 != 3)), 'Unsupported software system instruction'
        if kind == 'zephyr':
            stacks = layout['stacks']
            actual = {name for name, symbol in all_symbols.items() if symbol['st_size'] and name.endswith(('_stack', '_stacks'))
                      and isinstance(symbol['st_shndx'], int) and elf.get_section(symbol['st_shndx'])['sh_flags'] & 3 == 3
                      and not elf.get_section(symbol['st_shndx'])['sh_flags'] & 4}
            assert {stack['symbol'] for stack in stacks} == actual, 'Missing or unrelated stack objects'
            for stack in stacks:
                symbol = all_symbols[stack['symbol']]
                count = harts if stack['symbol'].endswith('_stacks') else 1
                assert stack == dict(symbol=stack['symbol'], address=symbol['st_value'], size=symbol['st_size'], count=count, stride=symbol['st_size'] // count), 'Stack object layout changed'
                assert stack['size'] % count == 0
            assert all_symbols['__test_results']['st_size'] == 8 * harts, 'Result array has the wrong hart count'
        else:
            assert symbols['__hart_count'] == harts and symbols['__stack_top'] - symbols['__stack_bottom'] == harts * symbols['__stack_bytes']
            stacks = [dict(symbol='__stack_bottom', address=symbols['__stack_bottom'], size=harts * symbols['__stack_bytes'], count=harts, stride=symbols['__stack_bytes'])]
            assert base == symbols['__ram_base'] and symbols['__stack_top'] <= base + symbols['__ram_bytes'] <= base + memory_bytes
            if kind == 'arch-test':
                assert harts == 1 and stacks == layout['stacks'], 'Architecture test stack layout changed'
                low, high = symbols['__stack_bottom'], symbols['__stack_top']
                assert all(high <= start or end <= low for start, end in payloads), 'Loaded bytes overlap reserved stack'
                assert all(high <= span['start'] or span['end'] <= low for span in code), 'Code overlaps reserved stack'
    assert any(low <= base < high and flags & 1 for low, high, flags in spans), 'Entry is not executable'
    assert symbols['__test_halt'] % 4 == 0 and any(low <= symbols['__test_halt'] < high and flags & 1 for low, high, flags in spans)
    bss = symbols['__bss_start'], symbols['__bss_end']
    assert base <= bss[0] <= symbols['__test_results'] <= symbols['__test_results'] + 8 * harts <= bss[1] <= base + memory_bytes
    assert symbols['__test_results'] % 8 == 0 and all(memory.get(address) == 0 for address in range(*bss)), 'ELF BSS was not zero-filled'
    assert not layout or (layout['bssStart'], layout['bssEnd']) == bss
    ranges = []
    for stack in stacks:
        low, high = stack['address'], stack['address'] + stack['size']
        assert stack['size'] > 0 and low % 16 == 0 and high % 16 == 0 and bss[1] <= low < high <= base + memory_bytes
        if kind == 'zephyr':
            assert any(start <= low and high <= end and flags & 2 for start, end, flags in spans), 'Stack has no writable load allocation'
        assert any(not r['device'] and r['readable'] and r['writable'] and int(r['base']) <= low < high <= int(r['base']) + int(r['size']) for r in config['memoryRegions']), 'Stacks exceed writable RAM'
        assert all(high <= start or end <= low for start, end in ranges), 'Stack objects overlap'
        ranges.append((low, high))
    output = manifest.get('console', dict(transport='word', base=symbols.get('__console_base')))
    console = output['base']
    assert output['transport'] == 'word' and isinstance(console, int) and console % 4 == 0, 'Unsupported console transport'
    assert any(r['device'] and r['writable'] and not r['executable'] and not r['atomic'] and int(r['base']) <= console and
               console + 4 * harts <= int(r['base']) + int(r['size']) for r in config['memoryRegions']), 'Console mapping is invalid'
    expected = manifest.get('expectedConsole', [f'hart {hart:x} online\n' for hart in range(harts)])
    assert len(expected) == harts and all(text and text.endswith('\n') and text.isascii() for text in expected), 'Invalid expected console bytes'
    interrupt_causes = manifest.get('expectedInterruptCauses', [])
    assert isinstance(interrupt_causes, list) and all(type(cause) is int and 0 <= cause < 64 for cause in interrupt_causes), 'Invalid expected software interrupt causes'
    frequency = manifest.get('timebaseHz', 100000000)
    assert 0 < frequency <= 100000000 and 100000000 % frequency == 0, 'Unsupported software timebase'
    if kind == 'zephyr':
        assert frequency == 10000000 and local_interrupt_base(config) is not None and config['enableInterrupts']
        assert all(hashlib.sha256(image.with_name(name).read_bytes()).hexdigest() == digest for name, digest in manifest['generatedHashes'].items()), 'Generated software configuration changed'
    return config, SimpleNamespace(memory=memory, faults={}, stop=symbols['__test_halt'],
        software=dict(kind=kind, console=console, results=symbols['__test_results'], bss=bss, expectedConsole=expected, expectedInterruptCauses=interrupt_causes,
                      memoryBytes=memory_bytes, timebaseHz=frequency, timeTickCycles=100000000 // frequency,
                      idleCycles=4 * 100000000 // 100 if kind == 'zephyr' else 0)), manifest


def test_source_hashes():
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for name in
            ('verify.py', 'contracts.py', 'model.py', 'programs.py', 'core_tb.sv', 'memory_tb.sv')
            for p in (Path('test') / name,)}


def check_software_output(lines, config, program, console):
    report = check_multicore(lines, config, program, 'software', atomic_metadata=True, software_output=True)
    assert Counter(console.read_text().splitlines()) == Counter(f'[hart {hart}] {line}' for hart, text in enumerate(program.software['expectedConsole']) for line in text.splitlines()), 'Console log differs from software bytes'
    return report


def check_translation_guards(lines, config, program):
    cached_response, contexts = None, {}
    for index, line in enumerate(lines):
        fields = line.split()
        if not fields:
            continue
        hart = int(fields[1]) if fields[0] == 'HART' else 0
        if fields[0] == 'HART':
            fields = fields[2:]
        if fields[0] == 'TRANSLATE_REQUEST':
            contexts[hart, int(fields[1])] = dict(paged=int(fields[3], 16) != 3 and int(fields[6], 16) >> 60 == 8)
        elif fields[0] == 'WALK_REQUEST':
            contexts[hart, int(fields[3])]['walked'] = True
        elif fields[0] == 'ARCH_CANCEL' and (hart, 0) in contexts:
            contexts[hart, 0]['cancelled'] = True
        elif fields[0] == 'TRANSLATE_RESPONSE':
            context = contexts.pop((hart, int(fields[1])))
            if context['paged'] and not context.get('walked') and not context.get('cancelled') and not int(fields[3], 16):
                cached_response = index
                break
    mutations = (('contextPrivilege', 'TRANSLATE_REQUEST', 3, 1),
                 ('contextRoot', 'TRANSLATE_REQUEST', 6, 1),
                 ('physicalResult', 'TRANSLATE_RESPONSE', 2, 0x1000),
                 ('pteAddress', 'WALK_REQUEST', 1, 8),
                 ('pteOwner', 'WALK_REQUEST', 3, 1),
                 ('pteData', 'WALK_RESPONSE', 1, 1),
                 ('lsuAddress', 'ARCH_DATA_REQUEST', 2, 8))
    if config.get('tlbEntries'):
        assert cached_response is not None, 'Translation cache was not exercised'
        mutations += (('cachedResult', 'TRANSLATE_RESPONSE', 2, 8),)
    for name, event, field, mask in mutations:
        changed = list(lines)
        index = cached_response if name == 'cachedResult' else next(i for i, line in enumerate(lines) if line.split()[2 if line.startswith('HART ') else 0] == event)
        fields = changed[index].split()
        field += 2 if fields[0] == 'HART' else 0
        fields[field] = f'{int(fields[field], 16) ^ mask:x}'
        changed[index] = ' '.join(fields)
        try:
            check_multicore(changed, config, program, 'software', atomic_metadata=True, software_output=True)
        except AssertionError:
            continue
        raise AssertionError(f'Translation oracle accepted {name}')
    guards = [item[0] for item in mutations]
    if config.get('tlbEntries'):
        fields = next(line.split()[2:] if line.startswith('HART ') else line.split() for line in lines
                      if 'TRANSLATE_REQUEST' in line and int(line.split()[-3], 16) >> 60 == 8 and int(line.split()[-6], 16) != 3)
        context = dict(port=int(fields[1]), address=int(fields[2], 16), privilege=int(fields[3], 16),
                       kind='fetch' if int(fields[4]) else 'write' if int(fields[5]) else 'read',
                       satp=int(fields[6], 16), status=(int(fields[7]) << 18) | (int(fields[8]) << 19), reads=[])
        permitted = dict(config, pmpEntries=0)
        try:
            check_translation_result(context, (context['address'], False, 0), permitted, Model(permitted, {}, {}), [])
        except AssertionError:
            guards.append('fabricatedHit')
        else:
            raise AssertionError('Translation oracle accepted an unfilled cache hit')
    return guards


def software_schedule(task):
    binary, image, output, config, program, seed, transaction_limit, cycle_limit, timeout = task
    console, log = output / f'console-{seed}.log', output / f'software-{seed}.log'
    run([binary, f'+IMAGE={image.resolve()}', f'+BASE={int(config["resetVector"]):x}', f'+STOP={program.stop:x}', f'+SEED={seed}',
         f'+CONSOLE_BASE={program.software["console"]:x}', f'+CONSOLE_LOG={console.resolve()}',
         f'+RESULTS={program.software["results"]:x}', f'+TRANSACTIONS={transaction_limit}', f'+CYCLE_LIMIT={cycle_limit}'], log, timeout=timeout)
    return dict(seed=seed, consoleLog=str(console), performance=performance_metrics(log, config),
                **check_software_output(log, config, program, console))


def verify_software(args):
    args.output.mkdir(parents=True, exist_ok=True)
    summary_path = args.output / 'summary.json'
    summary_path.unlink(missing_ok=True)
    config, program, software = load_software(args.elf, args.config)
    software_manifest_hash = hashlib.sha256(args.elf.with_name('manifest.json').read_bytes()).hexdigest()
    if args.poison_bss:
        program.memory.update((address, 0xa5) for address in range(*program.software['bss']))
    test_hashes = test_source_hashes()
    config_path, rtl = args.output / 'input.json', args.output / 'rtl'
    config_path.write_text(json.dumps(config, indent=2) + '\n')
    if not args.use_generated:
        run(['build-ditdah-a1', '--trace', '--config', config_path, '--output', rtl], args.output / 'build.log')
    manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
    assert manifest['top'] == 'DitDahA1' and manifest['validationScope'] == 'system'
    assert all(manifest['parameters'][key] == value for key, value in config.items() if key != 'enableTrace'), 'Stale software RTL configuration'
    assert all(hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest for name, digest in manifest['sourceHashes'].items()), 'Stale software RTL sources'
    assert not args.burst_refill or config.get('enableBurstRefill'), 'Software configuration does not enable burst refill'
    assert args.dcache_refill_bytes == 8 or config.get('dCacheRefillBytes') == args.dcache_refill_bytes, 'Software configuration does not enable data line refill'
    assert not args.branch_prediction or config.get('enableBranchPrediction'), 'Software configuration does not enable branch prediction'
    assert not args.branch_predictor_entries or config.get('branchPredictorEntries') == args.branch_predictor_entries, 'Software predictor capacity mismatch'
    profile = program.software
    if profile['kind'] != 'runtime':
        assert args.software_transactions is not None, 'Set a measured or bounded --software-transactions probe budget'
    transaction_limit = args.software_transactions or 640 * config['hartCount']
    software_timeout = args.software_timeout or 600
    assert transaction_limit > 0
    cycle_limit = transaction_limit * 128 + profile['idleCycles'] if args.software_transactions else (50000 if config['hartCount'] == 1 else transaction_limit * 128)
    assert cycle_limit < 1 << 31, 'Software budget exceeds simulator counter width'
    binary = compile_tb(rtl, args.output, config['axiDataBits'], config['physicalAddressBits'], software=profile)
    base, harts = int(config['resetVector']), config['hartCount']
    image = args.output / 'software.hex'
    image.write_text('\n'.join(f'{program.memory.get(base + i, 0):02x}' for i in range(profile['memoryBytes'])) + '\n')
    tasks = [(binary, image, args.output, manifest['parameters'], program, seed, transaction_limit, cycle_limit, software_timeout)
             for seed in args.seeds]
    with ProcessPoolExecutor(max_workers=min(args.jobs, len(tasks))) as executor:
        reports = list(executor.map(software_schedule, tasks))
    guards = (check_translation_guards((args.output / f'software-{args.seeds[0]}.log').read_text().splitlines(), manifest['parameters'], program)
              if config.get('virtualAddressBits') == 39 and config['hartCount'] == 1 and not config['dCacheBytes'] else [])
    writeback_guards = check_writeback_guards((args.output / f'software-{args.seeds[0]}.log').read_text().splitlines(), manifest['parameters'], program, 'software') if config.get('dCacheWriteback') else []
    hashes = {**manifest['sourceHashes'], **test_hashes, **software['sourceHashes']}
    assert all(hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest for name, digest in hashes.items()), 'Sources changed during software verification'
    assert hashlib.sha256(args.elf.read_bytes()).hexdigest() == software['imageHash'], 'Image changed during software verification'
    assert hashlib.sha256(args.config.read_bytes()).hexdigest() == software['configurationHash'], 'Configuration changed during software verification'
    assert hashlib.sha256(args.elf.with_name('manifest.json').read_bytes()).hexdigest() == software_manifest_hash, 'Software manifest changed during verification'
    summary = dict(scope='implemented scalar software execution and console', sourceHashes=hashes,
        software=software, poisonBss=args.poison_bss, zeroLoadedBssBytes=program.software['bss'][1] - program.software['bss'][0],
        issueWidth=config.get('issueWidth', 1), hartCount=harts, axiDataBits=config['axiDataBits'], clockHz=100000000, timebaseHz=profile['timebaseHz'],
        cyclesPerTimeTick=profile['timeTickCycles'], transactionLimit=transaction_limit, cycleLimit=cycle_limit,
        idleCycles=profile['idleCycles'], wallSecondsPerSchedule=software_timeout, translationOracleGuards=guards, writebackOracleGuards=writeback_guards, cases=reports)
    summary_path.write_text(json.dumps(summary, indent=2) + '\n')
    print(f'{harts}-hart ELF software and console passed {len(reports)} bus schedules', flush=True)
    return summary


def verify_software_matrix(args):
    args.output.mkdir(parents=True, exist_ok=True)
    summary_path = args.output / 'summary.json'
    summary_path.unlink(missing_ok=True)
    document = json.loads(args.config.read_text())
    template = document.get('parameters', document)
    hashes = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in (args.config, Path('Makefile'))}
    profiles = []
    for harts in args.harts or (1, 2, 16):
        expected = None
        for selection in ((2, 4) if args.software_read_matrix else (8, 64) if args.software_refill_matrix else (1, 2, 3)):
            width = args.issue_width if args.software_refill_matrix or args.software_read_matrix else selection
            refill = selection if args.software_refill_matrix else args.dcache_refill_bytes
            directory = args.output / (f'd{selection}-h{harts}' if args.software_read_matrix else f'r{refill}-h{harts}' if args.software_refill_matrix else f'w{width}-h{harts}')
            directory.mkdir(parents=True, exist_ok=True)
            config_path = directory / 'input.json'
            config_path.write_text(json.dumps(dict(template, hartCount=harts, issueWidth=width, enableBranchPrediction=args.branch_prediction, branchPredictorEntries=args.branch_predictor_entries,
                axiDataBits=512 if harts == 16 else 64, iCacheBytes=args.icache_bytes,
                dCacheBytes=args.dcache_bytes, dCacheRefillBytes=refill, dCacheWriteback=args.dcache_writeback, enableBurstRefill=args.burst_refill, loadQueueEntries=args.load_queue_entries,
                **(dict(fabricReadSlots=selection) if args.software_read_matrix else {})), indent=2) + '\n')
            software = directory / 'software'
            run(['python3', 'scripts/build_software.py', '--config', config_path,
                 '--program', 'software/tests/integer.c', '--stack-bytes', '512',
                 '--console-base', '0x10000000', '--output', software], directory / 'software-build.log')
            run_args = SimpleNamespace(**{**vars(args), 'elf': software / 'software.elf',
                                         'config': config_path, 'output': directory / 'verification', 'dcache_refill_bytes': refill})
            summary = verify_software(run_args)
            payload = hashlib.sha256((run_args.output / 'software.hex').read_bytes()).hexdigest()
            for report in summary['cases']:
                if args.software_read_matrix:
                    assert report['readConcurrency']['maxOutstanding'] == selection, 'Software did not exercise the configured read capacity'
                if args.software_refill_matrix:
                    assert all(bool(count.get('lineReads')) == (refill == 64) and count['hits'] > 0 for count in report['dataCache']), 'Software did not consume the selected refill mode and cache hits'
                    if harts == 16 and refill == 64 and not args.dcache_writeback:
                        assert report['lineConcurrency']['maxOutstanding'] == 2 and report['lineConcurrency']['overlapCycles'] > 0, 'Software did not exercise simultaneous line reads'
                if args.dcache_writeback:
                    assert sum(count.get('cachedStores', 0) for count in report['dataCache']) > 0, 'Software did not exercise cached stores'
                observed = payload, report['results'], report['console']
                if expected is None:
                    expected = observed
                assert observed == expected, 'Loaded software, per-hart results or console differ across paired configurations or schedules'
            for path, digest in summary['sourceHashes'].items():
                assert path not in hashes or hashes[path] == digest, 'Mixed matrix source snapshots'
                hashes[path] = digest
            report_path = run_args.output / 'summary.json'
            profiles.append(dict(issueWidth=width, dCacheRefillBytes=refill, hartCount=harts, summary=str(report_path),
                                 summaryHash=hashlib.sha256(report_path.read_bytes()).hexdigest(),
                                 loadedMemoryHash=payload))
    assert all(hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest for path, digest in hashes.items()), 'Matrix sources changed'
    dimension = 'ReadSlots' if args.software_read_matrix else 'Refills' if args.software_refill_matrix else 'Widths'
    summary_path.write_text(json.dumps(dict(scope=f'same software across {dimension.lower()} for each hart count',
        sourceHashes=hashes, configurations=profiles, busSchedules=len(profiles) * len(args.seeds),
        **{key + dimension: True for key in ('loadedBytesEqualAcross', 'resultsEqualAcross', 'consoleEqualAcross')}), indent=2) + '\n')
    print(f'Software matrix passed {len(profiles)} configurations and {len(profiles) * len(args.seeds)} schedules', flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--width', type=int, choices=(64, 128, 256, 512), action='append')
    parser.add_argument('--issue-width', type=int, choices=(1, 2, 3), default=1)
    parser.add_argument('--load-queue-entries', type=int, choices=(1, 2), default=1)
    parser.add_argument('--fabric-read-slots', type=int, choices=(1, 2, 3, 4))
    parser.add_argument('--use-generated', action='store_true')
    parser.add_argument('--elf', type=Path)
    parser.add_argument('--software-matrix', action='store_true')
    parser.add_argument('--software-refill-matrix', action='store_true')
    parser.add_argument('--software-read-matrix', action='store_true')
    parser.add_argument('--config', type=Path)
    parser.add_argument('--poison-bss', action='store_true')
    parser.add_argument('--software-transactions', type=int)
    parser.add_argument('--software-timeout', type=int)
    parser.add_argument('--seeds', type=int, nargs='+', default=(1, 17, 2026))
    parser.add_argument('--jobs', type=int, choices=range(1, 17), default=1)
    parser.add_argument('--user-mode', action='store_true')
    parser.add_argument('--supervisor-mode', action='store_true')
    parser.add_argument('--sv39', action='store_true')
    parser.add_argument('--burst-refill', action='store_true')
    parser.add_argument('--branch-prediction', action='store_true')
    parser.add_argument('--branch-predictor-entries', type=int, choices=(0, 8, 16), default=0)
    parser.add_argument('--tlb-entries', type=int, choices=(0, 2, 4), default=0)
    parser.add_argument('--multicore-only', action='store_true')
    parser.add_argument('--platform-only', action='store_true')
    parser.add_argument('--harts', type=int, choices=(1, 2, 3, 16), action='append')
    parser.add_argument('--output', type=Path, default=Path('result/verify'))
    parser.add_argument('--interrupts', action='store_true', help='Run only enabled interrupt profiles')
    parser.add_argument('--pmp-entries', type=int, choices=(0, 16))
    parser.add_argument('--icache-bytes', type=int, choices=(0, 8192, 16384, 32768, 65536), default=0)
    parser.add_argument('--dcache-bytes', type=int, choices=(0, 8192), default=0)
    parser.add_argument('--dcache-writeback', action='store_true')
    parser.add_argument('--dcache-refill-bytes', type=int, choices=(8, 64), default=8)
    parser.add_argument('--case', dest='selected', action='append', default=[])
    parser.add_argument('--traffic-baseline', type=Path)
    parser.add_argument('--prediction-baseline', type=Path)
    args = parser.parse_args()
    if args.fabric_read_slots is not None and args.elf:
        parser.error('Software read slots use their configuration')
    if args.burst_refill and not args.icache_bytes and not args.elf:
        parser.error('--burst-refill requires --icache-bytes')
    if (args.dcache_refill_bytes == 64 or args.software_refill_matrix) and not args.dcache_bytes and not args.elf:
        parser.error('Data line refill requires --dcache-bytes')
    if args.dcache_writeback and not args.dcache_bytes and not args.elf:
        parser.error('Writeback requires --dcache-bytes')
    matrix = args.software_matrix or args.software_refill_matrix or args.software_read_matrix
    if sum((args.software_matrix, args.software_refill_matrix, args.software_read_matrix)) > 1:
        parser.error('Select one software matrix dimension')
    if args.software_read_matrix and args.harts != [16]:
        parser.error('Read capacity software requires --harts 16')
    if args.tlb_entries and not args.sv39:
        parser.error('--tlb-entries requires --sv39')
    if args.sv39:
        args.supervisor_mode = True
    if args.supervisor_mode:
        args.user_mode = args.interrupts = True
    if len(set(args.seeds)) != len(args.seeds) or any(not 0 < seed < 1 << 32 for seed in args.seeds):
        parser.error('--seeds requires distinct nonzero 32-bit integers')
    if not (args.elf or matrix) and (args.jobs != 1 or tuple(args.seeds) != (1, 17, 2026)):
        parser.error('--seeds and --jobs require --elf')
    if args.software_timeout is not None and (not (args.elf or matrix) or args.software_timeout <= 0):
        parser.error('--software-timeout requires --elf and a positive integer')
    if matrix:
        if args.elf or not args.config or args.harts and (len(set(args.harts)) != len(args.harts) or any(hart not in (1, 2, 16) for hart in args.harts)):
            parser.error('Software matrix requires --config, no --elf, and distinct hart counts from 1, 2, 16')
        verify_software_matrix(args)
        return
    assert bool(args.elf) == bool(args.config), 'ELF execution requires its configuration'
    assert not args.poison_bss or args.elf, 'BSS poisoning requires an ELF image'
    if args.elf:
        verify_software(args)
        return
    assert not (args.multicore_only and args.platform_only), 'Select one shared-memory profile family'
    args.output.mkdir(parents=True, exist_ok=True)
    summary_path = args.output / 'summary.json'
    summary_path.unlink(missing_ok=True)
    test_hashes = test_source_hashes()
    summary = {'scope': 'implemented scalar subset; simulation and assertions', 'selectedCases': args.selected,
               'fetchOracleGuards': check_fetch_oracle(), 'dataOracleGuards': check_data_oracle(), 'configurations': []}
    frozen_sources = None

    def freeze_sources(manifest):
        nonlocal frozen_sources
        assert manifest.get('sourceHashes'), 'Generated RTL has no source provenance'
        if frozen_sources is None:
            frozen_sources = manifest['sourceHashes']
        assert manifest['sourceHashes'] == frozen_sources, 'Mixed generated source snapshots'

    core_profiles = {}
    profiles = [(width, entries, False) for entries in ((args.pmp_entries,) if args.pmp_entries is not None else (0, 16))
                for width in args.width or (64, 128, 256, 512) if entries == 0 or width in (64, 512)]
    if args.interrupts or args.multicore_only or args.platform_only:
        profiles = []
    profiles += [(width, entries, True) for width, entries in (() if args.multicore_only or args.platform_only else ((64, 0), (512, 16)))
                 if (not args.width or width in args.width) and (args.pmp_entries is None or entries == args.pmp_entries)]
    if args.supervisor_mode and not (args.multicore_only or args.platform_only):
        profiles = [(width, args.pmp_entries if args.pmp_entries is not None else 16, True)
                    for width in args.width or (64, 512)]
    assert profiles or args.multicore_only or args.platform_only, 'No configurations match the requested profile'
    for width, entries, interrupts in profiles:
        directory = args.output / f'{"irq-" if interrupts else ""}{"pmp16-" if entries else ""}axi{width}'
        directory.mkdir(parents=True, exist_ok=True)
        config = configuration(width)
        config.update(issueWidth=args.issue_width, loadQueueEntries=args.load_queue_entries, pmpEntries=entries, enableInterrupts=interrupts, iCacheBytes=args.icache_bytes, dCacheBytes=args.dcache_bytes, dCacheRefillBytes=args.dcache_refill_bytes, dCacheWriteback=args.dcache_writeback, tlbEntries=args.tlb_entries, enableBurstRefill=args.burst_refill, enableBranchPrediction=args.branch_prediction, branchPredictorEntries=args.branch_predictor_entries)
        if args.fabric_read_slots is not None:
            config['fabricReadSlots'] = args.fabric_read_slots
        config['memoryRegions'][0]['dataCacheable'] = bool(args.dcache_bytes)
        if args.user_mode:
            config['enableUserMode'] = True
        if args.supervisor_mode:
            config['enableSupervisorMode'] = True
        if args.sv39:
            config['virtualAddressBits'] = 39
        config_path = directory / 'input.json'
        config_path.write_text(json.dumps(config, indent=2) + '\n')
        rtl = directory / 'rtl'
        if not args.use_generated:
            print(f'Generating AXI{width} RTL', flush=True)
            run(['build-ditdah-a1', '--trace', '--config', config_path, '--output', rtl], directory / 'build.log')
        manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
        freeze_sources(manifest)
        assert manifest['top'] == 'DitDahA1' and manifest['validationScope'] == 'system'
        assert manifest.get('sourceHashes'), 'Generated RTL has no source provenance'
        for name, digest in manifest['sourceHashes'].items():
            assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, f'Stale RTL source: {name}'
        for key, value in config.items():
            assert manifest['parameters'][key] == value, f'Stale RTL configuration: {key}'
        interface_contracts = verify_contracts(rtl, directory / 'contracts')
        storage = verify_storage(rtl, directory / 'storage')
        binary = compile_tb(rtl, directory, width, config['physicalAddressBits'])
        print(f'Checking AXI{width}', flush=True)
        report = compare(binary, directory, manifest['parameters'], selected=args.selected)
        report['interfaceContracts'] = interface_contracts
        report['instructionStorage'] = storage
        report.update(issueWidth=args.issue_width, loadQueueEntries=args.load_queue_entries, axiDataBits=width, physicalAddressBits=config['physicalAddressBits'], pmpEntries=entries, enableInterrupts=interrupts, iCacheBytes=args.icache_bytes, dCacheBytes=args.dcache_bytes, dCacheRefillBytes=args.dcache_refill_bytes, dCacheWriteback=args.dcache_writeback,
                      branchPredictorEntries=args.branch_predictor_entries, enableBranchPrediction=args.branch_prediction, parameters=manifest['parameters'])
        summary['configurations'].append(report)
        core = directory / 'core'
        core_config = dict(config, axiDataBits=256, dCacheBytes=0, dCacheRefillBytes=8, dCacheWriteback=False)
        core_key = json.dumps(core_config, sort_keys=True)
        if core_key in core_profiles:
            report['coreReuse'] = core_profiles[core_key]
            continue
        core.mkdir(exist_ok=True)
        core_input = core / 'input.json'
        core_input.write_text(json.dumps(core_config, indent=2) + '\n')
        if not args.use_generated:
            run(['build-ditdah-a1', '--top', 'DitDahA1Core', '--trace', '--config', core_input, '--output', core / 'rtl'], core / 'build.log')
        core_manifest = json.loads((core / 'rtl/ditdah_a1_config.json').read_text())
        assert core_manifest['top'] == 'DitDahA1Core' and core_manifest['validationScope'] == 'core'
        assert all(core_manifest['parameters'][k] == v for k, v in core_config.items()), 'Stale Core configuration'
        assert core_manifest['sourceHashes'] == manifest['sourceHashes'], 'Stale Core sources'
        assert not (core / 'rtl/DitDahA1Axi.sv').exists(), 'AXI dependency in standalone Core'
        binary = compile_tb(core / 'rtl', core, width, config['physicalAddressBits'], 'memory_tb',
                            Path('test/memory_tb.sv').resolve(), [(rtl / 'DitDahA1Memory.sv').resolve()])
        report['core'] = compare(binary, core, core_manifest['parameters'], 'memory', args.selected)
        core_profiles[core_key] = str(core)
    if args.multicore_only or args.platform_only:
        shared_profiles = ((1, 64, 0, True), (2, 64, 0, True), (3, 128, 16, True), (16, 512, 16, True)) if args.platform_only else (
            (2, 64, 0, False), (2, 512, 16, True), (3, 64, 16, True), (16, 512, 16, True))
        if args.multicore_only and args.harts and args.width and args.pmp_entries is not None:
            shared_profiles = tuple((h, w, args.pmp_entries, bool(args.interrupts or args.pmp_entries))
                                    for h in args.harts for w in args.width)
        for harts, width, entries, interrupts in shared_profiles:
            if (args.harts and harts not in args.harts) or (args.width and width not in args.width):
                continue
            if args.pmp_entries is not None and entries != args.pmp_entries:
                continue
            directory = args.output / f'harts{harts}-axi{width}'
            directory.mkdir(parents=True, exist_ok=True)
            config = dict(configuration(width), issueWidth=args.issue_width, loadQueueEntries=args.load_queue_entries, hartCount=harts, pmpEntries=entries, enableInterrupts=interrupts, iCacheBytes=args.icache_bytes, dCacheBytes=args.dcache_bytes, dCacheRefillBytes=args.dcache_refill_bytes, dCacheWriteback=args.dcache_writeback, tlbEntries=args.tlb_entries, enableBurstRefill=args.burst_refill, enableBranchPrediction=args.branch_prediction, branchPredictorEntries=args.branch_predictor_entries)
            if args.fabric_read_slots is not None:
                config['fabricReadSlots'] = args.fabric_read_slots
            config['memoryRegions'][0]['dataCacheable'] = bool(args.dcache_bytes)
            if args.user_mode:
                config['enableUserMode'] = True
            if args.supervisor_mode:
                config.update(enableSupervisorMode=True, enableInterrupts=True)
            if args.sv39:
                config['virtualAddressBits'] = 39
            if args.platform_only:
                local_base = int(config['resetVector']) + 0x10000
                config.update(localInterruptBase=str(local_base))
                config['memoryRegions'].append(dict(base=str(local_base), size=str(65536), readable=True,
                                                    writable=True, executable=False, device=True, atomic=False, dataCacheable=False))
            config_path, rtl = directory / 'input.json', directory / 'rtl'
            config_path.write_text(json.dumps(config, indent=2) + '\n')
            if not args.use_generated:
                run(['build-ditdah-a1', '--trace', '--config', config_path, '--output', rtl], directory / 'build.log')
            manifest = json.loads((rtl / 'ditdah_a1_config.json').read_text())
            freeze_sources(manifest)
            assert manifest['implementation']['hartCount'] == harts
            assert all(manifest['parameters'][key] == value for key, value in config.items())
            assert all(hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest for name, digest in manifest['sourceHashes'].items())
            binary = compile_tb(rtl, directory, width, config['physicalAddressBits'])
            report = compare_multicore(binary, directory, manifest['parameters'], args.selected, args.platform_only)
            report['interfaceContracts'] = verify_contracts(
                rtl, directory / 'contracts', modules=('DitDahA1MemoryArbiter', 'DitDahA1MemoryFabric', *(('DitDahA1ReadQueue',) if config.get('fabricReadSlots') or harts > 1 else ()),
                                                      *(('DitDahA1Backend', 'DitDahA1Lsu') if args.load_queue_entries == 2 and not args.sv39 else ()),
                                                      *(('DitDahA1DataCache', 'DitDahA1Coherence') if args.dcache_bytes else ()),
                                                      *(('DitDahA1LocalInterrupts',) if args.platform_only else ())))
            report['instructionStorage'] = verify_storage(rtl, directory / 'storage')
            report.update(issueWidth=args.issue_width, loadQueueEntries=args.load_queue_entries, hartCount=harts, axiDataBits=width, pmpEntries=entries, enableInterrupts=interrupts, iCacheBytes=args.icache_bytes, dCacheBytes=args.dcache_bytes, dCacheRefillBytes=args.dcache_refill_bytes, dCacheWriteback=args.dcache_writeback)
            if not args.icache_bytes and not args.dcache_bytes and not args.platform_only:
                for count in ((15, 16) if harts == 16 else (harts,)):
                    Path(f'result/harts{count}-input.json').write_text(json.dumps(dict(config, hartCount=count), indent=2) + '\n')
            summary['configurations'].append(report)
        assert summary['configurations'], 'No selected multicore profile'
    else:
        frontend_config = dict(configuration(128), issueWidth=2, axiDataBits=512, iCacheBytes=8192, enableInterrupts=True)
        Path('result/frontend-input.json').write_text(json.dumps(frontend_config, indent=2) + '\n')
        fabric_config = dict(frontend_config, resetVector='2', hartCount=16, virtualAddressBits=48, pmpEntries=16)
        Path('result/fabric-input.json').write_text(json.dumps(fabric_config, indent=2) + '\n')
        backend_config = dict(fabric_config, issueWidth=1, pmpEntries=0, enableInterrupts=False, iCacheBytes=0)
        Path('result/backend-input.json').write_text(json.dumps(backend_config, indent=2) + '\n')
    assert frozen_sources
    for name, digest in frozen_sources.items():
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, f'Source changed during verification: {name}'
    summary['sourceHashes'] = dict(frozen_sources)
    for name, digest in test_hashes.items():
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, f'Test changed during verification: {name}'
    summary['sourceHashes'].update(test_hashes)
    if args.traffic_baseline:
        baseline = json.loads(args.traffic_baseline.read_text())
        assert args.icache_bytes and baseline['sourceHashes'] == summary['sourceHashes'], 'Traffic baseline uses different sources'
        comparison = []
        keys = ('axiDataBits', 'physicalAddressBits', 'pmpEntries', 'enableInterrupts')
        for profile in summary['configurations']:
            previous = [entry for entry in baseline['configurations'] if not entry['iCacheBytes']
                        and all(entry[key] == profile[key] for key in keys)]
            assert len(previous) == 1, 'Missing matching uncached traffic profile'
            for observed in profile['cases']:
                if observed['test'] != 'pipeline_reuse':
                    continue
                wanted = next(entry for entry in previous[0]['cases'] if entry['test'] == observed['test'] and entry['seed'] == observed['seed'])
                old, new = wanted['fetches']['accepted'], observed['fetches']['accepted']
                assert new < old, 'Repeated instruction hits did not reduce external fetches'
                comparison.append(dict(**{key: profile[key] for key in keys}, seed=observed['seed'],
                                       uncachedFetches=old, cachedFetches=new,
                                       uncachedCycles=wanted['cycles'], cachedCycles=observed['cycles']))
        assert comparison, 'No repeated workload for traffic comparison'
        summary['instructionCacheComparison'] = comparison
    if args.prediction_baseline:
        baseline = json.loads(args.prediction_baseline.read_text())
        assert args.branch_predictor_entries and baseline['sourceHashes'] == summary['sourceHashes'], 'Prediction baseline uses different sources'
        comparison = []
        for current, previous in zip(summary['configurations'], baseline['configurations'], strict=True):
            assert previous['branchPredictorEntries'] == 0 and previous['enableBranchPrediction']
            assert current['parameters'] | dict(branchPredictorEntries=0) == previous['parameters'], 'Prediction window configuration differs'
            for transport in ('axi', 'core'):
                observed = current if transport == 'axi' else current['core']
                expected = previous if transport == 'axi' else previous['core']
                for new, old in zip(observed['cases'], expected['cases'], strict=True):
                    assert (new['test'], new['seed'], new['events']) == (old['test'], old['seed'], old['events'])
                    if new['test'] in ('branch_window', 'return_window'):
                        assert new['pipeline']['workCycles'] < old['pipeline']['workCycles'], 'Prediction did not improve the fixed window'
                        comparison.append(dict(test=new['test'], seed=new['seed'], transport=transport, before=old['pipeline']['workCycles'], after=new['pipeline']['workCycles']))
        assert comparison, 'Missing prediction window'
        summary['predictionComparison'] = comparison
    summary_path.write_text(json.dumps(summary, indent=2) + '\n')
    print('Scalar RTL verification passed', flush=True)


if __name__ == '__main__':
    main()
