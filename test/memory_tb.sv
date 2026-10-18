// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
`timescale 1ns/1ps
typedef struct packed {
  logic [63:0] address, data;
  logic [2:0] size;
  logic [7:0] mask, tag;
  logic write, fetch, privileged, atomic;
  logic [4:0] atomicOperation;
  logic scEligible;
} request_t;
typedef struct packed { logic [63:0] data; logic fault; logic [7:0] tag; } response_t;
interface memory_port;
  logic request_ready, request_valid, response_ready, response_valid = 0;
  request_t request;
  response_t response = '0;
endinterface
`define PORT(P, B) \
  .P``_request_ready(B.request_ready), .P``_request_valid(B.request_valid), \
  .P``_request_bits_address(B.request.address), .P``_request_bits_data(B.request.data), \
  .P``_request_bits_size(B.request.size), .P``_request_bits_mask(B.request.mask), \
  .P``_request_bits_tag(B.request.tag), .P``_request_bits_write(B.request.write), \
  .P``_request_bits_fetch(B.request.fetch), .P``_request_bits_atomic(B.request.atomic), \
  .P``_request_bits_privileged(B.request.privileged), \
  .P``_request_bits_atomicOperation(B.request.atomicOperation), .P``_request_bits_scEligible(B.request.scEligible), .P``_response_ready(B.response_ready), \
  .P``_response_valid(B.response_valid), .P``_response_bits_data(B.response.data), \
  .P``_response_bits_fault(B.response.fault), .P``_response_bits_tag(B.response.tag)
`undef CORE_TRACE
`define CORE_TRACE dut.backend.dV
module memory_tb;
  logic clock = 0, reset = 1;
  always #5 clock = ~clock;
  memory_port core_port[2](), physical_port[2]();
  logic status_trap, status_busy, status_sleep;
  DitDahA1Core dut(.clock(clock), .reset(reset), .hartId(4'b0), `PORT(instruction, core_port[0]),
    `PORT(data, core_port[1]),
`ifdef ENABLE_INTERRUPTS
    .interrupts_software(irq_levels[0]), .interrupts_timer(irq_levels[1]), .interrupts_external(irq_levels[2]),
`endif
    .status_trap(status_trap), .status_busy(status_busy), .status_sleep(status_sleep));
  `include "fetch_observers.svh"
`ifdef ENABLE_INTERRUPTS
  logic [2:0] irq_levels;
  logic irq_activate, irq_ack = 0, irq_retired = 0;
  integer irq_mode;
  logic [63:0] irq_target;
  interrupt_driver interrupts(clock, reset, irq_activate, irq_ack, irq_levels, irq_mode, irq_target);
  always_comb case (irq_mode)
    0: irq_activate = 1;
    1, 2, 3: irq_activate = core_port[1].request_valid && core_port[1].request.write;
    4: irq_activate = service[1].pending && !service[1].captured.write;
`ifdef ICACHE
    5: irq_activate = architectural_fetch_busy[0] && architectural_fetch_pc[0] == irq_target && `CORE_TRACE.pipelineOccupancy == 0;
`else
    5: irq_activate = service[0].pending && service[0].captured.address == irq_target && `CORE_TRACE.pipelineOccupancy == 0;
`endif
    6: irq_activate = dut.backend.multiply.busy;
    7: irq_activate = irq_retired;
    8: irq_activate = service[1].pending && service[1].captured.atomic;
    default: irq_activate = 0;
  endcase
  always @(posedge clock) irq_retired <= !reset && `CORE_TRACE.traceValid && `CORE_TRACE.tracePc == irq_target;
  always @(posedge clock) irq_ack <= !reset && physical_port[1].request_valid && physical_port[1].request_ready &&
    physical_port[1].request.write && physical_port[1].request.address == base_address + 'h5008;
`endif
  byte unsigned memory [0:65535];
  string image;
  logic [63:0] base_address, stop_pc, fault_fetch, fault_read, fault_write, fault_exclusive;
  logic [31:0] random_state;
  logic [1:0] core_pending = 0;
  integer cycles = 0, overlap = 0, pipeline_max = 0, dependency_stalls = 0;
  function automatic logic [63:0] access_mask(input logic [2:0] size);
    return 64'hffffffffffffffff >> (64 - (8 << size));
  endfunction
  initial begin
    if (!$value$plusargs("IMAGE=%s", image)) $fatal(1, "Missing image");
    if (!$value$plusargs("BASE=%h", base_address)) $fatal(1, "Missing base");
    if (!$value$plusargs("STOP=%h", stop_pc)) $fatal(1, "Missing stop");
    if (!$value$plusargs("SEED=%d", random_state)) random_state = 1;
    if (!$value$plusargs("FAULT_FETCH=%h", fault_fetch)) fault_fetch = '1;
    if (!$value$plusargs("FAULT_READ=%h", fault_read)) fault_read = '1;
    if (!$value$plusargs("FAULT_WRITE=%h", fault_write)) fault_write = '1;
    if (!$value$plusargs("FAULT_EXCLUSIVE=%h", fault_exclusive)) fault_exclusive = '1;
    for (integer i = 0; i < 65536; i++) memory[i] = 0;
    $readmemh(image, memory);
    repeat (3) @(negedge clock);
    reset = 0;
  end
  always @(negedge clock) begin
    random_state = random_state ^ (random_state << 13);
    random_state = random_state ^ (random_state >> 17);
    random_state = random_state ^ (random_state << 5);
  end
  for (genvar p = 0; p < 2; p++) begin: service
    DitDahA1Memory permissions(.clock(clock), .reset(reset),
      `PORT(upstream, core_port[p]), `PORT(downstream, physical_port[p]));
    logic pending = 0;
    request_t captured;
    logic [63:0] atomic_data, atomic_result, updated_data, reservation_address;
    logic reservation_valid = 0, service_fault, successful_write;
    logic [2:0] reservation_size;
    logic [7:0] owner_tag;
    integer delay = 0, stalls = 0, delayed = 0, rejected = 0, wraps = 0, requests = 0;
    always @(negedge clock) begin
      physical_port[p].request_ready = !reset && !pending && !physical_port[p].response_valid && random_state[p];
`ifdef ENABLE_INTERRUPTS
      if (p == 1 && interrupts.mask != 0 && !interrupts.started && irq_mode >= 1 && irq_mode <= 3)
        physical_port[p].request_ready = 0;
`endif
    end
    always @(posedge clock) if (!reset) begin
      if (core_port[p].request_valid && !core_port[p].request_ready) stalls <= stalls + 1;
      if (core_port[p].request_valid && core_port[p].request_ready) begin
        if (core_pending[p]) $fatal(1, "Overlapping requests on one port");
        if (core_port[p].request.fetch != (p == 0) ||
            (p == 0 ? core_port[p].request.size != 2 : core_port[p].request.size > 3) ||
            core_port[p].request.mask != (core_port[p].request.write ? ((1 << (1 << core_port[p].request.size)) - 1) : 0) ||
            (p == 0 && (core_port[p].request.write || core_port[p].request.atomic)) ||
            (core_port[p].request.atomic && (core_port[p].request.size != 3 ||
             core_port[p].request.write != (core_port[p].request.atomicOperation != 2)))) $fatal(1, "Core request attributes");
        core_pending[p] <= 1;
        owner_tag <= core_port[p].request.tag;
        requests <= requests + 1;
        if (p == 0 && requests != 0 && core_port[p].request.tag == 0) wraps <= wraps + 1;
        if (!physical_port[p].request_valid) rejected <= rejected + 1;
        $display("REQUEST %s %016h %0d %016h", core_port[p].request.atomic ? "atomic" : (p == 0 ? "fetch" : (core_port[p].request.write ? "write" : "read")),
          core_port[p].request.address, 1 << core_port[p].request.size,
          core_port[p].request.write ? core_port[p].request.data & access_mask(core_port[p].request.size) : 64'b0);
        $display("ACCESS_PRIVILEGE %01h", core_port[p].request.privileged);
        if (core_port[p].request.atomic)
          $display("ATOMIC %02h %01h", core_port[p].request.atomicOperation, core_port[p].request.scEligible);
      end
      if (core_port[p].response_valid && core_port[p].response_ready) begin
        if (!core_pending[p] || core_port[p].response.tag != owner_tag) $fatal(1, "Response ownership");
        core_pending[p] <= 0;
      end
      if (physical_port[p].request_valid && physical_port[p].request_ready) begin
        if (pending || physical_port[p].response_valid) $fatal(1, "Overlapping physical requests");
        if (physical_port[p].request.address < base_address || physical_port[p].request.address > base_address + 65536 - (1 << physical_port[p].request.size)) $fatal(1, "Memory bounds");
        captured <= physical_port[p].request;
        pending <= 1;
        delay <= p == 0 ? integer'(random_state[5:4]) : 32 + integer'(random_state[7:4]);
`ifdef ENABLE_INTERRUPTS
        if (p == 0 && irq_mode == 5 && physical_port[p].request.address == irq_target) delay <= 48;
`endif
        physical_port[p].response.tag <= physical_port[p].request.tag;
        service_fault = physical_port[p].request.address == (p == 0 ? fault_fetch : (physical_port[p].request.write ? fault_write : fault_read));
        if (physical_port[p].request.atomic) begin
          case (physical_port[p].request.atomicOperation)
            2: service_fault = physical_port[p].request.address == fault_read || physical_port[p].request.address == fault_exclusive;
            3: service_fault = physical_port[p].request.scEligible && physical_port[p].request.address == fault_write;
            default: service_fault = service_fault || physical_port[p].request.address == fault_read || physical_port[p].request.address == fault_exclusive;
          endcase
        end
        physical_port[p].response.fault <= service_fault;
        $display("BUS %s %016h %0d %016h", physical_port[p].request.atomic ? "atomic" : (p == 0 ? "fetch" : (physical_port[p].request.write ? "write" : "read")),
          physical_port[p].request.address, 1 << physical_port[p].request.size,
          physical_port[p].request.write ? physical_port[p].request.data & access_mask(physical_port[p].request.size) : 64'b0);
        atomic_data = 0;
        if (physical_port[p].request.atomic)
          for (integer i = 0; i < 8; i++) atomic_data[i*8 +: 8] = memory[integer'(physical_port[p].request.address - base_address) + i];
        atomic_result = atomic_data;
        updated_data = physical_port[p].request.data;
        successful_write = physical_port[p].request.write && !service_fault;
        if (physical_port[p].request.atomic) begin
          case (physical_port[p].request.atomicOperation)
            0: updated_data = atomic_data + physical_port[p].request.data;
            1: updated_data = physical_port[p].request.data;
            8: updated_data = atomic_data | physical_port[p].request.data;
            2: if (!service_fault) begin
              reservation_valid <= 1;
              reservation_address <= physical_port[p].request.address;
              reservation_size <= physical_port[p].request.size;
            end
            3: begin
              successful_write = successful_write && physical_port[p].request.scEligible && reservation_valid &&
                reservation_address == physical_port[p].request.address && reservation_size == physical_port[p].request.size;
              atomic_result = successful_write ? 0 : 1;
              if (physical_port[p].request.scEligible && !service_fault) reservation_valid <= 0;
            end
            default: $fatal(1, "Unsupported atomic operation");
          endcase
        end
        if (successful_write) begin
          if (physical_port[p].request.address < reservation_address + (1 << reservation_size) &&
              reservation_address < physical_port[p].request.address + (1 << physical_port[p].request.size)) reservation_valid <= 0;
          for (integer i = 0; i < 8; i++)
            if (physical_port[p].request.mask[i]) memory[integer'(physical_port[p].request.address - base_address) + i] <=
              updated_data[i*8 +: 8];
        end
      end
      if (pending) begin
        if (delay > 0) begin delay <= delay - 1; delayed <= delayed + 1; end
        else begin
          physical_port[p].response.data <= captured.atomic ? atomic_result : 0;
          if (!captured.write && !captured.atomic)
            for (integer i = 0; i < (1 << captured.size); i++)
              physical_port[p].response.data[i*8 +: 8] <= memory[integer'(captured.address - base_address) + i];
          physical_port[p].response_valid <= 1;
          pending <= 0;
        end
      end
      if (physical_port[p].response_valid && physical_port[p].response_ready) begin
        if (p == 0) $display("FETCH %016h %01h %08h", captured.address, physical_port[p].response.fault ? 2 : 0, 32'(physical_port[p].response.data));
        physical_port[p].response_valid <= 0;
      end
    end
    assert property (@(posedge clock) disable iff (reset)
      core_port[p].request_valid && !core_port[p].request_ready |=> core_port[p].request_valid && $stable(core_port[p].request));
    assert property (@(posedge clock) disable iff (reset)
      physical_port[p].response_valid && !physical_port[p].response_ready |=> physical_port[p].response_valid && $stable(physical_port[p].response));
  end
  always @(posedge clock) if (!reset) begin
    cycles <= cycles + 1;
    if (cycles > 50000) $fatal(1, "Timeout");
    if (&core_pending) overlap <= overlap + 1;
    if (`CORE_TRACE.pipelineOccupancy > 4) $fatal(1, "Pipeline occupancy");
    if (`CORE_TRACE.pipelineOccupancy > pipeline_max) pipeline_max <= `CORE_TRACE.pipelineOccupancy;
    if (`CORE_TRACE.pipelineStall) dependency_stalls <= dependency_stalls + 1;
    if (`CORE_TRACE.traceValid) begin
`ifdef ENABLE_INTERRUPTS
        $display("IRQ %01h", irq_levels);
`endif

      if (`CORE_TRACE.traceRdWrite && `CORE_TRACE.traceRd == 0) $fatal(1, "x0 write");
      $display("TRACE %016h %016h %08h %016h %02h %01h %016h %01h %016h %016h",
        `CORE_TRACE.traceOrder, `CORE_TRACE.tracePc, `CORE_TRACE.traceInstruction, `CORE_TRACE.traceNextPc,
        `CORE_TRACE.traceRd, `CORE_TRACE.traceRdWrite, `CORE_TRACE.traceValue, `CORE_TRACE.traceTrap,
        `CORE_TRACE.traceCause, `CORE_TRACE.traceTval);
      if (!`CORE_TRACE.traceTrap && `CORE_TRACE.tracePc == stop_pc) begin
        $display("COVER %0d %0d %0d %0d %0d %0d", overlap, service[0].stalls, service[1].stalls,
          service[0].delayed + service[1].delayed, service[0].rejected + service[1].rejected, service[0].wraps);
        $display("PIPELINE %0d %0d", pipeline_max, dependency_stalls);
        $display("CYCLES %0d", cycles);
        $display("PASS"); $finish;
      end
    end
  end
endmodule
