// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
`timescale 1ns/1ps
`define CORE_TRACE traces[0]
module core_tb;
  localparam integer DW = `AXI_BITS;
  localparam integer PA = `PA_BITS;
  localparam integer HARTS = `HARTS;
  // Multicore programs allow 256 transactions per hart and 128 cycles per transaction.
  localparam integer TRANSACTION_LIMIT = HARTS == 1 ? 4096 : 256 * HARTS;
  localparam integer CYCLE_LIMIT = HARTS == 1 ? 50000 : TRANSACTION_LIMIT * 128;
  typedef struct packed {
    logic traceValid;
    logic [63:0] traceOrder, tracePc;
    logic [31:0] traceInstruction;
    logic [63:0] traceNextPc;
    logic [4:0] traceRd;
    logic traceRdWrite;
    logic [63:0] traceValue;
    logic traceTrap;
    logic [63:0] traceCause, traceTval;
    logic [2:0] pipelineOccupancy;
    logic pipelineStall;
  } trace_t;
  typedef struct packed {
    logic [63:0] address, data;
    logic [2:0] size;
    logic [7:0] mask, tag;
    logic write, fetch, atomic;
  } core_request_t;
  typedef struct packed { logic [63:0] data; logic fault; logic [7:0] tag; } core_response_t;
  trace_t traces[HARTS];
  core_request_t requests[2*HARTS];
  core_response_t responses[2*HARTS];
  wire [2*HARTS-1:0] request_valid, request_ready, response_valid, response_ready;
  wire [HARTS-1:0] multiply_busy;
  logic [HARTS-1:0] finished = 0;
  integer bus_owner = 0, active_source = -1, completed_transactions = 0;
  logic [7:0] accepted_tag;
  `include "core_bindings.svh"
  logic clock = 0;
  logic reset = 1;
  always #5 clock = ~clock;
  logic arvalid, arready = 0, rvalid = 0, rready, rlast = 1;
  logic awvalid, awready = 0, wvalid, wready = 0, wlast, bvalid = 0, bready;
  logic [PA-1:0] araddr, awaddr;
  logic arid, awid, arlock, awlock;
  logic [7:0] arlen, awlen;
  logic [2:0] arsize, awsize, arprot, awprot;
  logic [1:0] arburst, awburst, rresp = 0, bresp = 0;
  logic [3:0] arcache, awcache, arqos, awqos;
  logic [DW-1:0] rdata = 0, wdata;
  logic [DW/8-1:0] wstrb;
  logic status_trap, status_busy, status_sleep;
  DitDahA1 dut (
    .clock(clock), .reset(reset),
    .axi_ar_valid(arvalid), .axi_ar_ready(arready), .axi_ar_bits_addr(araddr),
    .axi_ar_bits_id(arid), .axi_ar_bits_len(arlen), .axi_ar_bits_size(arsize),
    .axi_ar_bits_burst(arburst), .axi_ar_bits_lock(arlock), .axi_ar_bits_cache(arcache),
    .axi_ar_bits_prot(arprot), .axi_ar_bits_qos(arqos),
    .axi_r_valid(rvalid), .axi_r_ready(rready), .axi_r_bits_data(rdata),
    .axi_r_bits_resp(rresp), .axi_r_bits_id(1'b0), .axi_r_bits_last(rlast),
    .axi_aw_valid(awvalid), .axi_aw_ready(awready), .axi_aw_bits_addr(awaddr),
    .axi_aw_bits_id(awid), .axi_aw_bits_len(awlen), .axi_aw_bits_size(awsize),
    .axi_aw_bits_burst(awburst), .axi_aw_bits_lock(awlock), .axi_aw_bits_cache(awcache),
    .axi_aw_bits_prot(awprot), .axi_aw_bits_qos(awqos),
    .axi_w_valid(wvalid), .axi_w_ready(wready), .axi_w_bits_data(wdata),
    .axi_w_bits_strb(wstrb), .axi_w_bits_last(wlast),
    .axi_b_valid(bvalid), .axi_b_ready(bready), .axi_b_bits_resp(bresp), .axi_b_bits_id(1'b0),
    `include "core_ports.svh"
    .status_trap(status_trap), .status_busy(status_busy), .status_sleep(status_sleep)
  );
  `include "fetch_observers.svh"
`ifdef ENABLE_INTERRUPTS
  logic [2:0] irq_levels;
  wire [2:0] irq_by_hart[HARTS];
  integer irq_hart;
  initial if (!$value$plusargs("IRQ_HART=%d", irq_hart)) irq_hart = 0;
  for (genvar h = 0; h < HARTS; h++) assign irq_by_hart[h] = h == irq_hart ? irq_levels : 0;
  logic irq_activate, irq_ack = 0, irq_retired = 0;
  integer irq_mode;
  logic [63:0] irq_target;
  interrupt_driver interrupts(clock, reset, irq_activate, irq_ack, irq_levels, irq_mode, irq_target);
  always_comb case (irq_mode)
    0: irq_activate = 1;
    1: irq_activate = awvalid || wvalid;
    2: irq_activate = aw_held && !w_held;
    3: irq_activate = w_held && !aw_held;
    4: irq_activate = read_pending && !read_fetch;
`ifdef ICACHE
    5: irq_activate = architectural_fetch_busy[irq_hart] && architectural_fetch_pc[irq_hart] == irq_target && traces[irq_hart].pipelineOccupancy == 0;
`else
    5: irq_activate = read_pending && read_fetch && read_address == irq_target && traces[irq_hart].pipelineOccupancy == 0;
`endif
    6: irq_activate = multiply_busy[irq_hart];
    7: irq_activate = irq_retired;
    8: irq_activate = read_pending && read_exclusive && bus_owner / 2 == irq_hart;
    9: irq_activate = irq_retired && read_pending && !read_fetch && bus_owner / 2 != irq_hart;
    default: irq_activate = 0;
  endcase
  always @(posedge clock) irq_retired <= !reset && ((irq_mode == 9 && irq_retired) ||
    (traces[irq_hart].traceValid && traces[irq_hart].tracePc == irq_target));
  always @(posedge clock) irq_ack <= !reset && aw_held && w_held && !write_pending && !bvalid && write_address == base_address + 'h5008;
`endif
  byte unsigned memory [0:65535];
  string image;
  logic [63:0] base_address, stop_pc, fault_fetch, fault_read, fault_write, fault_exclusive;
  logic [63:0] reservation_address, interference, interference_value;
  logic reservation_valid = 0, read_exclusive = 0, write_exclusive = 0;
  integer exclusive_failures;
  logic [31:0] random_state;
  logic read_pending = 0, read_fetch = 0, aw_held = 0, w_held = 0, write_pending = 0;
  logic [63:0] read_address, write_address;
  logic [DW-1:0] write_data;
  logic [DW/8-1:0] write_mask;
  integer read_delay = 0, write_delay = 0, cycles = 0;
  integer aw_first = 0, w_first = 0, together = 0;
  integer ar_stall = 0, aw_stall = 0, w_stall = 0;
  integer pipeline_max = 0, dependency_stalls = 0;
  initial begin
    if (!$value$plusargs("IMAGE=%s", image)) $fatal(1, "Missing image");
    if (!$value$plusargs("BASE=%h", base_address)) $fatal(1, "Missing base");
    if (!$value$plusargs("STOP=%h", stop_pc)) $fatal(1, "Missing stop");
    if (!$value$plusargs("SEED=%d", random_state)) random_state = 1;
    if (!$value$plusargs("FAULT_FETCH=%h", fault_fetch)) fault_fetch = '1;
    if (!$value$plusargs("FAULT_READ=%h", fault_read)) fault_read = '1;
    if (!$value$plusargs("FAULT_WRITE=%h", fault_write)) fault_write = '1;
    if (!$value$plusargs("FAULT_EXCLUSIVE=%h", fault_exclusive)) fault_exclusive = '1;
    if (!$value$plusargs("EXCLUSIVE_FAILURES=%d", exclusive_failures)) exclusive_failures = 0;
    if (!$value$plusargs("INTERFERENCE=%d", interference)) interference = 0;
    for (integer i = 0; i < 65536; i++) memory[i] = 0;
    $readmemh(image, memory);
    repeat (3) @(negedge clock);
    reset = 0;
  end
  always @(negedge clock) begin
    random_state = random_state ^ (random_state << 13);
    random_state = random_state ^ (random_state >> 17);
    random_state = random_state ^ (random_state << 5);
    arready = !reset && !read_pending && !rvalid && random_state[0];
    awready = !reset && !aw_held && !bvalid && random_state[1];
    wready = !reset && !w_held && !bvalid && random_state[2];
`ifdef ENABLE_INTERRUPTS
    if (interrupts.mask != 0 && !interrupts.started) begin
      if (irq_mode == 1 || irq_mode == 3) awready = 0;
      if (irq_mode == 1 || irq_mode == 2) wready = 0;
    end
`endif
  end
  always @(posedge clock) begin
    if (!reset) begin
      cycles <= cycles + 1;
      if (cycles > CYCLE_LIMIT) $fatal(1, "Timeout");
      if (arvalid && !arready) ar_stall <= ar_stall + 1;
      if (awvalid && !awready) aw_stall <= aw_stall + 1;
      if (wvalid && !wready) w_stall <= w_stall + 1;
      if (arvalid && arready) begin
        if (64'(araddr) < base_address || 64'(araddr) >= base_address + 65536) $fatal(1, "Truncated or unexpected read address");
        if (arid != 0 || arlen != 0 || arburst != 1 || (arlock && arprot[2]) || arcache != 0 || arqos != 0) $fatal(1, "Read attributes");
        if (arprot != 1 && arprot != 5) $fatal(1, "Read privilege");
        if (arsize != (arprot[2] ? 2 : 3) || (araddr & ((1 << arsize) - 1)) != 0) $fatal(1, "Read alignment");
        if (HARTS > 1) $write("HART %0d ", bus_owner / 2);
        $display("BUS %s %016h %0d %016h", arlock ? "exclusive_read" : (arprot[2] ? "fetch" : "read"), 64'(araddr), 1 << arsize, 64'b0);
        read_pending <= 1;
        read_address <= 64'(araddr);
        read_fetch <= arprot[2];
        read_exclusive <= arlock;
        read_delay <= arprot[2] ? integer'(random_state[5:4]) : 32 + integer'(random_state[7:4]);
`ifdef ENABLE_INTERRUPTS
        if (irq_mode == 5 && 64'(araddr) == irq_target) read_delay <= 48;
`endif
      end
      if (read_pending && !rvalid) begin
        if (read_delay > 0) read_delay <= read_delay - 1;
        else begin
          for (integer i = 0; i < DW/8; i++)
            rdata[i*8 +: 8] <= memory[integer'((read_address - base_address) & ~(64'(DW/8) - 1)) + i];
          rresp <= ((read_fetch && read_address == fault_fetch) || (!read_fetch && read_address == fault_read)) ? 2 :
            (read_exclusive && read_address != fault_exclusive ? 1 : 0);
          if (read_exclusive) begin
            reservation_address <= read_address;
            reservation_valid <= read_address != fault_read && read_address != fault_exclusive;
          end
          rvalid <= 1;
          read_pending <= 0;
        end
      end
      if (rvalid && rready) begin
        if (HARTS > 1) $write("HART %0d ", bus_owner / 2);
        $display("READ %016h %01h %016h", read_address, rresp,
          64'(rdata >> (8 * (read_address % (DW/8)))) & (read_fetch ? 64'hffffffff : '1));
        if (read_fetch) begin
          if (HARTS > 1) $write("HART %0d ", bus_owner / 2);
          $display("FETCH %016h %01h %08h", read_address, rresp,
            32'(rdata >> (8 * (read_address % (DW/8)))));
        end
        rvalid <= 0;
      end
      if (awvalid && awready) begin
        if (64'(awaddr) < base_address || 64'(awaddr) >= base_address + 65536) $fatal(1, "Truncated or unexpected write address");
        if (awid != 0 || awlen != 0 || awsize != 3 || awburst != 1 || awcache != 0 || awprot != 1 || awqos != 0 || awaddr[2:0] != 0) $fatal(1, "Write attributes");
        aw_held <= 1;
        write_address <= 64'(awaddr);
        write_exclusive <= awlock;
        if (!w_held && !(wvalid && wready)) aw_first <= aw_first + 1;
      end
      if (wvalid && wready) begin
        if (!wlast) $fatal(1, "Missing WLAST");
        w_held <= 1;
        write_data <= wdata;
        write_mask <= wstrb;
        if (!aw_held && !(awvalid && awready)) w_first <= w_first + 1;
      end
      if (awvalid && awready && wvalid && wready) together <= together + 1;
      if (aw_held && w_held && !write_pending && !bvalid) begin
        if (write_mask != (DW/8)'(255 << (write_address % (DW/8)))) $fatal(1, "Write strobes");
        if (HARTS > 1) $write("HART %0d ", bus_owner / 2);
        $display("BUS %s %016h 8 %016h", write_exclusive ? "exclusive_write" : "write", write_address, 64'(write_data >> (8 * (write_address % (DW/8)))));
        bresp <= write_address == fault_write ? 2 : (write_exclusive ? (reservation_valid && reservation_address == write_address ? 1 : 0) : 0);
        if (write_exclusive && reservation_valid && reservation_address == write_address && exclusive_failures > 0 && write_address != fault_write) begin
          interference_value = 0;
          for (integer i = 0; i < 8; i++) interference_value[i*8 +: 8] = memory[integer'(write_address - base_address) + i];
          interference_value = interference_value + interference;
          for (integer i = 0; i < 8; i++) memory[integer'(write_address - base_address) + i] <= interference_value[i*8 +: 8];
          exclusive_failures <= exclusive_failures - 1;
          bresp <= 0;
          if (HARTS > 1) $write("HART %0d ", bus_owner / 2);
          $display("INTERFERE %016h %016h", write_address, interference_value);
        end else if (write_address != fault_write && (!write_exclusive || (reservation_valid && reservation_address == write_address)))
          for (integer i = 0; i < DW/8; i++)
            if (write_mask[i]) memory[integer'((write_address - base_address) & ~(64'(DW/8) - 1)) + i] <= write_data[i*8 +: 8];
        if (reservation_address == write_address) reservation_valid <= 0;
        write_pending <= 1;
        write_delay <= integer'(random_state[11:8]);
      end
      if (write_pending && !bvalid) begin
        if (write_delay > 0) write_delay <= write_delay - 1;
        else begin
          bvalid <= 1;
          write_pending <= 0;
        end
      end
      if (bvalid && bready) begin
        if (write_exclusive) begin
          if (HARTS > 1) $write("HART %0d ", bus_owner / 2);
          $display("WRITE %016h %01h", write_address, bresp);
        end
        bvalid <= 0;
        aw_held <= 0;
        w_held <= 0;
      end
      for (integer h = 0; h < HARTS; h++) begin
        if (traces[h].pipelineOccupancy > 4) $fatal(1, "Pipeline occupancy");
        if (traces[h].pipelineOccupancy > pipeline_max) pipeline_max <= traces[h].pipelineOccupancy;
        if (traces[h].pipelineStall) dependency_stalls <= dependency_stalls + 1;
        if (traces[h].traceValid) begin
`ifdef ENABLE_INTERRUPTS
          if (HARTS > 1) $write("HART %0d ", h);
          $display("IRQ %01h", irq_by_hart[h]);
`endif
          if (traces[h].traceRdWrite && traces[h].traceRd == 0) $fatal(1, "x0 write");
          if (HARTS > 1) $write("HART %0d ", h);
          $display("TRACE %016h %016h %08h %016h %02h %01h %016h %01h %016h %016h",
            traces[h].traceOrder, traces[h].tracePc, traces[h].traceInstruction, traces[h].traceNextPc,
            traces[h].traceRd, traces[h].traceRdWrite, traces[h].traceValue, traces[h].traceTrap,
            traces[h].traceCause, traces[h].traceTval);
          if (!traces[h].traceTrap && traces[h].tracePc == stop_pc) finished[h] = 1;
        end
      end
      if (&finished) begin
        $display("COVER %0d %0d %0d %0d %0d %0d", aw_first, w_first, together, ar_stall, aw_stall, w_stall);
        $display("PIPELINE %0d %0d", pipeline_max, dependency_stalls);
        $display("CYCLES %0d", cycles);
        $display("PASS"); $finish;
      end
    end
  end
  always @(posedge clock) if (!reset) begin
    for (integer source = 0; source < 2*HARTS; source++) begin
      if (request_valid[source] && request_ready[source]) begin
        if (active_source != -1) $fatal(1, "Overlapping accepted sources");
        active_source = source;
        accepted_tag = requests[source].tag;
        bus_owner <= source;
        if (HARTS > 1) $write("HART %0d ", source / 2);
        $display("REQUEST %s %016h %0d %016h %02h",
          requests[source].atomic ? "atomic" : (source % 2 == 0 ? "fetch" : (requests[source].write ? "write" : "read")),
          requests[source].address, 1 << requests[source].size, requests[source].write ? requests[source].data : 64'b0,
          requests[source].tag);
      end
      if (response_valid[source] && response_ready[source]) begin
        if (active_source != source || responses[source].tag != accepted_tag)
          $fatal(1, "Response source or tag");
        active_source = -1;
        completed_transactions = completed_transactions + 1;
        if (completed_transactions > TRANSACTION_LIMIT) $fatal(1, "Transaction budget");
        if (HARTS > 1) $write("HART %0d ", source / 2);
        $display("RESPONSE %0d %016h %01h %02h", source % 2,
          responses[source].data, responses[source].fault, responses[source].tag);
      end
    end
  end
  assert property (@(posedge clock) disable iff (reset)
    arvalid && !arready |=> arvalid && $stable({araddr, arid, arlen, arsize, arburst, arlock, arcache, arprot, arqos}));
  assert property (@(posedge clock) disable iff (reset)
    awvalid && !awready |=> awvalid && $stable({awaddr, awid, awlen, awsize, awburst, awlock, awcache, awprot, awqos}));
  assert property (@(posedge clock) disable iff (reset)
    wvalid && !wready |=> wvalid && $stable({wdata, wstrb, wlast}));
endmodule

`ifdef ENABLE_INTERRUPTS
module interrupt_driver(input logic clock, reset, activate, acknowledge,
  output logic [2:0] levels = 0, output integer mode, output logic [63:0] target);
  integer mask, waited = 0;
  logic started = 0;
  initial begin
    if (!$value$plusargs("IRQ_MASK=%d", mask)) mask = 0;
    if (!$value$plusargs("IRQ_MODE=%d", mode)) mode = -1;
    if (!$value$plusargs("IRQ_TARGET=%h", target)) target = 0;
  end
  always @(negedge clock) if (!reset) begin
    if (!started && activate && mask != 0) begin
      levels = 3'(mask); started = 1;
      $display("IRQ_START %0d", mode);
    end
    if (acknowledge) begin
      if (levels[2]) levels[2] = 0;
      else if (levels[0]) levels[0] = 0;
      else levels[1] = 0;
      waited = 0;
    end
    if (levels != 0) waited = waited + 1;
    if (waited > 1000 * `HARTS) $fatal(1, "Held interrupt was not acknowledged");
  end
endmodule
`endif
