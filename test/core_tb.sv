// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
`timescale 1ns/1ps
`ifndef MEMORY_BYTES
`define MEMORY_BYTES 65536
`endif
`ifndef TIME_TICK_CYCLES
`define TIME_TICK_CYCLES 1
`endif
module core_tb;
  localparam integer DW = `AXI_BITS;
  localparam integer PA = `PA_BITS;
  localparam integer HARTS = `HARTS;
  localparam integer IDW = HARTS > 1 ? $clog2(HARTS) : 1;
  localparam integer MB = `MEMORY_BYTES;
`ifdef SOFTWARE
  localparam integer TRANSACTION_LIMIT = 640 * HARTS;
`elsif LOCAL_INTERRUPTS
  // Repeated platform work exceeds 256 retired instructions per hart.
  localparam integer TRANSACTION_LIMIT = 512 * HARTS;
`else
  localparam integer TRANSACTION_LIMIT = HARTS == 1 ? 4096 : 256 * HARTS;
`endif
  localparam integer CYCLE_LIMIT = HARTS == 1 ? 50000 : TRANSACTION_LIMIT * 128;
  integer transaction_limit = TRANSACTION_LIMIT, cycle_limit = CYCLE_LIMIT;
  `include "retire_bindings.svh"
  typedef struct packed {
    logic [63:0] address, data;
    logic [2:0] size;
    logic [7:0] mask, tag;
    logic write, fetch, privileged, atomic;
    logic [4:0] atomicOperation;
    logic scEligible;
  } core_request_t;
  typedef struct packed { logic [63:0] data; logic fault; logic [7:0] tag; logic last; } core_response_t;
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
  logic [IDW-1:0] arid, awid, read_id, write_id;
  logic arlock, awlock;
  logic [7:0] arlen, awlen;
  logic [2:0] arsize, awsize, arprot, awprot;
  logic [1:0] arburst, awburst, rresp = 0, bresp = 0;
  logic [3:0] arcache, awcache, arqos, awqos;
  logic [DW-1:0] rdata = 0, wdata;
  logic [DW/8-1:0] wstrb;
  logic status_trap, status_busy, status_sleep;
`ifdef LOCAL_INTERRUPTS
  wire local_tick = cycles % `TIME_TICK_CYCLES == 0;
`endif
  DitDahA1 dut (
    .clock(clock), .reset(reset),
    .axi_ar_valid(arvalid), .axi_ar_ready(arready), .axi_ar_bits_addr(araddr),
    .axi_ar_bits_id(arid), .axi_ar_bits_len(arlen), .axi_ar_bits_size(arsize),
    .axi_ar_bits_burst(arburst), .axi_ar_bits_lock(arlock), .axi_ar_bits_cache(arcache),
    .axi_ar_bits_prot(arprot), .axi_ar_bits_qos(arqos),
    .axi_r_valid(rvalid), .axi_r_ready(rready), .axi_r_bits_data(rdata),
    .axi_r_bits_resp(rresp), .axi_r_bits_id(read_id), .axi_r_bits_last(rlast),
    .axi_aw_valid(awvalid), .axi_aw_ready(awready), .axi_aw_bits_addr(awaddr),
    .axi_aw_bits_id(awid), .axi_aw_bits_len(awlen), .axi_aw_bits_size(awsize),
    .axi_aw_bits_burst(awburst), .axi_aw_bits_lock(awlock), .axi_aw_bits_cache(awcache),
    .axi_aw_bits_prot(awprot), .axi_aw_bits_qos(awqos),
    .axi_w_valid(wvalid), .axi_w_ready(wready), .axi_w_bits_data(wdata),
    .axi_w_bits_strb(wstrb), .axi_w_bits_last(wlast),
    .axi_b_valid(bvalid), .axi_b_ready(bready), .axi_b_bits_resp(bresp), .axi_b_bits_id(write_id),
    `include "core_ports.svh"
    .status_trap(status_trap), .status_busy(status_busy), .status_sleep(status_sleep)
  );
  `include "fetch_observers.svh"
  `include "platform_observers.svh"
`ifdef ENABLE_INTERRUPTS
  logic [2:0] irq_levels;
  wire [2:0] irq_by_hart[HARTS];
  wire [2:0] effective_irq[HARTS];
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
    5: irq_activate = architectural_fetch_busy[irq_hart] && architectural_fetch_pc[irq_hart] == irq_target && traces[irq_hart][0].pipelineOccupancy == 0;
`else
    5: irq_activate = read_pending && read_fetch && read_address == irq_target && traces[irq_hart][0].pipelineOccupancy == 0;
`endif
    6: irq_activate = multiply_busy[irq_hart];
    7: irq_activate = irq_retired;
    8: irq_activate = read_pending && read_exclusive && bus_owner / 2 == irq_hart;
    9: irq_activate = irq_retired && read_pending && !read_fetch && bus_owner / 2 != irq_hart;
    default: irq_activate = 0;
  endcase
  always @(posedge clock) irq_retired <= !reset && ((irq_mode == 9 && irq_retired) ||
    retired_pc(irq_hart, irq_target));
  always @(posedge clock) irq_ack <= !reset && aw_held && w_held && !write_pending && !bvalid && write_address == base_address + 'h5008;
`endif
  byte unsigned memory [0:MB-1];
  string image;
  string console_path, console_lines[HARTS];
  bit console_enabled = 0;
  integer console_file = 0;
  logic [63:0] console_base, results_address, result_value;
  logic [63:0] base_address, stop_pc, fault_fetch, fault_read, fault_write, fault_exclusive;
  logic [63:0] reservation_address[HARTS], interference, interference_value;
  logic [2:0] reservation_size[HARTS];
  logic [HARTS-1:0] reservation_valid = 0;
  logic read_exclusive = 0, write_exclusive = 0, exclusive_success, write_success;
  integer reservation_max = 0;
  integer exclusive_failures;
  logic [31:0] random_state;
  logic read_pending = 0, read_fetch = 0, aw_held = 0, w_held = 0, write_pending = 0;
  logic [63:0] read_address, write_address;
  logic [2:0] read_size, write_size;
  logic [DW-1:0] write_data;
  logic [DW/8-1:0] write_mask;
  integer read_remaining = 0;
  logic read_line = 0;
  integer read_delay = 0, write_delay = 0, cycles = 0;
  integer aw_first = 0, w_first = 0, together = 0;
  integer ar_stall = 0, aw_stall = 0, w_stall = 0;
  integer pipeline_max = 0, dependency_stalls = 0;
  integer issue_run = 0, retire_run = 0, issue_max = 0, retire_max = 0;
  function automatic bit console_address(input logic [63:0] address);
    return console_enabled && address >= console_base && address < console_base + 4 * HARTS;
  endfunction
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
    if (!$value$plusargs("EXCLUSIVE_FAILURES=%d", exclusive_failures)) exclusive_failures = 0;
    if (!$value$plusargs("INTERFERENCE=%d", interference)) interference = 0;
    console_enabled = $value$plusargs("CONSOLE_BASE=%h", console_base);
    if (console_enabled) begin
      if (!$value$plusargs("CONSOLE_LOG=%s", console_path) || !$value$plusargs("RESULTS=%h", results_address)) $fatal(1, "Missing software output contract");
      if (results_address < base_address || results_address + 8 * HARTS > base_address + MB) $fatal(1, "Software result bounds");
      console_file = $fopen(console_path, "w");
      if (!console_file) $fatal(1, "Cannot open software console");
    end
`ifdef SOFTWARE
    if (!console_enabled) $fatal(1, "Missing software console");
    if (!$value$plusargs("TRANSACTIONS=%d", transaction_limit) || transaction_limit <= 0 ||
        !$value$plusargs("CYCLE_LIMIT=%d", cycle_limit) || cycle_limit <= 0) $fatal(1, "Missing software resource bounds");
`endif
    for (integer i = 0; i < MB; i++) memory[i] = 0;
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
    if (HARTS > 1 && !aw_held && !w_held
`ifdef ENABLE_INTERRUPTS
        && (interrupts.mask == 0 || interrupts.started)
`endif
    ) begin
      if (aw_first == 0) wready = 0;
      else if (w_first == 0) awready = 0;
      else if (together == 0) begin
        awready = awvalid && wvalid && awready && wready;
        wready = awready;
      end
    end
`ifdef ENABLE_INTERRUPTS
    if (interrupts.mask != 0 && !interrupts.started) begin
      if (irq_mode == 1 || irq_mode == 3) awready = 0;
      if (irq_mode == 1 || irq_mode == 2) wready = 0;
    end
`endif
  end
  always @(posedge clock) begin
    if (!reset) begin
`ifdef LOCAL_INTERRUPTS
      observe_platform();
`endif
      cycles <= cycles + 1;
      if (cycles > cycle_limit) $fatal(1, "Timeout");
      if (arvalid && !arready) ar_stall <= ar_stall + 1;
      if (awvalid && !awready) aw_stall <= aw_stall + 1;
      if (wvalid && !wready) w_stall <= w_stall + 1;
      if (arvalid && arready) begin
        if (!console_address(64'(araddr)) && (64'(araddr) < base_address || 64'(araddr) + (1 << arsize) * (1 + integer'(arlen)) > base_address + MB)) $fatal(1, "Truncated or unexpected read address");
        if (arid != IDW'(bus_owner / 2) || arlen != (requests[bus_owner].size == 6 ? 64 / (DW/8) - 1 : 0) || arburst != 1 || (arlock && arprot[2]) || arcache != 0 || arqos != 0) $fatal(1, "Read attributes");
        if (arprot != {requests[bus_owner].fetch, 1'b0, requests[bus_owner].privileged}) $fatal(1, "Read privilege");
        if ((arprot[2] ? arsize != (requests[bus_owner].size == 6 ? $clog2(DW/8) : 2) : arsize > 3) ||
            (arlock && arsize != 3) || (araddr & ((1 << arsize) - 1)) != 0) $fatal(1, "Read alignment");
        if (HARTS > 1) $write("HART %0d ", bus_owner / 2);
        $display("BUS %s %016h %0d %016h", arlock ? "exclusive_read" : (arprot[2] ? "fetch" : "read"), 64'(araddr), requests[bus_owner].size == 6 ? 64 : 1 << arsize, 64'b0);
        read_pending <= 1;
        read_remaining <= integer'(arlen);
        read_line <= requests[bus_owner].size == 6;
        read_address <= 64'(araddr);
        read_id <= arid;
        read_size <= arsize;
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
            rdata[i*8 +: 8] <= console_address(read_address) ? 0 : memory[integer'((read_address - base_address) & ~(64'(DW/8) - 1)) + i];
          rresp <= ((read_fetch && read_address <= fault_fetch && fault_fetch < read_address + (1 << read_size)) || (!read_fetch && read_address == fault_read) || console_address(read_address)) ? 2 :
            (read_exclusive && read_address != fault_exclusive ? 1 : 0);
          if (read_exclusive && read_address != fault_read && read_address != fault_exclusive && !console_address(read_address)) begin
            reservation_address[read_id] <= read_address;
            reservation_size[read_id] <= read_size;
            reservation_valid[read_id] <= 1;
            if ($countones(reservation_valid | (HARTS'(1) << read_id)) > reservation_max)
              reservation_max <= $countones(reservation_valid | (HARTS'(1) << read_id));
          end
          rlast <= read_remaining == 0;
          rvalid <= 1;
        end
      end
      if (rvalid && rready) begin
        if (HARTS > 1) $write("HART %0d ", bus_owner / 2);
        if (read_line) $display("LINE_BEAT %016h %01h %h %01h", read_address, rresp, rdata, rlast);
        else $display("READ %016h %01h %016h", read_address, rresp,
          64'(rdata >> (8 * (read_address % (DW/8)))) & access_mask(read_size));
        if (read_fetch) begin
          for (integer word_index = 0; word_index < (read_line ? DW/32 : 1); word_index++) begin
            if (HARTS > 1) $write("HART %0d ", bus_owner / 2);
            $display("FETCH %016h %01h %08h", read_address + 4 * word_index, rresp,
              32'(rdata >> (8 * (read_address % (DW/8)) + 32 * word_index)));
          end
        end
        if (rlast) read_pending <= 0;
        else begin
          read_address <= read_address + (1 << read_size);
          read_remaining <= read_remaining - 1;
          read_delay <= integer'(random_state[5:4]);
        end
        rvalid <= 0;
      end
      if (awvalid && awready) begin
        if (!console_address(64'(awaddr)) && (64'(awaddr) < base_address || 64'(awaddr) + (1 << awsize) > base_address + MB)) $fatal(1, "Truncated or unexpected write address");
        if (awid != IDW'(bus_owner / 2) || awlen != 0 || awsize > 3 || (awlock && awsize != 3) ||
            awburst != 1 || awcache != 0 || awprot != {2'b0, requests[bus_owner].privileged} || awqos != 0 ||
            (awaddr & ((1 << awsize) - 1)) != 0) $fatal(1, "Write attributes");
        aw_held <= 1;
        write_address <= 64'(awaddr);
        write_id <= awid;
        write_size <= awsize;
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
        if (write_mask != ((DW/8)'((1 << (1 << write_size)) - 1) << (write_address % (DW/8)))) $fatal(1, "Write strobes");
        if (HARTS > 1) $write("HART %0d ", bus_owner / 2);
        $display("BUS %s %016h %0d %016h", write_exclusive ? "exclusive_write" : "write", write_address,
          1 << write_size, 64'(write_data >> (8 * (write_address % (DW/8)))) & access_mask(write_size));
        if (console_address(write_address) && write_address != fault_write) begin
          if (write_size != 2 || write_exclusive || write_address != console_base + 4 * (bus_owner / 2)) $fatal(1, "Console access ownership");
          if ((write_data >> (8 * (write_address % (DW/8)))) & 32'hffffff80) $fatal(1, "Console requires ASCII");
          $display("CONSOLE %0d %02h", bus_owner / 2, 8'(write_data >> (8 * (write_address % (DW/8)))));
          if (8'(write_data >> (8 * (write_address % (DW/8)))) == 10) begin
            $fdisplay(console_file, "[hart %0d] %s", bus_owner / 2, console_lines[bus_owner / 2]);
            $display("CONSOLE_LINE [hart %0d] %s", bus_owner / 2, console_lines[bus_owner / 2]);
            console_lines[bus_owner / 2] = "";
          end else console_lines[bus_owner / 2] = {console_lines[bus_owner / 2], 8'(write_data >> (8 * (write_address % (DW/8))))};
        end
        exclusive_success = reservation_valid[write_id] && reservation_address[write_id] == write_address && reservation_size[write_id] == write_size;
        write_success = write_address != fault_write && (!write_exclusive || exclusive_success);
        bresp <= write_address == fault_write ? 2 : (write_exclusive ? (exclusive_success ? 1 : 0) : 0);
        if (write_exclusive && exclusive_success && exclusive_failures > 0 && write_address != fault_write) begin
          interference_value = 0;
          for (integer i = 0; i < 8; i++) interference_value[i*8 +: 8] = memory[integer'(write_address - base_address) + i];
          interference_value = interference_value + interference;
          for (integer i = 0; i < 8; i++) memory[integer'(write_address - base_address) + i] <= interference_value[i*8 +: 8];
          exclusive_failures <= exclusive_failures - 1;
          write_success = 0;
          bresp <= 0;
          if (HARTS > 1) $write("HART %0d ", bus_owner / 2);
          $display("INTERFERE %016h %016h", write_address, interference_value);
        end else if (!console_address(write_address) && write_success)
          for (integer i = 0; i < DW/8; i++)
            if (write_mask[i]) memory[integer'((write_address - base_address) & ~(64'(DW/8) - 1)) + i] <= write_data[i*8 +: 8];
        if (write_success || (write_exclusive && exclusive_success && exclusive_failures > 0 && write_address != fault_write))
          for (integer h = 0; h < HARTS; h++)
            if (write_address < reservation_address[h] + (1 << reservation_size[h]) &&
                reservation_address[h] < write_address + (1 << write_size)) reservation_valid[h] <= 0;
        if (write_exclusive && write_address != fault_write) reservation_valid[write_id] <= 0;
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
        if (traces[h][0].pipelineOccupancy > 6 * ISSUE_WIDTH) $fatal(1, "Pipeline occupancy");
        if (traces[h][0].pipelineOccupancy > pipeline_max) pipeline_max <= traces[h][0].pipelineOccupancy;
        if (traces[h][0].pipelineStall) dependency_stalls <= dependency_stalls + 1;
        for (integer lane = 0; lane < ISSUE_WIDTH; lane++) if (traces[h][lane].traceValid) begin
`ifdef ENABLE_INTERRUPTS
          if (HARTS > 1) $write("HART %0d ", h);
          $display("IRQ %01h", effective_irq[h]);
`endif
          if (traces[h][lane].traceRdWrite && traces[h][lane].traceRd == 0) $fatal(1, "x0 write");
          if (HARTS > 1) $write("HART %0d ", h);
          $display("TRACE %016h %016h %08h %016h %02h %01h %016h %01h %016h %016h",
            traces[h][lane].traceOrder, traces[h][lane].tracePc, traces[h][lane].traceInstruction, traces[h][lane].traceNextPc,
            traces[h][lane].traceRd, traces[h][lane].traceRdWrite, traces[h][lane].traceValue, traces[h][lane].traceTrap,
            traces[h][lane].traceCause, traces[h][lane].traceTval);
          if (!traces[h][lane].traceTrap && traces[h][lane].tracePc == stop_pc) finished[h] = 1;
        end
      end
      issue_run = issue_count[0] == ISSUE_WIDTH ? issue_run + 1 : 0;
      retire_run = retire_count[0] == ISSUE_WIDTH && !traces[0][0].traceTrap ? retire_run + 1 : 0;
      if (issue_run > issue_max) issue_max = issue_run;
      if (retire_run > retire_max) retire_max = retire_run;
      if (&finished) begin
        if (console_enabled) begin
          for (integer h = 0; h < HARTS; h++) begin
            if (console_lines[h] != "") $fatal(1, "Incomplete console line");
            result_value = 0;
            for (integer i = 0; i < 8; i++) result_value[i*8 +: 8] = memory[integer'(results_address - base_address) + 8 * h + i];
            $display("RESULT %0d %016h", h, result_value);
          end
          $fclose(console_file);
        end
        $display("COVER %0d %0d %0d %0d %0d %0d", aw_first, w_first, together, ar_stall, aw_stall, w_stall);
        $display("EXCLUSIVE %0d", reservation_max);
        $display("PIPELINE %0d %0d", pipeline_max, dependency_stalls);
        $display("THROUGHPUT %0d %0d", issue_max, retire_max);
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
          requests[source].address, 1 << requests[source].size,
          requests[source].write ? requests[source].data & access_mask(requests[source].size) : 64'b0,
          requests[source].tag);
        if (HARTS > 1) $write("HART %0d ", source / 2);
        $display("ACCESS_PRIVILEGE %01h", requests[source].privileged);
        if (requests[source].atomic) begin
          if (HARTS > 1) $write("HART %0d ", source / 2);
          $display("ATOMIC %02h %01h", requests[source].atomicOperation, requests[source].scEligible);
        end
      end
      if (response_valid[source] && response_ready[source]) begin
        if (active_source != source || responses[source].tag != accepted_tag)
          $fatal(1, "Response source or tag");
        if (responses[source].last) begin
          active_source = -1;
          completed_transactions = completed_transactions + 1;
        end
        if (completed_transactions > transaction_limit) $fatal(1, "Transaction budget");
        if (HARTS > 1) $write("HART %0d ", source / 2);
        $display("RESPONSE %0d %016h %01h %02h %01h", source % 2,
          responses[source].data, responses[source].fault, responses[source].tag, responses[source].last);
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
