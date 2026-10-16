// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
`timescale 1ns/1ps
`define CORE_TRACE dut.core.dV
module core_tb;
  localparam integer DW = `AXI_BITS;
  localparam integer PA = `PA_BITS;
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
    .status_trap(status_trap), .status_busy(status_busy), .status_sleep(status_sleep)
  );
  byte unsigned memory [0:65535];
  string image;
  logic [63:0] base_address, stop_pc, fault_fetch, fault_read, fault_write;
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
  end
  always @(posedge clock) begin
    if (!reset) begin
      cycles <= cycles + 1;
      if (cycles > 50000) $fatal(1, "Timeout");
      if (arvalid && !arready) ar_stall <= ar_stall + 1;
      if (awvalid && !awready) aw_stall <= aw_stall + 1;
      if (wvalid && !wready) w_stall <= w_stall + 1;
      if (`CORE_TRACE.pipelineOccupancy > 4) $fatal(1, "Pipeline occupancy");
      if (`CORE_TRACE.pipelineOccupancy > pipeline_max) pipeline_max <= `CORE_TRACE.pipelineOccupancy;
      if (`CORE_TRACE.pipelineStall) dependency_stalls <= dependency_stalls + 1;
      if (arvalid && arready) begin
        if (64'(araddr) < base_address || 64'(araddr) >= base_address + 65536) $fatal(1, "Truncated or unexpected read address");
        if (arid != 0 || arlen != 0 || arburst != 1 || arlock || arcache != 0 || arqos != 0) $fatal(1, "Read attributes");
        if (arprot != 1 && arprot != 5) $fatal(1, "Read privilege");
        if (arsize != (arprot[2] ? 2 : 3) || (araddr & ((1 << arsize) - 1)) != 0) $fatal(1, "Read alignment");
        $display("BUS %s %016h %0d %016h", arprot[2] ? "fetch" : "read", 64'(araddr), 1 << arsize, 64'b0);
        read_pending <= 1;
        read_address <= 64'(araddr);
        read_fetch <= arprot[2];
        read_delay <= arprot[2] ? integer'(random_state[5:4]) : 32 + integer'(random_state[7:4]);
      end
      if (read_pending && !rvalid) begin
        if (read_delay > 0) read_delay <= read_delay - 1;
        else begin
          for (integer i = 0; i < DW/8; i++)
            rdata[i*8 +: 8] <= memory[integer'((read_address - base_address) & ~(64'(DW/8) - 1)) + i];
          rresp <= ((read_fetch && read_address == fault_fetch) || (!read_fetch && read_address == fault_read)) ? 2 : 0;
          rvalid <= 1;
          read_pending <= 0;
        end
      end
      if (rvalid && rready) begin
        if (read_fetch)
          $display("FETCH %016h %01h %08h", read_address, rresp,
            32'(rdata >> (8 * (read_address % (DW/8)))));
        rvalid <= 0;
      end
      if (awvalid && awready) begin
        if (64'(awaddr) < base_address || 64'(awaddr) >= base_address + 65536) $fatal(1, "Truncated or unexpected write address");
        if (awid != 0 || awlen != 0 || awsize != 3 || awburst != 1 || awlock || awcache != 0 || awprot != 1 || awqos != 0 || awaddr[2:0] != 0) $fatal(1, "Write attributes");
        aw_held <= 1;
        write_address <= 64'(awaddr);
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
        $display("BUS write %016h 8 %016h", write_address, 64'(write_data >> (8 * (write_address % (DW/8)))));
        if (write_address != fault_write)
          for (integer i = 0; i < DW/8; i++)
            if (write_mask[i]) memory[integer'((write_address - base_address) & ~(64'(DW/8) - 1)) + i] <= write_data[i*8 +: 8];
        write_pending <= 1;
        write_delay <= integer'(random_state[11:8]);
      end
      if (write_pending && !bvalid) begin
        if (write_delay > 0) write_delay <= write_delay - 1;
        else begin
          bresp <= write_address == fault_write ? 2 : 0;
          bvalid <= 1;
          write_pending <= 0;
        end
      end
      if (bvalid && bready) begin
        bvalid <= 0;
        aw_held <= 0;
        w_held <= 0;
      end
      if (`CORE_TRACE.traceValid) begin
        if (`CORE_TRACE.traceRdWrite && `CORE_TRACE.traceRd == 0) $fatal(1, "x0 write");
        $display("TRACE %016h %016h %08h %016h %02h %01h %016h %01h %016h %016h",
          `CORE_TRACE.traceOrder, `CORE_TRACE.tracePc, `CORE_TRACE.traceInstruction, `CORE_TRACE.traceNextPc,
          `CORE_TRACE.traceRd, `CORE_TRACE.traceRdWrite, `CORE_TRACE.traceValue, `CORE_TRACE.traceTrap,
          `CORE_TRACE.traceCause, `CORE_TRACE.traceTval);
        if (!`CORE_TRACE.traceTrap && `CORE_TRACE.tracePc == stop_pc) begin
          $display("COVER %0d %0d %0d %0d %0d %0d", aw_first, w_first, together, ar_stall, aw_stall, w_stall);
          $display("PIPELINE %0d %0d", pipeline_max, dependency_stalls);
          $display("PASS");
          $finish;
        end
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
