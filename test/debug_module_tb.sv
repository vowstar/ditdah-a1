// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
`timescale 1ns/1ps
`include "memory_port.svh"
module debug_module_tb;
  localparam integer HARTS = `HARTS;
  logic clock = 0, reset = 1;
  always #5 clock = !clock;
  wire ndmreset, core_reset = reset || ndmreset;
  wire halt_req[HARTS], debug_mode[HARTS];
  wire [63:0] debug_entry[HARTS], debug_exception[HARTS];
  memory_port client[2*HARTS](), shared(), debug_memory(), ram();
  wire [3:0] owner;
  logic memory_stall = 0;
  logic response_debug = 0;
  logic [7:0] memory[16384];
  integer faults = 0, replies = 0, denied = 0, speculative = 0;
  logic ram_valid = 0;
  response_t ram_response = '0;
  logic dmi_request_valid = 0, dmi_response_ready = 0;
  wire dmi_request_ready, dmi_response_valid;
  logic [6:0] dmi_request_bits_address;
  logic [31:0] dmi_request_bits_data;
  logic [1:0] dmi_request_bits_op;
  wire [31:0] dmi_response_bits_data;
  wire [1:0] dmi_response_bits_status;
  `include "debug_module_bindings.svh"
  for (genvar n = 0; n < HARTS; n++) begin: harts
    DitDahA1Core core(.clock(clock), .reset(core_reset), .hartId(4'(n)),
      .debug_haltReq(halt_req[n]), .debug_entryPc(debug_entry[n]), .debug_exceptionPc(debug_exception[n]),
      .debug_mode(debug_mode[n]), `PORT(instruction, client[2*n]), `PORT(data, client[2*n+1]),
      .status_trap(), .status_busy(), .status_sleep());
  end
  wire selected = shared.request.address >= 'h10000 && shared.request.address < 'h11000;
  always_comb begin
    debug_memory.request = shared.request; ram.request = shared.request;
    debug_memory.request_valid = shared.request_valid && selected && !memory_stall;
    ram.request_valid = shared.request_valid && !selected;
    shared.request_ready = selected ? debug_memory.request_ready && !memory_stall : ram.request_ready;
    shared.response_valid = response_debug ? debug_memory.response_valid : ram.response_valid;
    shared.response = response_debug ? debug_memory.response : ram.response;
    debug_memory.response_ready = shared.response_ready && response_debug;
    ram.response_ready = shared.response_ready && !response_debug;
    ram.request_ready = !ram_valid || ram.response_ready;
    ram.response_valid = ram_valid; ram.response = ram_response;
  end
  always @(posedge clock) begin
    if (core_reset) begin response_debug <= 0; ram_valid <= 0; end
    else begin
      if (shared.request_valid && shared.request_ready) response_debug <= selected;
      if (ram.response_valid && ram.response_ready) ram_valid <= 0;
      if (ram.request_valid && ram.request_ready) begin
        ram_valid <= 1; ram_response <= '0;
        ram_response.tag <= ram.request.tag; ram_response.last <= 1;
        ram_response.fault <= ram.request.address + (1 << ram.request.size) > 16384;
        for (integer n = 0; n < 8; n++) if (ram.request.address + n < 16384) begin
          ram_response.data[8*n +: 8] <= memory[ram.request.address+n];
          if (ram.request.write && ram.request.mask[n]) memory[ram.request.address+n] <= ram.request.data[8*n +: 8];
        end
      end
      if (debug_memory.response_valid && debug_memory.response_ready) begin
        replies <= replies + 1;
        if (debug_memory.response.fault) begin
          faults <= faults + 1;
          if (!shared.request.debug) denied <= denied + 1;
          else begin
            check(shared.request.fetch, "Unexpected authorized debug data fault");
            speculative <= speculative + 1;
          end
        end
      end
    end
  end
  task automatic tick;
    @(posedge clock); #1;
  endtask
  task automatic check(input bit condition, input string message);
    if (!condition) $fatal(1, "%s", message);
  endtask
  task automatic dmi(input bit write, input reg [6:0] address, input reg [31:0] data, output reg [31:0] value);
    @(negedge clock);
    dmi_request_valid = 1; dmi_request_bits_address = address;
    dmi_request_bits_data = data; dmi_request_bits_op = write ? 2 : 1;
    while (!dmi_request_ready) @(negedge clock);
    tick();
    @(negedge clock); dmi_request_valid = 0;
    while (!dmi_response_valid) tick();
    value = dmi_response_bits_data;
    repeat (3) begin tick(); check(dmi_response_valid && dmi_response_bits_data == value, "Stable DMI response under backpressure"); end
    check(dmi_response_bits_status == 0, "DMI register access succeeds");
    @(negedge clock); dmi_response_ready = 1; tick();
    @(negedge clock); dmi_response_ready = 0;
  endtask
  reg [31:0] scratch;
  task automatic put(input reg [6:0] address, input reg [31:0] value);
    dmi(1, address, value, scratch);
  endtask
  task automatic get(input reg [6:0] address, output reg [31:0] value);
    dmi(0, address, 0, value);
  endtask
  task automatic complete_command(input integer expected_error = 0);
    reg [31:0] value;
    integer count;
    count = 0;
    do begin get('h16, value); count++; check(count < 20000, "Abstract command completes with fair memory service"); end while (value[12]);
    check(value[10:8] == expected_error, $sformatf("Abstract error %0d, expected %0d", value[10:8], expected_error));
  endtask
  task automatic read_gpr(input integer index, output reg [63:0] value, input bit narrow = 0);
    reg [31:0] low, high;
    put('h17, (narrow ? 'h220000 : 'h320000) | 'h1000 | index); complete_command();
    get(4, low); get(5, high); value = {high, low};
  endtask
  task automatic write_gpr(input integer index, input reg [63:0] value);
    put(4, value[31:0]); put(5, value[63:32]);
    put('h17, 'h331000 | index); complete_command();
  endtask
  task automatic select_hart(input integer hart, input reg [31:0] flags = 0);
    put('h10, (hart << 16) | 1 | flags);
  endtask
  task automatic execute;
    put('h17, 'h40000); complete_command();
  endtask
  reg [63:0] expected[HARTS][32], value64;
  reg [31:0] value;
  string image;
  integer count;
  initial begin
    check($value$plusargs("IMAGE=%s", image), "Software image supplied");
    $readmemh(image, memory);
    `include "debug_module_expected.svh"
    tick(); tick(); reset = 0; tick();
    put('h10, 1); put(4, 'h87654321); put(5, 'h12345678);
    count = 0;
    do begin tick(); count++; check(count < 20000, "All software harts reach their ready marker");
    end while (!(`READY_HARTS));
    check(faults == 2*HARTS, "Ordinary harts cannot read or write the debug window");
    get(4, value); check(value == 'h87654321, "Denied stores do not alter shared debug data");
    put('h10, 'h3ff0001); get('h10, value);
    check(value[25:16] == (`SELECT_MASK), "Hart selection width is WARL");
    for (integer hart = 0; hart < HARTS; hart++) begin
      select_hart(hart, 'h80000000);
      do get('h11, value); while (!value[9]);
      for (integer r = 0; r < 32; r++) if (HARTS <= 3 || r == 0 || r == 1 || r == 8 || r == 9 || r == 31) begin
        read_gpr(r, value64); check(value64 == expected[hart][r], $sformatf("Hart %0d x%0d: got %h, expected %h", hart, r, value64, expected[hart][r]));
      end
      write_gpr(8, 64'hfedcba9876543210 ^ hart); expected[hart][8] = 64'hfedcba9876543210 ^ hart;
      write_gpr(9, 64'h1234567887654321 ^ hart); expected[hart][9] = 64'h1234567887654321 ^ hart;
      read_gpr(8, value64); check(value64 == expected[hart][8], "Transfer through x9 preserves x8");
      read_gpr(9, value64); check(value64 == expected[hart][9], "Transfer through x8 preserves x9");
      write_gpr(0, '1); read_gpr(0, value64); check(value64 == 0, "x0 remains zero");
      read_gpr(9, value64, 1); check(value64[31:0] == expected[hart][9][31:0], "RV64 supports narrow register reads");
      check(value64[63:32] == 0, "Narrow reads preserve the other data register");
      $display("DM_HART %0d register access passed", hart);
    end
    `include "debug_module_commands.svh"
    check(replies > 100, "Real core instruction and data requests consumed the debug module");
    check(denied == 2*HARTS, "Only the ordinary software probes lack debug authorization");
    $display("DM harts=%0d memory_replies=%0d denied=%0d speculative_faults=%0d", HARTS, replies, denied, speculative);
    $display("PASS"); $finish;
  end
  initial begin #100000000; $fatal(1, "Debug module timeout"); end
endmodule
