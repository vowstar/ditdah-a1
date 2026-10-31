// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
`timescale 1ns/1ps
module jtag_tb;
  reg clock = 0, tck = 0, reset = 1, trstN = 0, tms = 1, tdi = 0;
  wire tdo, tdoEnable, requestReady, requestValid, responseReady;
  wire [6:0] requestAddress;
  wire [31:0] requestData;
  wire [1:0] requestOp;
  integer systemHalf = 5, seed = 17, cycles = 0, accepted = 0, completed = 0, writes = 0;
  reg [31:0] idcode;
  reg systemRun = 1, holdRequest = 0, holdResponse = 0, zeroLatency = 0;
  reg [1:0] forcedStatus = 0;
  reg active = 0;
  integer delayCount = 0;
  reg [31:0] memory [0:127], savedData;
  reg [1:0] savedStatus;
  wire dmReady = !holdRequest && !active && cycles % 4 != 0;
  wire dmValid;
  wire [6:0] dmAddress;
  wire [31:0] dmData;
  wire [1:0] dmOp;
  wire dmResponseValid = !holdResponse && (active && delayCount == 0 || zeroLatency && dmValid && dmReady);
  wire dmResponseReady;
  wire [31:0] dmResponseData = active ? savedData : memory[dmAddress];
  wire [1:0] dmResponseStatus = active ? savedStatus : forcedStatus;
  reg manual = 0, manualValid = 0, manualReady = 0;
  wire bridgeValid;
  wire [31:0] bridgeData;
  wire [1:0] bridgeStatus;
  DitDahA1JtagDtm dtm(
    .tck(tck), .reset(reset), .trstN(trstN), .tms(tms), .tdi(tdi), .tdo(tdo), .tdoEnable(tdoEnable),
    .dmi_request_ready(requestReady && !manual), .dmi_request_valid(requestValid),
    .dmi_request_bits_address(requestAddress), .dmi_request_bits_data(requestData), .dmi_request_bits_op(requestOp),
    .dmi_response_ready(responseReady), .dmi_response_valid(bridgeValid && !manual),
    .dmi_response_bits_data(bridgeData), .dmi_response_bits_status(bridgeStatus));
  DitDahA1DmiBridge bridge(
    .clock(clock), .tck(tck), .reset(reset),
    .upstream_request_ready(requestReady), .upstream_request_valid(manual ? manualValid : requestValid),
    .upstream_request_bits_address(manual ? 7'h30 : requestAddress),
    .upstream_request_bits_data(manual ? 32'h76543210 : requestData), .upstream_request_bits_op(manual ? 2'h2 : requestOp),
    .upstream_response_ready(manual ? manualReady : responseReady), .upstream_response_valid(bridgeValid),
    .upstream_response_bits_data(bridgeData), .upstream_response_bits_status(bridgeStatus),
    .downstream_request_ready(dmReady), .downstream_request_valid(dmValid), .downstream_request_bits_address(dmAddress),
    .downstream_request_bits_data(dmData), .downstream_request_bits_op(dmOp),
    .downstream_response_ready(dmResponseReady), .downstream_response_valid(dmResponseValid),
    .downstream_response_bits_data(dmResponseData), .downstream_response_bits_status(dmResponseStatus));
  initial forever begin #(systemHalf); clock = systemRun ? !clock : 0; end
  always @(posedge clock) begin
    if (reset) begin
      cycles <= 0; accepted <= 0; completed <= 0; writes <= 0; active <= 0;
      for (integer n = 0; n < 128; n++) memory[n] <= 32'h13579bdf ^ (n * 32'h10203);
    end else begin
      cycles <= cycles + 1;
      if (active && delayCount != 0) delayCount <= delayCount - 1;
      if (dmValid && dmReady) begin
        accepted <= accepted + 1;
        if (dmOp == 2) begin memory[dmAddress] <= dmData; writes <= writes + 1; end
        if (!zeroLatency) begin
          active <= 1; delayCount <= 1 + cycles % 11;
          savedData <= memory[dmAddress]; savedStatus <= forcedStatus;
        end
      end
      if (dmResponseValid && dmResponseReady) begin active <= 0; completed <= completed + 1; end
    end
  end
  task automatic check(input bit condition, input string message);
    if (!condition) $fatal(1, "%s", message);
  endtask
  task automatic cycle(input bit select, input bit data, output bit sampled);
    tms = select; tdi = data;
    seed = (seed * 1103515245 + 12345) & 32'h7fffffff;
    #(2 + seed % 4); sampled = tdo;
    tck = 1; #5; tck = 0; #3;
  endtask
  bit ignored;
  task automatic idle(input integer count);
    repeat (count) cycle(0, 0, ignored);
  endtask
  task automatic wait_response;
    integer count;
    count = 0;
    while (!bridgeValid) begin
      idle(1); count++;
      check(count < 2048, "Bridge completes under downstream progress");
    end
  endtask
  task automatic scan_ir(input reg [4:0] value);
    reg [4:0] captured;
    cycle(1, 0, ignored); cycle(1, 0, ignored); cycle(0, 0, ignored); cycle(0, 0, ignored);
    for (integer n = 0; n < 5; n++) cycle(n == 4, value[n], captured[n]);
    cycle(1, 0, ignored); cycle(0, 0, ignored);
    check(captured[1:0] == 1, "IR capture low bits");
  endtask
  task automatic scan_dr(input reg [40:0] value, input integer width, output reg [40:0] captured);
    captured = 0;
    cycle(1, 0, ignored); cycle(0, 0, ignored); cycle(0, 0, ignored);
    for (integer n = 0; n < width; n++) begin
      check(tdoEnable, "TDO enabled while shifting");
      cycle(n == width - 1, value[n], captured[n]);
    end
    cycle(1, 0, ignored); cycle(0, 0, ignored);
  endtask
  reg [40:0] result;
  task automatic control(input reg [31:0] value);
    scan_ir(16); scan_dr({9'b0, value}, 32, result); scan_ir(17);
  endtask
  task automatic request(input reg [1:0] op, input reg [6:0] address, input reg [31:0] data);
    scan_ir(17); scan_dr({address, data, op}, 41, result);
  endtask
  task automatic poll(output reg [40:0] value);
    integer attempts;
    attempts = 0;
    do begin
      idle(16); scan_dr(0, 41, value);
      if (value[1:0] == 3) control(32'h10000);
      attempts++;
      check(attempts < 100, "DMI completes under downstream progress");
    end while (value[1:0] == 3);
  endtask
  task automatic access(input reg [1:0] op, input reg [6:0] address, input reg [31:0] data);
    request(op, address, data); poll(result);
    check(result[1:0] == 0, "DMI success");
    if (op == 2) check(memory[address] == data, "DMI write reaches its intended address and data");
    if (op == 1) begin
      check(result[40:34] == address, "DMI response address");
      check(result[33:2] == memory[address], $sformatf("DMI address %h: got %h, expected %h; accepted=%0d completed=%0d", address, result[33:2], memory[address], accepted, completed));
    end
  endtask
  integer beforeCount, beforeWrites;
  initial begin
    if ($value$plusargs("SYSTEM_HALF=%d", systemHalf)) begin end
    if ($value$plusargs("SEED=%d", seed)) begin end
    check($value$plusargs("IDCODE=%h", idcode), "Explicit test IDCODE");
    repeat (8) cycle(1, 0, ignored);
    reset = 0; manual = 1; manualValid = 1;
    repeat (2) begin
      check(!requestReady, "Reset release cannot acknowledge a discarded request");
      cycle(1, 0, ignored);
    end
    check(requestReady, "TCK reset releases after synchronization");
    cycle(1, 0, ignored); manualValid = 0; wait_response();
    check(bridgeValid, "First request survives independent system reset release");
    manualReady = 1; cycle(0, 0, ignored); manualReady = 0; manual = 0; trstN = 1;
    repeat (6) cycle(1, 0, ignored); idle(4);
    scan_dr(0, 32, result); check(result == {9'b0, idcode}, "Explicit development IDCODE after reset");
    scan_ir(16); scan_dr(0, 32, result); check(result == 32'h1071, "DTMCS version, address width and idle hint");
    for (integer n = 0; n < 32; n++) if (n != 1 && n != 16 && n != 17) begin
      scan_ir(n); scan_dr(7'b1011011, 7, result); check(result == 7'b0110110, "Unimplemented IR selects one-bit BYPASS");
    end
    for (integer mode = 0; mode < 2; mode++) begin
      zeroLatency = mode;
      for (integer n = 0; n < 9; n++) begin
        reg [6:0] address;
        address = n == 8 ? 127 : n == 0 ? 0 : 1 << (n - 1);
        access(1, address, 0); access(2, address, 32'h5a010203 ^ (32'h01010101 * n)); access(1, address, 0);
      end
    end
    zeroLatency = 0;
    forcedStatus = 2; request(1, 5, 0); #(systemHalf * 60); idle(8); poll(result);
    check(result[1:0] == 2, "Failed response is reported");
    beforeCount = accepted; request(2, 6, 32'hffffffff); idle(32);
    check(accepted == beforeCount, "Sticky failure suppresses later writes");
    forcedStatus = 0; control(32'h10000); access(1, 6, 0);
    holdResponse = 1; beforeCount = accepted; beforeWrites = writes;
    request(2, 9, 32'hfeed1234); idle(64); scan_dr(0, 41, result);
    check(result[1:0] == 3, "Premature capture reports busy");
    request(2, 10, 32'hbad12345); control(32'h10000); scan_dr(0, 41, result);
    check(result[1:0] == 3, "DMI reset preserves the outstanding request");
    holdResponse = 0; idle(64); control(32'h10000); poll(result);
    check(result[1:0] == 0 && accepted == beforeCount + 1 && writes == beforeWrites + 1, "Busy scans do not duplicate writes");
    holdRequest = 1; beforeCount = accepted;
    request(2, 11, 32'hace01234); control(32'h20000);
    scan_ir(16); scan_dr(0, 32, result); check(result[11:10] == 0, "Hard reset clears logical status");
    request(2, 12, 32'hbad54321); scan_dr(0, 41, result);
    check(result[1:0] == 3, "Bridge retains its accepted owner across hard reset");
    holdRequest = 0; idle(128); control(32'h10000); access(1, 11, 0);
    check(accepted == beforeCount + 2 && memory[11] == 32'hace01234, "Hard reset does not withdraw or replay an accepted request");
    holdResponse = 1; request(1, 2, 0); idle(64); control(32'h20000);
    holdResponse = 0; idle(128); access(1, 3, 0);
    holdResponse = 1; beforeCount = accepted; request(2, 13, 32'habc00001); idle(64);
    trstN = 0; #100; holdResponse = 0; #1000;
    repeat (8) cycle(1, 0, ignored); trstN = 1;
    repeat (6) cycle(1, 0, ignored); idle(64); access(1, 13, 0);
    check(accepted == beforeCount + 2, "TRST preserves bridge ownership");
    holdResponse = 1; beforeCount = accepted; request(2, 14, 32'habc00002); idle(64);
    repeat (6) cycle(1, 0, ignored); idle(1); holdResponse = 0; idle(128); access(1, 14, 0);
    check(accepted == beforeCount + 2, "TMS reset does not replay accepted writes");
    beforeCount = accepted; request(2, 15, 32'habc00003); #(systemHalf * 300);
    idle(128); poll(result); check(accepted == beforeCount + 1, "Stopped TCK retains one transaction");
    systemRun = 0; #(systemHalf * 2); request(2, 16, 32'habc00004); idle(32);
    scan_dr(0, 41, result); check(result[1:0] == 3, "Stopped system clock reports busy");
    systemRun = 1; idle(128); control(32'h10000); poll(result); access(1, 16, 0);
    idle(128); manual = 1; manualValid = 1; cycle(0, 0, ignored); manualValid = 0;
    wait_response(); check(bridgeValid && !requestReady, "Bridge retains response under backpressure");
    begin
      reg [33:0] held;
      held = {bridgeData, bridgeStatus};
      repeat (8) begin cycle(0, 0, ignored); check(bridgeValid && {bridgeData, bridgeStatus} == held, "Stable held response"); end
    end
    manualReady = 1; cycle(0, 0, ignored); check(requestReady, "Bridge releases ownership on response acceptance");
    check(accepted == completed, "Every accepted request has one response");
    $display("JTAG accepted=%0d completed=%0d writes=%0d", accepted, completed, writes);
    $display("PASS"); $finish;
  end
  initial begin #10000000; $fatal(1, "JTAG timeout"); end
endmodule
