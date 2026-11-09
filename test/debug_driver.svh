// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT

integer debug_trigger, debug_entries = 0, debug_retirements = 0;
integer debug_priority;
bit debug_priority_sent = 0;
bit debug_triggered, debug_previous_mode = 0;
logic [63:0] debug_next_pc;
initial begin
  if (!$value$plusargs("DEBUG_TRIGGER=%d", debug_trigger)) debug_trigger = -1;
  if (!$value$plusargs("DEBUG_PRIORITY=%d", debug_priority)) debug_priority = 0;
  debug_halt_req = debug_trigger == 0;
  debug_triggered = debug_trigger <= 0;
  debug_next_pc = 0;
end
always @(negedge clock) if (!reset) begin
  if (!debug_triggered) begin
    case (debug_trigger)
      1: debug_halt_req = service[1].pending && service[1].captured.write;
`ifdef ENABLE_M
      2: debug_halt_req = dut.backend.mulDiv.busy;
`endif
      3: debug_halt_req = status_sleep;
      4: debug_halt_req = service[1].pending && service[1].captured.atomic;
      5: debug_halt_req = service[1].pending && !service[1].captured.write;
      8: debug_halt_req = dut.backend.commitCount != 0 && !dut.backend.commit.output_valid &&
        (dut.backend.commitPackets_0_instruction_instruction == 'h00d00073 ||
         dut.backend.commitPackets_0_instruction_instruction == 'h01d00073);
`ifdef ENABLE_FLOATING
      7: debug_halt_req = dut.backend.fpu.input_valid && dut.backend.fpu.input_ready;
`endif
      default: $fatal(1, "Unknown debug trigger");
    endcase
    if (debug_halt_req) debug_triggered = 1;
  end
  if (debug_mode) debug_halt_req = 0;
  if (debug_priority && !debug_priority_sent && !debug_mode && dut.backend.debugBreakPending) begin
    debug_halt_req = 1;
    debug_priority_sent = 1;
  end
end
always @(posedge clock) if (!reset) begin
  for (integer lane = 0; lane < ISSUE_WIDTH; lane++) if (traces[0][lane].traceValid) begin
    if (debug_mode) $fatal(1, "Debug execution in software trace");
    debug_retirements++;
    debug_next_pc = traces[0][lane].traceNextPc;
  end
  if (debug_mode && !debug_previous_mode) begin
    if (core_pending[1] || service[1].pending) $fatal(1, "Debug entry before accepted data drain");
    debug_entries++;
    $display("DEBUG_ENTER %0d %0d %016h", cycles, debug_retirements, debug_next_pc);
  end
  if (!debug_mode && debug_previous_mode) $display("DEBUG_EXIT %0d", cycles);
  debug_previous_mode <= debug_mode;
end
function automatic logic [63:0] debug_word(input integer address);
  for (integer n = 0; n < 8; n++) debug_word[n*8 +: 8] = memory[address+n];
endfunction
final begin
  for (integer address = 'h3000; address < 'h3200; address += 8)
    $display("DEBUG_VALUE %04h %016h", address, debug_word(address));
  for (integer address = 'h200; address < 'h240; address += 8)
    $display("DEBUG_VALUE %04h %016h", address, debug_word(address));
end
