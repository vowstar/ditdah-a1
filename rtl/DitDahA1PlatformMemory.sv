// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
module DitDahA1PlatformMemory #(
  parameter integer ID_BITS = 1, HARTS = 1,
  parameter bit ENABLE_A = 1,
  parameter logic [31:0] ROM_BASE = 32'h1000, RAM_BASE = 32'h80000000,
  parameter integer RAM_BYTES = 524288,
  parameter logic [31:0] CONSOLE_BASE = 32'h10000000,
  parameter integer CLOCK_HZ = 10000000, BAUD = 115200, TIMEBASE_HZ = 1000000
)(
  input logic clock, reset,
  output logic tx, timeTick,
  input logic axi_ar_valid, output logic axi_ar_ready,
  input logic [31:0] axi_ar_bits_addr,
  input logic [ID_BITS-1:0] axi_ar_bits_id,
  input logic [7:0] axi_ar_bits_len,
  input logic [2:0] axi_ar_bits_size,
  input logic [1:0] axi_ar_bits_burst,
  input logic axi_ar_bits_lock,
  output logic axi_r_valid, input logic axi_r_ready,
  output logic [63:0] axi_r_bits_data,
  output logic [ID_BITS-1:0] axi_r_bits_id,
  output logic [1:0] axi_r_bits_resp,
  output logic axi_r_bits_last,
  input logic axi_aw_valid, output logic axi_aw_ready,
  input logic [31:0] axi_aw_bits_addr,
  input logic [ID_BITS-1:0] axi_aw_bits_id,
  input logic [7:0] axi_aw_bits_len,
  input logic [2:0] axi_aw_bits_size,
  input logic [1:0] axi_aw_bits_burst,
  input logic axi_aw_bits_lock,
  input logic axi_w_valid, output logic axi_w_ready,
  input logic [63:0] axi_w_bits_data,
  input logic [7:0] axi_w_bits_strb,
  input logic axi_w_bits_last,
  output logic axi_b_valid, input logic axi_b_ready,
  output logic [ID_BITS-1:0] axi_b_bits_id,
  output logic [1:0] axi_b_bits_resp
);
  localparam integer BIT_CYCLES = (CLOCK_HZ + BAUD/2) / BAUD;
  localparam integer TICK_CYCLES = CLOCK_HZ / TIMEBASE_HZ;
  localparam integer UART_BITS = $clog2(BIT_CYCLES) > 0 ? $clog2(BIT_CYCLES) : 1;
  localparam integer TICK_BITS = $clog2(TICK_CYCLES) > 0 ? $clog2(TICK_CYCLES) : 1;
  logic [63:0] ram [RAM_BYTES/8];
  logic reading, read_error, read_exclusive;
  logic [31:0] read_address;
  logic [7:0] read_left;
  logic [2:0] read_size;
  logic [ID_BITS-1:0] read_id;
  logic aw_held, w_held, write_error, write_exclusive;
  logic [31:0] write_address;
  logic [7:0] write_left;
  logic [2:0] write_size;
  logic [ID_BITS-1:0] write_id;
  logic [63:0] write_data;
  logic [7:0] write_strobe;
  logic write_last;
  logic [9:0] serial;
  logic [3:0] serial_left;
  logic [UART_BITS-1:0] baud_count;
  logic [TICK_BITS-1:0] tick_count;
  wire read_ram = {1'b0,read_address} >= {1'b0,RAM_BASE} &&
      {1'b0,read_address} + (33'd1 << read_size) <= {1'b0,RAM_BASE} + RAM_BYTES;
  wire read_rom = {1'b0,read_address} >= {1'b0,ROM_BASE} &&
      {1'b0,read_address} + (33'd1 << read_size) <= {1'b0,ROM_BASE} + 4096;
  wire write_ram = {1'b0,write_address} >= {1'b0,RAM_BASE} &&
      {1'b0,write_address} + (33'd1 << write_size) <= {1'b0,RAM_BASE} + RAM_BYTES;
  wire write_console = write_address >= CONSOLE_BASE &&
      {1'b0,write_address} < {1'b0,CONSOLE_BASE} + 4*HARTS && write_size == 2;
  wire [7:0] byte_mask = 8'(((32'd1 << (1 << write_size))-1) << write_address[2:0]);
  wire write_bad = write_error || write_last != (write_left == 0) ||
      (write_strobe & ~byte_mask) != 0 || (!write_ram && !write_console) ||
      (write_console && (write_exclusive || write_strobe != byte_mask));
  wire write_fire = aw_held && w_held &&
      (!write_console || write_bad || serial_left == 0);
  wire write_match;
  wire write_effect = write_fire && !write_bad && (!write_exclusive || write_match);
  assign axi_ar_ready = !reading && !axi_r_valid;
  assign axi_aw_ready = !aw_held && !axi_b_valid;
  assign axi_w_ready = !w_held;
  assign tx = serial_left == 0 ? 1'b1 : serial[0];
  assign timeTick = tick_count == TICK_BITS'(TICK_CYCLES-1);

  generate if (ENABLE_A) begin: exclusives
    logic [(1<<ID_BITS)-1:0] valid;
    logic [31:0] address [1<<ID_BITS];
    logic [2:0] size [1<<ID_BITS];
    assign write_match = valid[write_id] && address[write_id] == write_address && size[write_id] == write_size;
    always_ff @(posedge clock) begin
      if (reset) valid <= '0;
      else begin
        if (axi_ar_valid && axi_ar_ready && axi_ar_bits_lock) begin
          valid[axi_ar_bits_id] <= axi_ar_bits_len == 0 && axi_ar_bits_size <= 3 &&
              axi_ar_bits_burst == 1 && (axi_ar_bits_addr & ((32'd1 << axi_ar_bits_size)-1)) == 0 &&
              {1'b0,axi_ar_bits_addr} >= {1'b0,RAM_BASE} &&
              {1'b0,axi_ar_bits_addr} + (33'd1 << axi_ar_bits_size) <= {1'b0,RAM_BASE} + RAM_BYTES;
          address[axi_ar_bits_id] <= axi_ar_bits_addr;
          size[axi_ar_bits_id] <= axi_ar_bits_size;
        end
        if (write_fire && write_exclusive) valid[write_id] <= 0;
        for (integer id = 0; id < (1<<ID_BITS); id++) begin
          if (write_effect && write_ram &&
              {1'b0,write_address} < {1'b0,address[id]} + (33'd1 << size[id]) &&
              {1'b0,address[id]} < {1'b0,write_address} + (33'd1 << write_size)) valid[id] <= 0;
          if (write_effect && write_ram && axi_ar_valid && axi_ar_ready && axi_ar_bits_lock &&
              axi_ar_bits_id == ID_BITS'(id) &&
              {1'b0,write_address} < {1'b0,axi_ar_bits_addr} + (33'd1 << axi_ar_bits_size) &&
              {1'b0,axi_ar_bits_addr} < {1'b0,write_address} + (33'd1 << write_size)) valid[id] <= 0;
        end
      end
    end
  end else begin: no_exclusives
    assign write_match = 0;
  end endgenerate

  always_ff @(posedge clock) begin
    if (reset) begin
      reading <= 0; axi_r_valid <= 0; aw_held <= 0; w_held <= 0; axi_b_valid <= 0;
      serial_left <= 0; baud_count <= 0; tick_count <= 0;
    end else begin
      tick_count <= timeTick ? '0 : tick_count + 1'b1;
      if (serial_left != 0) begin
        if (baud_count == UART_BITS'(BIT_CYCLES-1)) begin
          baud_count <= 0; serial_left <= serial_left-1'b1; serial <= {1'b1,serial[9:1]};
        end else baud_count <= baud_count+1'b1;
      end
      if (axi_r_valid && axi_r_ready) axi_r_valid <= 0;
      if (axi_b_valid && axi_b_ready) axi_b_valid <= 0;
      if (axi_ar_valid && axi_ar_ready) begin
        reading <= 1; read_address <= axi_ar_bits_addr; read_id <= axi_ar_bits_id;
        read_left <= axi_ar_bits_len; read_size <= axi_ar_bits_size; read_exclusive <= axi_ar_bits_lock;
        read_error <= axi_ar_bits_size > 3 || axi_ar_bits_burst != 1 ||
            (axi_ar_bits_addr & ((32'd1 << axi_ar_bits_size)-1)) != 0 ||
            (axi_ar_bits_lock && (!ENABLE_A || axi_ar_bits_len != 0));
      end
      if (reading && !axi_r_valid) begin
        axi_r_valid <= 1; axi_r_bits_id <= read_id; axi_r_bits_last <= read_left == 0;
        axi_r_bits_resp <= read_error || (!read_ram && !read_rom) || (read_exclusive && !read_ram) ? 2'b11 : {1'b0,read_exclusive};
        axi_r_bits_data <= 0;
        if (!read_error && read_ram) axi_r_bits_data <= ram[(read_address-RAM_BASE)>>3];
        if (!read_error && read_rom && !read_exclusive) axi_r_bits_data <= 64'h0000006f0000006f;
        if (read_left == 0) reading <= 0;
        else begin read_left <= read_left-1'b1; read_address <= read_address + (32'd1 << read_size); end
      end
      if (axi_aw_valid && axi_aw_ready) begin
        aw_held <= 1; write_address <= axi_aw_bits_addr; write_id <= axi_aw_bits_id;
        write_left <= axi_aw_bits_len; write_size <= axi_aw_bits_size; write_exclusive <= axi_aw_bits_lock;
        write_error <= axi_aw_bits_len != 0 || axi_aw_bits_size > 3 || axi_aw_bits_burst != 1 ||
            (axi_aw_bits_addr & ((32'd1 << axi_aw_bits_size)-1)) != 0 || (axi_aw_bits_lock && !ENABLE_A);
      end
      if (axi_w_valid && axi_w_ready) begin
        w_held <= 1; write_data <= axi_w_bits_data; write_strobe <= axi_w_bits_strb; write_last <= axi_w_bits_last;
      end
      if (write_fire) begin
        w_held <= 0; write_error <= write_bad;
        if (write_effect && write_ram)
          for (integer lane = 0; lane < 8; lane++)
            if (write_strobe[lane]) ram[(write_address-RAM_BASE)>>3][8*lane+:8] <= write_data[8*lane+:8];
        if (write_effect && write_console) begin
          serial <= {1'b1,8'(write_data >> (8*write_address[2:0])),1'b0};
          serial_left <= 10; baud_count <= 0;
        end
        if (write_left == 0) begin
          aw_held <= 0; axi_b_valid <= 1; axi_b_bits_id <= write_id;
          axi_b_bits_resp <= write_bad ? 2'b10 : {1'b0,write_exclusive && write_match};
        end else write_left <= write_left-1'b1;
      end
    end
  end
endmodule
