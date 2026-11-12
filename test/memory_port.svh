// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
typedef struct packed {
`ifdef DEBUG_MEMORY
  logic debug;
`endif
  logic [63:0] address, data;
  logic [2:0] size;
  logic [7:0] mask, tag;
  logic write, fetch, privileged, atomic;
  logic [4:0] atomicOperation;
  logic scEligible;
  logic [2:0] refillSize;
  logic [1:0] cacheOperation;
  logic [1:0] pbmt;
} request_t;
typedef struct packed { logic [63:0] data; logic fault; logic [7:0] tag; logic last; } response_t;
interface memory_port;
  logic request_ready, request_valid, response_ready, response_valid;
  request_t request;
  response_t response;
endinterface
`ifdef DEBUG_MEMORY
`define DEBUG_PORT(P, B) .P``_request_bits_debug(B.request.debug),
`else
`define DEBUG_PORT(P, B)
`endif
`ifdef PBMT
`define PBMT_PORT(P, B) .P``_request_bits_pbmt(B.request.pbmt),
`else
`define PBMT_PORT(P, B)
`endif
`define PORT(P, B) \
  `DEBUG_PORT(P, B) \
  `PBMT_PORT(P, B) \
  .P``_request_ready(B.request_ready), .P``_request_valid(B.request_valid), \
  .P``_request_bits_address(B.request.address), .P``_request_bits_data(B.request.data), \
  .P``_request_bits_size(B.request.size), .P``_request_bits_mask(B.request.mask), \
  .P``_request_bits_tag(B.request.tag), .P``_request_bits_write(B.request.write), \
  .P``_request_bits_fetch(B.request.fetch), .P``_request_bits_atomic(B.request.atomic), \
  .P``_request_bits_privileged(B.request.privileged), \
  .P``_request_bits_atomicOperation(B.request.atomicOperation), .P``_request_bits_scEligible(B.request.scEligible), \
  .P``_request_bits_cacheOperation(B.request.cacheOperation), \
  .P``_request_bits_refillSize(B.request.refillSize), .P``_response_ready(B.response_ready), \
  .P``_response_valid(B.response_valid), .P``_response_bits_data(B.response.data), \
  .P``_response_bits_fault(B.response.fault), .P``_response_bits_tag(B.response.tag), .P``_response_bits_last(B.response.last)
