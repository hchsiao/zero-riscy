`include "riscv_debug.svh"

module mem_mux
(
  // ======================================
  //           INPUT
  // ======================================
  // Instruction memory interface
  input  logic        instr_req_i,
  output logic        instr_gnt_o,
  output logic        instr_rvalid_o,
  input  logic [31:0] instr_addr_i,
  output logic [31:0] instr_rdata_o,

  // Data memory interface
  input  logic        data_req_i,
  output logic        data_gnt_o,
  output logic        data_rvalid_o,
  input  logic        data_we_i,
  input  logic [3:0]  data_be_i,
  input  logic [31:0] data_addr_i,
  input  logic [31:0] data_wdata_i,
  output logic [31:0] data_rdata_o,

  // ======================================
  //           DEBUG MODULE
  // ======================================
  // Instruction memory interface
  output logic        instr_req_dbg,
  input  logic        instr_gnt_dbg,
  input  logic        instr_rvalid_dbg,
  output logic [31:0] instr_addr_dbg,
  input  logic [31:0] instr_rdata_dbg,

  // Data memory interface
  output logic        data_req_dbg,
  input  logic        data_gnt_dbg,
  input  logic        data_rvalid_dbg,
  output logic        data_we_dbg,
  output logic [3:0]  data_be_dbg,
  output logic [31:0] data_addr_dbg,
  output logic [31:0] data_wdata_dbg,
  input  logic [31:0] data_rdata_dbg,

  // ======================================
  //           OUTPUT
  // ======================================
  // Instruction memory interface
  output logic        instr_req_o,
  input  logic        instr_gnt_i,
  input  logic        instr_rvalid_i,
  output logic [31:0] instr_addr_o,
  input  logic [31:0] instr_rdata_i,

  // Data memory interface
  output logic        data_req_o,
  input  logic        data_gnt_i,
  input  logic        data_rvalid_i,
  output logic        data_we_o,
  output logic [3:0]  data_be_o,
  output logic [31:0] data_addr_o,
  output logic [31:0] data_wdata_o,
  input  logic [31:0] data_rdata_i
);
  
  wire instr_dbg_sel = (instr_addr_i >= `PB_BASE_ADDR) && (instr_addr_i < `PB_BASE_ADDR+`PB_ADDRRNG);
  wire data_dbg_sel = (data_addr_i >= `PB_BASE_ADDR) && (data_addr_i < `PB_BASE_ADDR+`PB_ADDRRNG);

  assign instr_gnt_o = instr_dbg_sel ? instr_gnt_dbg : instr_gnt_i;
  assign instr_rvalid_o = instr_rvalid_dbg ? 1'b1 : instr_rvalid_i;
  assign instr_rdata_o = instr_rvalid_dbg ? instr_rdata_dbg : instr_rdata_i;
  assign data_gnt_o = data_dbg_sel ? data_gnt_dbg : data_gnt_i;
  assign data_rvalid_o = data_rvalid_dbg ? 1'b1 : data_rvalid_i;
  assign data_rdata_o = data_rvalid_dbg ? data_rdata_dbg : data_rdata_i;

  assign instr_req_dbg = instr_req_i && instr_dbg_sel;
  assign instr_addr_dbg = instr_addr_i - `PB_BASE_ADDR;
  assign data_req_dbg = data_req_i && data_dbg_sel;
  assign data_we_dbg = data_we_i;
  assign data_be_dbg = data_be_i;
  assign data_addr_dbg = data_addr_i - `PB_BASE_ADDR;
  assign data_wdata_dbg = data_wdata_i;

  assign instr_req_o = instr_req_i && !instr_dbg_sel;
  assign instr_addr_o = instr_addr_i;
  assign data_req_o = data_req_i && !data_dbg_sel;
  assign data_we_o = data_we_i;
  assign data_be_o = data_be_i;
  assign data_addr_o = data_addr_i;
  assign data_wdata_o = data_wdata_i;

endmodule
