// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author : Alessandro Mandrile
//
//
// Description:    This wrapper around the standard register file replicates two or more copies.
//                 In case of exception, the active register file becomes inactive and another one
//                 starts receiving commands from the processor, while the old is saved on the stack.
//

module extended_regfile 
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg        = config_pkg::cva6_cfg_empty,
    parameter type                   fu_data_t      = logic,
    parameter type                   dcache_req_i_t = logic,
    parameter type                   dcache_req_o_t = logic,
    parameter int unsigned           DATA_WIDTH     = 32,
    parameter int unsigned           NR_READ_PORTS  = 2,
    parameter bit                    ZERO_REG_ZERO  = 0
) (
    // clock and reset
    input  logic                                             clk_i,
    input  logic                                             rst_ni,
    // disable clock gates for testing
    input  logic                                             test_en_i,
    // read port
    input  logic [        NR_READ_PORTS-1:0][           4:0] raddr_i,
    output logic [        NR_READ_PORTS-1:0][DATA_WIDTH-1:0] rdata_o,
    // write port
    input  logic [CVA6Cfg.NrCommitPorts-1:0][           4:0] waddr_i,
    input  logic [CVA6Cfg.NrCommitPorts-1:0][DATA_WIDTH-1:0] wdata_i,
    input  logic [CVA6Cfg.NrCommitPorts-1:0]                 we_i,
    // Trigger save logic - ISSUE STAGE
    output logic shadow_reg_save_i,
    output logic [DATA_WIDTH-1:0] next_sp_o,
    // CSR values to shadow - CSR Regfile
    input  logic [DATA_WIDTH-1:0] shadow_mepc_i,
    input  logic [DATA_WIDTH-1:0] shadow_mcause_i,
    // FU data from SHReg Unit is valid - EX STAGE 
    output logic     shru_valid_o,
    // FU data for storing shadow regs - EX STAGE
    output fu_data_t shru_fu_data_o,
    // Store of shadow register is valid - EX STAGE
    input  logic     shru_store_valid_i,
    // Shadow register unit can handle another exception - ISSUE
    output logic shru_store_ready_o,
    // Shadow register currently saving - CSR
    output logic [4:0] shru_save_level_o,
    // LSU can accept a new instruction
    input  logic     lsu_ready_i,
    // Page offset Load unit wants to load - EX STAGE
    input logic [11:0] page_offset_i,
    // Page offset is being saved in ShRU - EX STAGE
    output logic page_offset_matches_shru_o,
    // Data cache request ouput - CACHE
    input  dcache_req_o_t dcache_req_i,
    // Data cache request input - CACHE
    output dcache_req_i_t dcache_req_o
);
  localparam int unsigned ADDR_WIDTH = 5;
  logic [ADDR_WIDTH-1:0] shadow_raddr_sh_ctrl_rf;
  logic [DATA_WIDTH-1:0] shadow_rdata_rf_sh_ctrl;
  logic [DATA_WIDTH-1:0] shadow_sp_rf_sh_ctrl;
//TODO: To understand if another signal is better to drive shadow_csr_save,  and 

  ariane_regfile #(
      .CVA6Cfg      (CVA6Cfg),
      .DATA_WIDTH   (CVA6Cfg.XLEN),
      .ADDR_WIDTH   (ADDR_WIDTH),
      .NR_READ_PORTS(CVA6Cfg.NrRgprPorts),
      .ZERO_REG_ZERO(1)
  ) i_ariane_regfile_ff (
      .shadow_csr_save_i(shadow_reg_save_i),
      .shadow_save_i  (shadow_reg_save_i),
      .shadow_raddr_i (shadow_raddr_sh_ctrl_rf),
      .shadow_rdata_o (shadow_rdata_rf_sh_ctrl),
      .shadow_sp_o    (shadow_sp_rf_sh_ctrl),
      .test_en_i,
      .raddr_i,
      .rdata_o,
      .waddr_i,
      .wdata_i,
      .we_i,
      .shadow_mepc_i,
      .shadow_mcause_i,
      .next_sp_o,
      .*
  );

  shadow_register_controller #(
      .CVA6Cfg          (CVA6Cfg),
      .fu_data_t        (fu_data_t),
      .dcache_req_i_t   (dcache_req_i_t),
      .dcache_req_o_t   (dcache_req_o_t),
      .ADDR_WIDTH       (ADDR_WIDTH),
      .DATA_WIDTH       (CVA6Cfg.XLEN),
      .NUM_SHADOW_SAVES (16)
  ) i_shadow_register_controller (
      .shadow_reg_save_i,
      .shadow_ready_o      (shru_store_ready_o),
      .shadow_save_level_o (shru_save_level_o),
      .shadow_reg_raddr_o  (shadow_raddr_sh_ctrl_rf),
      .shadow_reg_rdata_i  (shadow_rdata_rf_sh_ctrl),
      .shadow_reg_sp_i     (shadow_sp_rf_sh_ctrl),
      .shru_valid_o,
      .shru_fu_data_o,
      .shru_store_valid_i,
      .lsu_ready_i,
      .page_offset_i,
      .page_offset_matches_shru_o,
      .dcache_req_i,
      .dcache_req_o,
      .*
  );

endmodule

