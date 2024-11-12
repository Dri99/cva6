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

module extended_regfile #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg       = config_pkg::cva6_cfg_empty,
    parameter int unsigned           DATA_WIDTH    = 32,
    parameter int unsigned           NR_READ_PORTS = 2,
    parameter bit                    ZERO_REG_ZERO = 0
) (
    // clock and reset
    input  logic                                             clk_i,
    input  logic                                             rst_ni,
    // pipeline currently flushed by an exception
    input  logic                                             ex_valid_i,
    // disable clock gates for testing
    input  logic                                             test_en_i,
    // read port
    input  logic [        NR_READ_PORTS-1:0][           4:0] raddr_i,
    output logic [        NR_READ_PORTS-1:0][DATA_WIDTH-1:0] rdata_o,
    // write port
    input  logic [CVA6Cfg.NrCommitPorts-1:0][           4:0] waddr_i,
    input  logic [CVA6Cfg.NrCommitPorts-1:0][DATA_WIDTH-1:0] wdata_i,
    input  logic [CVA6Cfg.NrCommitPorts-1:0]                 we_i,
    // Data cache request ouput - CACHE
    input  dcache_req_o_t dcache_req_i,
    // Data cache request input - CACHE
    output dcache_req_i_t dcache_req_o
);

  localparam ADDR_WIDTH = 5;
  localparam REGFILE_INSTANCES = 2;
  localparam NUM_WORDS = 2 ** ADDR_WIDTH;
  localparam LOG_NR_WRITE_PORTS = CVA6Cfg.NrCommitPorts == 1 ? 1 : $clog2(CVA6Cfg.NrCommitPorts);
  localparam LOG_REGFILE_INSTANCES = REGFILE_INSTANCES == 1 ? 1 : $clog2(REGFILE_INSTANCES);

  logic [LOG_REGFILE_INSTANCES-1: 0] in_use_d,in_use_q;
  
  parameter [4:0] sp_address = 'd2;
  typedef enum logic [4:0]{ 
    t0=5,
    t1,
    t2,
    t3=28,
    t4,
    t5,
    t6,
    a0=10,
    a1,
    a2,
    a3,
    a4,
    a5,
    a6,
    a7,
    ra=1
  } saved_reg_t;

  enum logic [1:0] {
    IDLE,
    SAVE_SP,
    SAVING
  } curr_state_d, curr_state_q;

  saved_reg_t to_save_d, to_save_q;

  always_comb begin : state_cycling
    curr_state_d = curr_state_q;

    case(curr_state_q):
    IDLE : if(ex_valid_i) curr_state_d = SAVE_SP;
    SAVE_SP : curr_state_d = SAVING;
    SAVING : if(to_save_q == ra /*&& dcache_req_i.data_gnt*/) curr_state_d = IDLE;
    endcase
  end

  always_comb begin : register_saving_cycling
    to_save_d = to_save_q;
    if(curr_state_q != SAVING)
      to_save_d = t0;
    else if(/*curr_state_q == SAVING && *//*dcache_req_i.data_gnt*/ 1) 
      to_save_d = to_save_q.next()
  end
  
  // -------------------------------------
  // SP updating
  // -------------------------------------

  always_comb begin
    if(curr_state_q)
  end

  // -------------------------------------
  // Data Path
  // -------------------------------------

  logic [      NR_READ_PORTS-1:0][           4:0] raddr_arr[REGFILE_INSTANCES];
  logic [      NR_READ_PORTS-1:0][DATA_WIDTH-1:0] rdata_arr[REGFILE_INSTANCES];

  logic [CVA6Cfg.NrCommitPorts-1:0][           4:0] waddr_arr[REGFILE_INSTANCES];
  logic [CVA6Cfg.NrCommitPorts-1:0][DATA_WIDTH-1:0] wdata_arr[REGFILE_INSTANCES];
  logic [CVA6Cfg.NrCommitPorts-1:0]                 we_arr   [REGFILE_INSTANCES];

  logic [      NR_READ_PORTS-1:0][           4:0] raddr_int;
  logic [      NR_READ_PORTS-1:0][DATA_WIDTH-1:0] rdata_int;
  logic [CVA6Cfg.NrCommitPorts-1:0][           4:0] waddr_int;
  logic [CVA6Cfg.NrCommitPorts-1:0][DATA_WIDTH-1:0] wdata_int;
  logic [CVA6Cfg.NrCommitPorts-1:0]                 we_int   ;

  for (genvar i = 0; i < REGFILE_INSTANCES; i++) begin

    assign raddr_arr[i] = in_use_q == i ? raddr_i : raddr_int;
    assign rdata_arr[i] = in_use_q == i ? rdata_i : rdata_int;
    assign waddr_arr[i] = in_use_q == i ? waddr_i : waddr_int;
    assign wdata_arr[i] = in_use_q == i ? wdata_i : wdata_int;
    assign we_arr[i]    = in_use_q == i ? we_i    : we_int;

    if (CVA6Cfg.FpgaEn) begin : gen_fpga_regfile
      ariane_regfile_fpga #(
          .CVA6Cfg      (CVA6Cfg),
          .DATA_WIDTH   (CVA6Cfg.XLEN),
          .NR_READ_PORTS(CVA6Cfg.NrRgprPorts),
          .ZERO_REG_ZERO(1)
      ) i_ariane_regfile_fpga (
          .test_en_i(1'b0),
          .raddr_i  (raddr_arr[i]),
          .rdata_o  (rdata_arr[i]),
          .waddr_i  (waddr_arr[i]),
          .wdata_i  (wdata_arr[i]),
          .we_i     (we_arr[i]),
          .*
      );
    end else begin : gen_asic_regfile
      ariane_regfile #(
          .CVA6Cfg      (CVA6Cfg),
          .DATA_WIDTH   (CVA6Cfg.XLEN),
          .NR_READ_PORTS(CVA6Cfg.NrRgprPorts),
          .ZERO_REG_ZERO(1)
      ) i_ariane_regfile (
          .test_en_i(1'b0),
          .raddr_i  (raddr_arr[i]),
          .rdata_o  (rdata_arr[i]),
          .waddr_i  (waddr_arr[i]),
          .wdata_i  (wdata_arr[i]),
          .we_i     (we_arr[i]),
          .*
      );
    end
  end

  // ---------------------------------------
  //  Sequential logic
  // ---------------------------------------

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      to_save_q    <= t0;
      curr_state_q <= IDLE;
      in_use_q     <= '0;
    end else begin
      to_save_q    <= to_save_d;
      curr_state_q <= curr_state_d;
      in_use_q     <= in_use_d;
    end
  end
// NOTE: adding one read port, it may be more than needed
endmodule

/*
   localparam type dcache_req_i_t = struct packed {
      logic [CVA6Cfg.DCACHE_INDEX_WIDTH-1:0] address_index;
      logic [CVA6Cfg.DCACHE_TAG_WIDTH-1:0]   address_tag;
      logic [CVA6Cfg.XLEN-1:0]               data_wdata;
      logic [CVA6Cfg.DCACHE_USER_WIDTH-1:0]  data_wuser;
      logic                                  data_req;
      logic                                  data_we;
      logic [(CVA6Cfg.XLEN/8)-1:0]           data_be;
      logic [1:0]                            data_size;
      logic [CVA6Cfg.DcacheIdWidth-1:0]      data_id;
      logic                                  kill_req;
      logic                                  tag_valid;
    },

    localparam type dcache_req_o_t = struct packed {
      logic                                 data_gnt;
      logic                                 data_rvalid;
      logic [CVA6Cfg.DcacheIdWidth-1:0]     data_rid;
      logic [CVA6Cfg.XLEN-1:0]              data_rdata;
      logic [CVA6Cfg.DCACHE_USER_WIDTH-1:0] data_ruser;
    },

*/