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
// Engineer:       Francesco Conti - f.conti@unibo.it
//
// Additional contributions by:
//                 Markus Wegmann - markus.wegmann@technokrat.ch
//
// Design Name:    RISC-V register file
// Project Name:   zero-riscy
// Language:       SystemVerilog
//
// Description:    Register file with 31 or 15x 32 bit wide registers.
//                 Register 0 is fixed to 0. This register file is based on
//                 flip flops.
//

module ariane_regfile #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg       = config_pkg::cva6_cfg_empty,
    parameter int unsigned           DATA_WIDTH    = 32,
    parameter int unsigned           ADDR_WIDTH    = 5,
    parameter int unsigned           NR_READ_PORTS = 2,
    parameter bit                    ZERO_REG_ZERO = 0
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
    // shadow csr registers
    input logic                    shadow_csr_save_i,
    input logic [CVA6Cfg.XLEN-1:0] shadow_mepc_i,
    input logic [CVA6Cfg.XLEN-1:0] shadow_mcause_i,
    // shadow csr registers
    input logic                    shadow_save_i,
    // shadow registers - read port
    input  logic [ADDR_WIDTH-1:0] shadow_raddr_i,
    output logic [DATA_WIDTH-1:0] shadow_rdata_o,
    output logic [DATA_WIDTH-1:0] shadow_sp_o,
    output logic [DATA_WIDTH-1:0] next_sp_o,
    // Trigger transfer from shadow to arch reg
    input  logic                  shadow_load_i,
    // shadow registers - write port
    input logic [ADDR_WIDTH-1:0] shadow_waddr_i,
    input logic [DATA_WIDTH-1:0] shadow_wdata_i,
    input logic shadow_we_i

);

  localparam NUM_WORDS = 2 ** ADDR_WIDTH;
  localparam NUM_WORDS_SHADOW = 16;

  logic [            NUM_WORDS-1:0][DATA_WIDTH-1:0] mem;
  logic [CVA6Cfg.NrCommitPorts-1:0][ NUM_WORDS-1:0] we_dec;

  // shadow integer register file
  logic [NUM_WORDS_SHADOW-1:0][DATA_WIDTH-1:0] mem_shadow;
  // shadow csrs
  logic [DATA_WIDTH-1:0]             shadow_mepc;
  logic [DATA_WIDTH-1:0]             shadow_mcause;
  logic [NUM_WORDS_SHADOW-1:0]       shadow_we_dec; 
  assign next_sp_o = shadow_save_i ? (mem[2] - (NUM_WORDS_SHADOW * (CVA6Cfg.XLEN / 8))) : mem[2];

  always_comb begin : we_decoder
    for (int unsigned j = 0; j < CVA6Cfg.NrCommitPorts; j++) begin
      for (int unsigned i = 0; i < NUM_WORDS; i++) begin
        if (waddr_i[j] == i) we_dec[j][i] = we_i[j];
        else we_dec[j][i] = 1'b0;
      end
    end
  end

  always_comb begin : shadow_we_decoder
    for (int unsigned i = 0; i < NUM_WORDS_SHADOW; i++) begin
      if (shadow_waddr_i == i) shadow_we_dec[i] = shadow_we_i;
      else shadow_we_dec[i] = 1'b0;
    end
  end
  //TODO:Add mechanism to block MRET if we are stil writing to a register that is going to be clobbered
  //         ^--- It might be useless, though
  // loop from 1 to NUM_WORDS-1 as R0 is nil
  always_ff @(posedge clk_i, negedge rst_ni) begin : register_write_behavioral
    if (~rst_ni) begin
      mem <= '{default: '0};
    end else begin
      for (int unsigned j = 0; j < CVA6Cfg.NrCommitPorts; j++) begin
        for (int unsigned i = 0; i < NUM_WORDS; i++) begin
          if (i == 2 && shadow_load_i) begin 
            mem[i] <= mem[i] + (NUM_WORDS_SHADOW * (CVA6Cfg.XLEN / 8));
          end else if (i == 2 && shadow_save_i) begin
            // shadow register save bumps the stack pointer too
            // TODO: if a write happens to sp at the same time as a
            // shadow_save_i request, we might lose the write..
            mem[i] <= mem[i] - (NUM_WORDS_SHADOW * (CVA6Cfg.XLEN / 8));
          end else if (we_dec[j][i]) begin
            mem[i] <= wdata_i[j];
          end
        end
        if (ZERO_REG_ZERO) begin
          mem[0] <= '0;
        end
      end
      //Writing it after, it ignores any other precedent assignment
      if(shadow_load_i)begin
        mem[1] <=  mem_shadow[0];  //ra
        mem[5] <=  mem_shadow[1];  //t0
        mem[6] <=  mem_shadow[2];  //t1
        mem[7] <=  mem_shadow[3];  //t2
        mem[10] <= mem_shadow[4];  //a0
        mem[11] <= mem_shadow[5];  //a1
        mem[12] <= mem_shadow[6];  //a2
        mem[13] <= mem_shadow[7];  //a3
        mem[14] <= mem_shadow[8];  //a4
        mem[15] <= mem_shadow[9];  //a5
        mem[16] <= mem_shadow[10]; //a6
        mem[17] <= mem_shadow[11]; //a7
        mem[28] <= mem_shadow[12]; //t3
        mem[29] <= mem_shadow[13]; //t4
        mem[30] <= mem_shadow[14]; //t5
        mem[31] <= mem_shadow[15]; //t6
      end
    end
  end

  for (genvar i = 0; i < NR_READ_PORTS; i++) begin
    assign rdata_o[i] = mem[raddr_i[i]];
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
      mem_shadow <= '{default: '0};
    end else begin
      if (shadow_save_i) begin
          mem_shadow[0] <= mem[1];   //ra
          mem_shadow[1] <= mem[5];   //t0
          mem_shadow[2] <= mem[6];   //t1
          mem_shadow[3] <= mem[7];   //t2
          mem_shadow[4] <= mem[10];  //a0
          mem_shadow[5] <= mem[11];  //a1
          mem_shadow[6] <= mem[12];  //a2
          mem_shadow[7] <= mem[13];  //a3
          mem_shadow[8] <= mem[14];  //a4
          mem_shadow[9] <= mem[15];  //a5
          mem_shadow[10] <= mem[16]; //a6
          mem_shadow[11] <= mem[17]; //a7
          mem_shadow[12] <= mem[28]; //t3
          mem_shadow[13] <= mem[29]; //t4
          mem_shadow[14] <= mem[30]; //t5
          mem_shadow[15] <= mem[31]; //t6
      end else begin
        for (int unsigned i = 0; i < NUM_WORDS_SHADOW; i++) begin
          if (shadow_we_dec[i]) begin
            mem_shadow[i] <= shadow_wdata_i;
          end
        end
      end 
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      shadow_mepc   <= '0;
      shadow_mcause <= '0;
    end else begin
      if (shadow_csr_save_i) begin
        shadow_mepc   <= shadow_mepc_i;
        shadow_mcause <= shadow_mcause_i;
      end
    end
  end
  assign shadow_rdata_o = mem_shadow[shadow_raddr_i];
  assign shadow_sp_o    = mem[2];

endmodule
