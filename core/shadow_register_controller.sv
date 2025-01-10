// Copyright 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// Author: Robert Balas <balasr@iis.ee.ethz.ch>
module shadow_register_controller 
import ariane_pkg::*;
#(
  parameter config_pkg::cva6_cfg_t CVA6Cfg          = config_pkg::cva6_cfg_empty,
  parameter type                   fu_data_t        = logic,
  parameter type                   dcache_req_i_t   = logic,
  parameter type                   dcache_req_o_t   = logic,
  parameter int unsigned           ADDR_WIDTH       = 6,
  parameter int unsigned           DATA_WIDTH       = 32,
  parameter int unsigned           NUM_SHADOW_SAVES = 16
) (
  input logic                   clk_i,
  input logic                   rst_ni,
  // Trigger save logic - ISSUE STAGE
  input logic shadow_reg_save_i,
  // whether we are ready to process another interrupt (for nesting)
  output logic                  shadow_ready_o,
  output logic [ADDR_WIDTH-1:0] shadow_save_level_o,
  // shadow register read port
  output logic [ADDR_WIDTH-1:0] shadow_reg_raddr_o,
  input logic [DATA_WIDTH-1:0]  shadow_reg_rdata_i,
  input logic [DATA_WIDTH-1:0]  shadow_reg_sp_i,
  // FU data from SHReg Unit is valid - EX STAGE 
  output logic shru_valid_o,
  // FU data for storing shadow regs - EX STAGE
  output fu_data_t shru_fu_data_o,
  // Store of shadow register is valid - EX STAGE
  input logic shru_store_valid_i,
  // LSU can accept a new instruction
  input logic lsu_ready_i,
  // Page offset Load unit wants to load - EX STAGE
  input logic [11:0] page_offset_i,
  // Page offset is being saved in ShRU - EX STAGE
  output logic page_offset_matches_shru_o,
  // Data cache request ouput - CACHE
  input  dcache_req_o_t [1:0] dcache_req_ports_i,
  // Data cache request input - CACHE
  output dcache_req_i_t [1:0] dcache_req_ports_o,
  // Csr read port - 
  input  logic [ADDR_WIDTH-1:0] csr_raddr_i,
  output logic [DATA_WIDTH-1:0] csr_rdata_o,
  // Request to begin an asynchronous load - CSR
  input  logic shru_load_valid_i,
  // Load request accepted - CSR
  output  logic shru_load_ack_o,
  // Register not yet loaded - CSR
  output logic [ADDR_WIDTH-1:0] shadow_load_level_o,
  // Request to commit an mret - COMMIT STAGE
  input logic mret_valid_i,
  // Mret request accepted - COMMIT STAGE
  output logic mret_ready_o,
  // Exception stack frame to load from - CSR
  input logic [DATA_WIDTH-1:0]  shadow_load_esf_i
);
  logic [ADDR_WIDTH-1:0]   cnt_q, cnt_d;
  logic [DATA_WIDTH-1:0]   stack_q, stack_d;
  logic [CVA6Cfg.PLEN-1:0] save_p_addr;
  localparam int unsigned SHADOW_RELOAD = NUM_SHADOW_SAVES - 1;
  typedef enum logic [1:0] {
    IDLE_SAVE, SAVE
  } save_state_e;
  save_state_e save_state_d, save_state_q;

  assign shru_fu_data_o.fu = STORE;
  assign shru_fu_data_o.operation = SHSR;
  assign shru_fu_data_o.operand_a= stack_q; // TODO: or stack_q
  assign shru_fu_data_o.operand_b= shadow_reg_rdata_i;
  assign shru_fu_data_o.imm      = 'b0;
  assign shru_fu_data_o.trans_id = 'b0; //TODO: maybe change with something useful

  //TODO: for now we assume that this process is always done with translation disabled
  assign save_p_addr = (CVA6Cfg.PLEN)'(stack_q[((CVA6Cfg.PLEN > CVA6Cfg.VLEN) ? CVA6Cfg.VLEN -1: CVA6Cfg.PLEN -1 ):0]);
  assign dcache_req_ports_o[0].address_index = save_p_addr[CVA6Cfg.DCACHE_INDEX_WIDTH-1:0];    
  assign dcache_req_ports_o[0].address_tag   = save_p_addr[CVA6Cfg.DCACHE_TAG_WIDTH     +
                                              CVA6Cfg.DCACHE_INDEX_WIDTH-1 :
                                              CVA6Cfg.DCACHE_INDEX_WIDTH];
  assign dcache_req_ports_o[0].data_wdata    = shadow_reg_rdata_i;     
  assign dcache_req_ports_o[0].data_wuser    = '0;
  assign dcache_req_ports_o[0].data_we       = '1;
  assign dcache_req_ports_o[0].data_size     = extract_transfer_size(CVA6Cfg.XLEN == 32? SW : SD);
  assign dcache_req_ports_o[0].data_id       = '0; 
  assign dcache_req_ports_o[0].kill_req      = '0;   
  assign dcache_req_ports_o[0].tag_valid     = '0;   
  
  if (CVA6Cfg.IS_XLEN64) begin : gen_8b_be
    assign dcache_req_ports_o[0].data_be     = be_gen(stack_q[2:0], extract_transfer_size(SD));
  end else begin : gen_4b_be
    assign dcache_req_ports_o[0].data_be     = be_gen_32(stack_q[1:0], extract_transfer_size(SW));
  end
   
  //TODO: add SVA to check that we only save in Machine mode
  always_comb begin
    logic [DATA_WIDTH-1:0]stack_bottom = stack_q - cnt_q * (CVA6Cfg.XLEN/8);
    save_state_d = save_state_q;
    cnt_d = cnt_q;
    stack_d = stack_q;

    shru_valid_o = 1'b0;
    shadow_ready_o = 1'b1;
    page_offset_matches_shru_o = '0;
    dcache_req_ports_o[0].data_req = '0;
    unique case (save_state_q)
      IDLE_SAVE: begin
        cnt_d = SHADOW_RELOAD;
        if (shadow_reg_save_i) begin
          save_state_d = SAVE;
          // the stack register points to the last already used address
          stack_d      = shadow_reg_sp_i - (CVA6Cfg.XLEN/8);
        end
      end
      SAVE: begin
        // write reg to stack
        //shru_valid_o = lsu_ready_i;
        dcache_req_ports_o[0].data_req = '1;
        shadow_ready_o = 1'b0;
        // the shadow register now contain the interrupt context
        if (dcache_req_ports_i[0].data_gnt) begin
          if (cnt_q == 0) begin
            save_state_d = IDLE_SAVE;
            cnt_d        = SHADOW_RELOAD;
            stack_d      = 32'b0;
          end else begin
            cnt_d = cnt_q - 1;
            stack_d = stack_q - (CVA6Cfg.XLEN/8);
          end
        end
        if (stack_q[11:3] >= page_offset_i[11:3] && page_offset_i[11:3] >= stack_bottom[11:3] ) page_offset_matches_shru_o = '1;
      end
      default:;
    endcase // unique case (save_state_q)
  end

  assign shadow_save_level_o = cnt_q;
  assign shadow_reg_raddr_o = shadow_ready_o ? csr_raddr_i : cnt_q;
  assign csr_rdata_o = shadow_ready_o ? shadow_reg_rdata_i : {(CVA6Cfg.XLEN/8){8'haa}};
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      save_state_q <= IDLE_SAVE;
      stack_q      <= '0;
      cnt_q        <= SHADOW_RELOAD;
    end else begin
      save_state_q <= save_state_d;
      stack_q      <= stack_d;
      cnt_q        <= cnt_d;
    end
  end

///////////////////////////////////////////////////////////////////////////
//                           Load Logic                                  //
///////////////////////////////////////////////////////////////////////////

  typedef enum logic [1:0] {
    IDLE_LOAD, LOADING, LD_READY
  } load_state_e;
  load_state_e load_state_d, load_state_q;
  logic [ADDR_WIDTH-1:0] load_cnt_d, load_cnt_q;
  logic [CVA6Cfg.PLEN-1:0] load_p_addr;
  logic [DATA_WIDTH-1:0] load_address;
  logic [DATA_WIDTH-1:0] load_value;

  //TODO: for now we assume that this process is always done with translation disabled
  //TODO: We will have to understant what to do when user mode will be enabled
  assign load_p_addr = (CVA6Cfg.PLEN)'(load_address[((CVA6Cfg.PLEN > CVA6Cfg.VLEN) ? CVA6Cfg.VLEN -1: CVA6Cfg.PLEN -1 ):0]);
  assign dcache_req_ports_o[1].address_index = load_p_addr[CVA6Cfg.DCACHE_INDEX_WIDTH-1:0];    
  assign dcache_req_ports_o[1].address_tag   = load_p_addr[CVA6Cfg.DCACHE_TAG_WIDTH     +
                                              CVA6Cfg.DCACHE_INDEX_WIDTH-1 :
                                              CVA6Cfg.DCACHE_INDEX_WIDTH];
  assign dcache_req_ports_o[1].data_wdata    = '0;     
  assign dcache_req_ports_o[1].data_wuser    = '0;
  assign dcache_req_ports_o[1].data_we       = '0;
  assign dcache_req_ports_o[1].data_size     = extract_transfer_size(CVA6Cfg.XLEN == 32? SW : SD);
  assign dcache_req_ports_o[1].data_id       = '0; //For now we send one request at a time
  assign dcache_req_ports_o[1].kill_req      = '0; //For now a loading cannot be interrupted and doesn't generate exceptions
  assign dcache_req_ports_o[1].tag_valid     = '1; //Skips mmu as we work in machine mode only
  
  if (CVA6Cfg.IS_XLEN64) begin : gen_8b_be
    assign dcache_req_ports_o[1].data_be     = be_gen(load_address[2:0], extract_transfer_size(SD));
  end else begin : gen_4b_be
    assign dcache_req_ports_o[1].data_be     = be_gen_32(load_address[1:0], extract_transfer_size(SW));
  end

  assign load_address = (DATA_WIDTH)'(load_cnt_q) + shadow_load_esf_i;
  assign load_value = dcache_req_ports_i[1].data_rdata;

  always_comb begin
    shru_load_ack_o = 1'b0;
    load_state_d = load_state_q;
    load_cnt_d = load_cnt_q;
    mret_ready_o = 1'b1;

    unique case(load_state_q)
    IDLE_LOAD: begin
      load_cnt_d = SHADOW_RELOAD;
      mret_ready_o = 1'b1;
      if(shru_load_valid_i) begin
        shru_load_ack_o = 1'b1;
        load_state_d = LOADING;
      end
    end
    LOADING: begin
      dcache_req_ports_o[1].data_req = '1;

      if(dcache_req_ports_i[1].data_rvalid) begin
        load_cnt_d = load_cnt_q - 5'b1;

      end
      mret_ready_o = 1'b0;
      if(load_cnt_q == 5'b0) begin
        load_state_d = LD_READY;
      end
    end
    LD_READY: begin
      mret_ready_o = 1'b1;
      if(mret_valid_i == 1'b1)begin
        load_state_d = IDLE_LOAD;
      end
    end
    endcase
  end

  always_ff@(posedge clk_i or negedge rst_ni) begin 
    if(!rst_ni)begin 
      load_state_q <= IDLE_LOAD;
      load_cnt_q   <= SHADOW_RELOAD;
    end else begin   
      load_state_q <= load_state_d;
      load_cnt_q   <= load_cnt_d;
    end
  end

    // TODO: Use CV32E40P_ASSERT_ON
`ifndef SYNTHESIS
  a_shadow_controller_acces_while_saving: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    save_state_q == SAVE |-> !shadow_reg_save_i)
    else
      $error("shadow register access is out of range");
`ifndef VERILATOR
`endif
`endif
endmodule