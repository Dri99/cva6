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
// Author: Alessandro Mandrile, Unito
// Date: 21.10.2024
// Description: Cycles counters


module cyc_counters
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg        = config_pkg::cva6_cfg_empty,
    parameter int unsigned           CycAccountRegs = 8
) (
    input logic clk_i,
    input logic rst_ni,
    input logic debug_mode_i,  // debug mode
    // SRAM like interface
    input logic [11:0] addr_i,  // read/write address (up to 6 counters possible)
    input logic we_i,  // write enable
    input logic [CVA6Cfg.XLEN-1:0] data_i,  // data to write
    output logic [CVA6Cfg.XLEN-1:0] data_o  // data to read
);

  logic [63:0] cyc_accounting_d[CycAccountRegs-1:0];
  logic [63:0] cyc_accounting_q[CycAccountRegs-1:0];

  typedef struct packed{
    logic [15:0] counter_en;
    logic [15:0] counter_sel;  
  } cyc_accounting_status_t; 

  cyc_accounting_status_t cyc_accounting_status_q, cyc_accounting_status_d;

  cyc_accounting_status_t casted_data_i;

  //internal signal to keep track of exception
  logic read_access_exception, update_access_exception;


  always_comb begin : cyc_counter
    cyc_accounting_d = cyc_accounting_q;
    data_o = 'b0;
    read_access_exception = 1'b0;
    update_access_exception = 1'b0;
    cyc_accounting_status_d = cyc_accounting_status_q;
    casted_data_i = cyc_accounting_status_t'(data_i[31:0]);
    // Increment the enabled counter
    if ((!debug_mode_i) && (!we_i)) begin
      cyc_accounting_d[cyc_accounting_status_q.counter_en] = cyc_accounting_q[cyc_accounting_status_q.counter_en] + 1'b1;
    end

    //Read
    unique case(addr_i) 
      riscv::CSR_CNT_DATA: begin
        if (riscv::XLEN == 32) begin
          data_o = cyc_accounting_q[cyc_accounting_status_q.counter_sel][31:0];
        end else begin
          data_o = cyc_accounting_q[cyc_accounting_status_q.counter_sel];
        end
      end 
      riscv::CSR_CNT_DATA_H: begin
        if (riscv::XLEN == 32) begin
          data_o = cyc_accounting_q[cyc_accounting_status_q.counter_sel][63:32];
        end else begin
          read_access_exception = 1'b1;
        end
      end 
      riscv::CSR_CNT_STATUS: begin
        data_o[31:0] = cyc_accounting_status_q[31:0];
      end 
      default: read_access_exception = 1'b1;
    
    endcase
    

    //Write
    if (we_i) begin
      unique case(addr_i) 
        riscv::CSR_CNT_DATA: begin
          if (riscv::XLEN == 32)
            cyc_accounting_d[cyc_accounting_status_q.counter_sel][31:0]  = data_i;
          else 
            cyc_accounting_d[cyc_accounting_status_q.counter_sel] =        data_i;
        end 
        riscv::CSR_CNT_DATA_H: begin
          if (riscv::XLEN == 32) 
            cyc_accounting_d[cyc_accounting_status_q.counter_sel][63:32] = data_i;
           else 
            update_access_exception = 1'b1;          
        end 
        riscv::CSR_CNT_STATUS: begin
          if(casted_data_i.counter_sel < CycAccountRegs && 
              casted_data_i.counter_en < CycAccountRegs )
          cyc_accounting_status_d = data_i[31:0];
        end 
        default: read_access_exception = 1'b1;
      
      endcase
    end
  end

  //Registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cyc_accounting_q        <= '{default: 0};
      cyc_accounting_status_q <= '{default: 0};
    end else begin
      cyc_accounting_q        <= cyc_accounting_d;
      cyc_accounting_status_q <= cyc_accounting_status_d;
    end
  end

endmodule
