////////////////////////////////////////////////////////////////////////////////
// Copyright (C) 2017 ETH Zurich, University of Bologna                       //
// All rights reserved.                                                       //
//                                                                            //
// This code is under development and not yet released to the public.         //
// Until it is released, the code is under the copyright of ETH Zurich        //
// and the University of Bologna, and may contain unpublished work.           //
// Any reuse/redistribution should only be under explicit permission.         //
//                                                                            //
// Bug fixes and contributions will eventually be released under the          //
// SolderPad open hardware license and under the copyright of ETH Zurich      //
// and the University of Bologna.                                             //
//                                                                            //
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Prefetcher Buffer for 32 bit memory interface              //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Prefetch Buffer that caches instructions. This cuts overly //
//                 long critical paths to the instruction cache               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
import ariane_pkg::*;

module prefetch_buffer
(
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             flush_i,

  // input side
  input  logic [63:0]      fetch_address_i,
  input  logic             fetch_valid_i,
  input  branchpredict_sbe branch_predict_i,
  // output side
  input  logic             ready_i,
  output logic             valid_o,
  output fetch_entry       fetch_entry_o,

  // goes to instruction memory / instruction cache
  output logic             instr_req_o,
  input  logic             instr_gnt_i,
  output logic [63:0]      instr_addr_o,
  input  logic [31:0]      instr_rdata_i,
  input  logic             instr_rvalid_i,

  // Prefetch Buffer Status
  output logic        busy_o
);

  enum logic [1:0] {IDLE, WAIT_GNT, WAIT_RVALID, WAIT_ABORTED } CS, NS;

  logic [63:0]      fetch_address;
  logic             addr_valid;
  logic [63:0]      instr_addr_q;
  logic             fifo_valid;
  logic             fifo_ready;
  logic             fifo_clear;
  branchpredict_sbe branchpredict_q;
  //---------------------------------
  // Prefetch buffer status
  //---------------------------------
  // we are busy if we are either waiting for a grant
  // or if the fifo is full
  assign busy_o = (CS inside {WAIT_GNT, WAIT_ABORTED} && !instr_req_o) || !fifo_ready;
  assign fetch_address = {fetch_address_i[63:2], 2'b0};
  //---------------------------------
  // Fetch FIFO
  // consumes addresses and rdata
  //---------------------------------
    fetch_fifo fifo_i (
        .branch_predict_i      ( branchpredict_q   ),
        .in_addr_i             ( instr_addr_q      ),
        .in_rdata_i            ( instr_rdata_i     ),
        .in_valid_i            ( fifo_valid        ),
        .in_ready_o            ( fifo_ready        ),

        .out_valid_o           ( valid_o           ),
        .out_ready_i           ( ready_i           ),
        .*
    );

  //--------------------------------------------------
  // Instruction fetch FSM
  // deals with instruction memory / instruction cache
  //--------------------------------------------------
  always_comb begin
    instr_req_o   = 1'b0;
    instr_addr_o  = fetch_address;
    fifo_valid    = 1'b0;
    NS            = CS;

    unique case(CS)
        // default state, not waiting for requested data
        IDLE: begin
            instr_addr_o = fetch_address;
            instr_req_o  = 1'b0;

            // make a new request
            if (fifo_ready && fetch_valid_i) begin
                instr_req_o = 1'b1;
                addr_valid  = 1'b1;


                if(instr_gnt_i) //~>  granted request
                    // we have one outstanding rvalid: wait for it
                    if (flush_i)
                        NS = WAIT_ABORTED;
                    else
                        NS = WAIT_RVALID;
                else begin //~> got a request but no grant
                    NS = WAIT_GNT;
                end
            end
        end // case: IDLE

        // we sent a request but did not yet get a grant
        WAIT_GNT: begin
            instr_addr_o = {instr_addr_q[63:2], 2'b0};
            instr_req_o  = 1'b1;

            if(instr_gnt_i)
                // we have one outstanding rvalid: wait for it
                if (flush_i)
                    NS = WAIT_ABORTED;
                else
                    NS = WAIT_RVALID;
            else
                NS = WAIT_GNT;
        end // case: WAIT_GNT

          // we wait for rvalid, after that we are ready to serve a new request
        WAIT_RVALID: begin
            instr_addr_o = fetch_address;
            // prepare for next request
            if (fifo_ready && fetch_valid_i) begin
                // wait for the valid signal
                if (instr_rvalid_i) begin
                    instr_req_o = 1'b1;
                    fifo_valid  = 1'b1;
                    addr_valid  = 1'b1;

                    if (instr_gnt_i) begin
                    // we have one outstanding rvalid: wait for it
                        // if we are receiving a data item during a flush ignore it
                        if (flush_i)
                            NS = WAIT_ABORTED;
                        else
                            NS = WAIT_RVALID;
                    end else begin
                      NS = WAIT_GNT;
                    end
                end
            end else begin
                // we are requested to abort our current request
                // we didn't get an rvalid yet, so wait for it
                if (flush_i) begin
                    NS = WAIT_ABORTED;
                end
                // just wait for rvalid and go back to IDLE, no new request
                if (instr_rvalid_i) begin
                  // if we are receiving a data item during a flush ignore it
                  fifo_valid = 1'b1;
                  NS         = IDLE;
                end
            end

        end // case: WAIT_RVALID

        // our last request was aborted, but we didn't yet get a rvalid and
        // there was no new request sent yet we assume that req_i is set to high
        WAIT_ABORTED: begin
            instr_addr_o = {fetch_address_i[63:2], 2'b0};
            if (instr_rvalid_i) begin
                // we are aborting this instruction so don't tell the FIFO it is valid
                fifo_valid   = 1'b0;
                instr_req_o  = 1'b1;

                if (instr_gnt_i) begin
                    // we have one outstanding rvalid
                    if (flush_i)
                        NS = WAIT_ABORTED;
                    else
                        NS = WAIT_RVALID;
                end else begin
                    NS = WAIT_GNT;
                end
            end
        end

        default: begin
            NS          = IDLE;
            instr_req_o = 1'b0;
        end
    endcase
  end

  //-------------
  // Registers
  //-------------

  always_ff @(posedge clk_i, negedge rst_ni)
  begin
    if (~rst_ni) begin
      CS              <= IDLE;
      instr_addr_q    <= '0;
      branchpredict_q <= '{default: 0};
    end else begin
      CS              <= NS;
      if (addr_valid) begin
        instr_addr_q    <= fetch_address_i;
        branchpredict_q <= branch_predict_i;
      end
    end
  end

endmodule