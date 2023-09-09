// ========== Copyright Header Begin ============================================
// Copyright (c) 2020 Princeton University
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of Princeton University nor the
//       names of its contributors may be used to endorse or promote products
//       derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY PRINCETON UNIVERSITY "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL PRINCETON UNIVERSITY BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// ========== Copyright Header End ============================================

//==================================================================================================
//  Filename      : fifo_buffer.v
//  Created On    : 2020-07-02
//  Revision      :
//  Author        : Marcelo Orenes Vera
//  Company       : Princeton University
//  Email         : movera@princeton.edu
//
//  Description   : Buffer entries to accumulate before requesting
//  Buffers in a FIFO fashion, without bypass 
//  (better timing and area, but 1 cycle delay between entrance and exit)
//==================================================================================================


module fifo
  #(
    // Configuration Parameters
    parameter INFLIGHT_IDX = 2,
    parameter SIZE = 4
  )
(
    // Clock + Reset
    input  wire                          clk,
    input  wire                          rst_n,
    /*AUTOSVA
    fifo: in -IN> out
    [INFLIGHT_IDX-1:0] in_transid = fifo.buffer_head_reg
    [INFLIGHT_IDX-1:0] out_transid = fifo.buffer_tail_reg
    */
    input  wire                          in_val,
    output wire                          in_rdy,
    input  wire [SIZE-1:0]               in_data,

    output wire                          out_val,
    input  wire                          out_rdy,
    output wire [SIZE-1:0]               out_data
);

genvar j;
// Note that the number of FIFO slots is always a power of 2
localparam INFLIGHT = 2**INFLIGHT_IDX;

reg [INFLIGHT    -1:0] buffer_val_reg;
reg [INFLIGHT_IDX-1:0] buffer_head_reg;
reg [INFLIGHT_IDX-1:0] buffer_tail_reg;
reg [SIZE-1:0][INFLIGHT-1:0] buffer_data_reg;

// Hanshake
wire in_hsk  = in_val && in_rdy;
wire out_hsk = out_val && out_rdy;

wire [INFLIGHT-1:0] add_buffer;
wire [INFLIGHT-1:0] clr_buffer;
assign add_buffer = ({{INFLIGHT-1{1'b0}}, 1'b1} << buffer_head_reg) & {INFLIGHT{in_hsk}};
assign clr_buffer = ({{INFLIGHT-1{1'b0}}, 1'b1} << buffer_tail_reg) & {INFLIGHT{out_hsk}};

always @(posedge clk) begin
    if (!rst_n) begin
        buffer_head_reg <= {INFLIGHT_IDX{1'b0}};
        buffer_tail_reg <= {INFLIGHT_IDX{1'b0}};
    end else begin
        // The wrap-around is done by ignoring the MSB
        if (in_hsk) begin
            buffer_head_reg <= buffer_head_reg + {{INFLIGHT_IDX-1{1'b0}}, 1'b1};
        end
        if (out_hsk) begin
            buffer_tail_reg <= buffer_tail_reg + {{INFLIGHT_IDX-1{1'b0}}, 1'b1};
        end
    end
end

generate
    for ( j = 0; j < INFLIGHT; j = j + 1) begin: buffers_gen
        always @(posedge clk) begin
            // Bitmap of the FIFO slot that contain valid data.
            if (!rst_n) begin
              buffer_val_reg [j] <= 1'b0;
            end else begin
              buffer_val_reg[j] <= add_buffer[j] || buffer_val_reg[j] && !clr_buffer[j];
            end
        end

        always @(posedge clk) begin
            if (add_buffer[j]) begin
                buffer_data_reg[j] <= in_data;
            end 
        end
    end
endgenerate

assign out_data = buffer_data_reg[buffer_tail_reg];
assign out_val  = |buffer_val_reg;
assign in_rdy  = !(&buffer_val_reg);

endmodule

/*
RULES:
SVA assertions are written within a property file, but DO NOT rewrite the module interface and DO NOT add includes in the property file (as we already have them in the property file).
DO NOT declare properties, ONLY assertions named as__<NAME>: assert property (<EXPRESSION>).
DO NOT use [] within assertion NAME. Do not add @(posedge clk) to EXPRESSION.
Assertions must be as high-level as possible, to avoid repeating implementation details.
Above each assertion, write a comment explaining behavior being checked.

&bitarray means that ALL the bits  are ONES.
!(&bitarray) means it's NOT TRUE that ALL the bits are ONES, i.e., SOME of the bits are ZEROS.
|bitarray means that SOME bits is ONES.
!(|bitarray) means that NONE of the bits are ONES, i.e., ALL the bits are ZEROS.

Same-cycle assertions (|->): the precondition and postcondition are evaluated in the same cycle.
Next-cycle assertions (|=>): the precondition is evaluated in the current cycle and the postcondition in the next cycle.
Signals ending in _reg are registers: the assigned value changes in the next cycle.
Signals NOT ending in _reg are wires: the assigned value changes in the same cycle.
The assigned value to wires (signals NOT ending in _reg) can be referenced in the current cycle.
USE a same-cycle assertion (|->) to reason about behavior ocurring in the same cycle.
USE a next-cycle assertion (|=>) to reason about behavior ocurring in the next cycle, for example, the updated value of a _reg.
USE same-cycle assertions (|->) when reasoning about the assigned value of wires (signals NOT ending in _reg).
USE next-cycle assertions (|=>) when reasoning about the updated value of a _reg.
DO NOT USE $past() in preconditions, only in postconditions.
DO NOT USE $past() on the postcondition of same-cycle assertion (|->).
On the postcondition of next-cycle assertions (|=>), USE $past() to refer to the value of wires.
On the postcondition of next-cycle assertions (|=>), DO NOT USE $past() to refer to the updated value of _reg.
On the postcondition of next-cycle assertions (|=>), USE $past() to refer to the value of the _reg on the cycle of the precondition, before the register update.
Assertions without precondition DO NOT use |->

Internal signals are those signals NOT present in the module interface. Internal signals are declared within the module.
Referencing internal signals in the property file ALWAYS requires prepending the name of the module before the signal name, e.g., fifo.<internal_signal>.
NEVER reference internal signals without the module name prefix, e.g., fifo.<internal_signal>.
DO NOT use foreach loops in assertions; Instead, use generate loops.

TASK:
Write SVA assertions to check correctness of ALL the functionality of the module but the reset behavior.
DO NOT answer anything except for the property file, ONLY write comments within the property file.
*/
