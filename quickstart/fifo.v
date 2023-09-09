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
    [INFLIGHT_IDX-1:0] in_transid = fifo.buffer_head_flipflop
    [INFLIGHT_IDX-1:0] out_transid = fifo.buffer_tail_flipflop
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

reg [INFLIGHT    -1:0] buffer_val_flipflop;
reg [INFLIGHT_IDX-1:0] buffer_head_flipflop;
reg [INFLIGHT_IDX-1:0] buffer_tail_flipflop;
reg [SIZE-1:0][INFLIGHT-1:0] buffer_data_flipflop;

// Hanshake
wire in_hsk  = in_val && in_rdy;
wire out_hsk = out_val && out_rdy;

wire [INFLIGHT-1:0] add_buffer;
wire [INFLIGHT-1:0] clr_buffer;
assign add_buffer = ({{INFLIGHT-1{1'b0}}, 1'b1} << buffer_head_flipflop) & {INFLIGHT{in_hsk}};
assign clr_buffer = ({{INFLIGHT-1{1'b0}}, 1'b1} << buffer_tail_flipflop) & {INFLIGHT{out_hsk}};

always @(posedge clk) begin
    if (!rst_n) begin
        buffer_head_flipflop <= {INFLIGHT_IDX{1'b0}};
        buffer_tail_flipflop <= {INFLIGHT_IDX{1'b0}};
    end else begin
        // The wrap-around is done by ignoring the MSB
        if (in_hsk) begin
            buffer_head_flipflop <= buffer_head_flipflop + {{INFLIGHT_IDX-1{1'b0}}, 1'b1};
        end
        if (out_hsk) begin
            buffer_tail_flipflop <= buffer_tail_flipflop + {{INFLIGHT_IDX-1{1'b0}}, 1'b1};
        end
    end
end

generate
    for ( j = 0; j < INFLIGHT; j = j + 1) begin: buffers_gen
        always @(posedge clk) begin
            // Bitmap of the FIFO slot that contain valid data.
            if (!rst_n) begin
              buffer_val_flipflop [j] <= 1'b0;
            end else begin
              buffer_val_flipflop[j] <= add_buffer[j] || buffer_val_flipflop[j] && !clr_buffer[j];
            end
        end

        always @(posedge clk) begin
            if (add_buffer[j]) begin
                buffer_data_flipflop[j] <= in_data;
            end 
        end
    end
endgenerate

assign out_data = buffer_data_flipflop[buffer_tail_flipflop];
assign out_val  = |buffer_val_flipflop;
assign in_rdy  = !(&buffer_val_flipflop);

endmodule

/*
RULES:
SVA assertions are written within a property file, but DO NOT rewrite the module interface and DO NOT add includes in the property file (as we already have them in the property file).
DO NOT declare properties, ONLY assertions named as__<NAME>: assert property (<EXPRESSION>).
DO NOT use [] within assertion NAME. Do not add @(posedge clk) to EXPRESSION.
Assertions must be as high-level as possible, to avoid repeating implementation details.

&bitarray means that ALL the bits  are ONES.
!(&bitarray) means it's NOT TRUE that ALL the bits are ONES, i.e., SOME of the bits are ZEROS.
|bitarray means that SOME bits is ONES.
!(|bitarray) means that NONE of the bits are ONES, i.e., ALL the bits are ZEROS.
Constants MUSH ALWAYS have width, e.g., <WIDTH>'d<VALUE> for decimal constants.

Same-cycle assertions (|->): the precondition and postcondition are evaluated in the same cycle.
Next-cycle assertions (|=>): the precondition is evaluated in the current cycle and the postcondition in the next cycle.
Signals ending in _flipflop are flip-flops: the updated value becomes available in the next cycle.
Signals NOT ending in _flipflop are wires: the assigned value is available in the current cycle.
The assigned value to wires (signals NOT ending in _flipflop) is available in the current cycle.
Use a same-cycle assertion (|->) to reason about behavior ocurring in the same cycle.
Use a next-cycle assertion (|=>) to reason about behavior ocurring in the next cycle, for example, the updated value of a flip-flop (signals ending in _flipflop).
When reasoning about the assigned value of wires (signals NOT ending in _flipflop), use same-cycle assertions (|->).
When reasoning about the updated value of a flipflop (signals ending in _flipflop), use next-cycle assertions (|=>).
When referencing wires on the postcondition of a next-cycle assertion (|=>), USE $past() to refer to the value of the wires on the cycle of the precondition.
When referencing flip-flops on the postcondition of a next-cycle assertion (|=>), we DO NOT USE $past() to refer to the updated value of the flip-flop.
When referencing flip-flops on the postcondition of a next-cycle assertion (|=>), we USE $past() to refer to the value of the flip-flop on the cycle of the precondition.
When referencing flip-flops on the postcondition of a same-cycle assertion (|->), we DO NOT USE $past() to refer to the current value of the flip-flop (before the update).
Assertions without precondition DO NOT use |->

Internal signals are those signals NOT present in the module interface. Internal signals are declared within the module.
Referencing internal signals in assertions ALWAYS requires prepending the name of the module before the signal name, e.g., fifo.<internal_signal>.
NEVER reference internal signals without the module name prefix, e.g., fifo.<internal_signal>.
EVERY time you reference an internal signal in an assertion, you MUST specify the module name prefix.
Do not use foreach loops in assertions; Instead, use generate loops.

TASK:
Write SVA assertions to check correctness of ALL the functionality of the module but the reset behavior.
Do not write explanations outside the property file, but you can write comments within the property file.
*/
