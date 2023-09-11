
module fifo
  #(
    // Configuration Parameters
    parameter INFLIGHT_IDX = 2,
    parameter SIZE = 4
  )
(

    // LLM-generated annotations (correct)
    /*AUTOSVA
    fifo_transaction: in -IN> out
                        in_val = in_val
                        in_ready = in_rdy
    [SIZE-1:0]         in_data = in_data
    [INFLIGHT_IDX-1:0] in_transid = buffer_head_reg
                        out_val = out_val
                        out_ready = out_rdy
    [SIZE-1:0]         out_data = out_data
    [INFLIGHT_IDX-1:0] out_transid = buffer_tail_reg
    */

    // Human-generated annotations (correct)
    /*AUTOSVA
    fifo: in -IN> out
    [INFLIGHT_IDX-1:0] in_transid = fifo_gen.wr_ptr_reg
    [INFLIGHT_IDX-1:0] out_transid = fifo_gen.rd_ptr_reg
    */

    // PROMPT (the rest of the file)
    
    // Clock + Reset
    input  wire                          clk,
    input  wire                          rst_n,

    input  wire                          in_val,
    output wire                          in_rdy,
    input  wire [SIZE-1:0]               in_data,

    output wire                          out_val,
    input  wire                          out_rdy,
    output wire [SIZE-1:0]               out_data
);

genvar j;
// Note that the number of fifo slots is always a power of 2
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
            // Bitmap of the fifo slot that contain valid data.
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
AutoSVA is a tool that generates SVA assertions for RTL module transactions.
The SVA assertions are written from the perspective of the RTL module that is the design-under-test (DUT).
An RTL module has input and output signals in the module interface.
Groups of signals in the module interface are called interfaces.
Pairs of interfaces denote transactions: a transaction connects a request interface to a response interface.
A request interface can be output by the DUT (outgoing transations), and so a response is expected to be received by the DUT eventually via an input reponse interface.
A request interface can be an input to the DUT (incoming transations), and so a response is expected to be sent by the DUT eventually via an output reponse interface.
AutoSVA requires annotations into the signal declaration section of the module interface to identify the interfaces and transactions.
The annotations are written as a multi-line Verilog comment starting with /*AUTOSVA 
A transation is defines as: transaction_name: request_interface -IN> response_interface if it's an incoming transaction. Thus the request interface is the input interface and the response interface is the output interface.
A transation is alternatively defined as: transaction_name: request_interface -OUT> response_interface if it's an outgoing transaction. Thus the request interface is the output interface and the response interface is the input interface.
For example, the following FIFO module interface has an incoming transaction called fifo_transaction: push -IN> pop
module fifo (
input  wire             push_val,
output wire             push_rdy,
input  wire [WIDTH-1:0] push_payload,
output wire             pop_val,
input  wire             pop_rdy,
output wire [WIDTH-1:0] pop_payload
);
and so the AUTOSVA annotation is:
/*AUTOSVA
fifo_transaction: push -IN> pop
                    push_valid = push_val
                    push_ready = push_rdy
[WIDTH-1:0]         push_data = push_payload
[INFLIGHT_IDX-1:0]  push_transid = fifo.write_pointer
                    pop_valid = pop_val
                    pop_ready = pop_rdy
[WIDTH-1:0]         pop_data = pop_payload
[INFLIGHT_IDX-1:0]  pop_transid = fifo.read_pointer

NOTE that in addition to the fifo_transaction: push -IN> pop there are more annotations that match interface signals with interface atributes.
Both request and response interfaces have valid, ready, data and transid attributes.
Valid indicates that the request or response is valid, and can be acknowledged by the other side.
Ready indicates that the request or response is ready to be received by the other side.
Data is the payload of the request or response.
Transid is a unique identifier of the request or response.

The formalized syntax of the AUTOSVA annotation is:
TRANSACTION ::= TNAME: RELATION ATTRIB
RELATION ::= P −in> Q | P −out> Q
ATTRIB ::= ATTRIB, ATTRIB | SIG = ASSIGN | input SIG | outputSIG
SIG ::= [STR:0] FIELD | STR FIELD
FIELD ::= P SUFFIX | Q SUFFIX
SUFFIX ::= val | ack | transid | transid unique | active | stable | data
TNAME, P, Q ::= STR

YOU MUST LEARN THE RULES ABOVE, THEN ANALYZE the RTL module interface and implementation and WRITE AUTOSVA annotations.
DO NOT answer anything except for the annotations.
*/