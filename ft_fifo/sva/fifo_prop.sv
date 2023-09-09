// This property file was autogenerated by AutoSVA on 2023-09-09
// to check the behavior of the original RTL module, whose interface is described below: 

module fifo_prop
#(
		parameter ASSERT_INPUTS = 0,
		parameter INFLIGHT_IDX = 2,
		parameter SIZE = 4
)
(		// Clock + Reset
		input  wire                          clk,
		input  wire                          rst_n,
		input  wire                          in_val,
		input  wire                          in_rdy, //output
		input  wire [SIZE-1:0]               in_data,
		
		input  wire                          out_val, //output
		input  wire                          out_rdy,
		input  wire [SIZE-1:0]               out_data //output
	);

//==============================================================================
// Local Parameters
//==============================================================================
localparam INFLIGHT = 2**INFLIGHT_IDX;

genvar j;
default clocking cb @(posedge clk);
endclocking
default disable iff (!rst_n);

// Re-defined wires 
wire [INFLIGHT_IDX-1:0] in_transid;
wire [INFLIGHT_IDX-1:0] out_transid;

// Symbolics and Handshake signals
wire [INFLIGHT_IDX-1:0] symb_in_transid;
am__symb_in_transid_stable: assume property($stable(symb_in_transid));
wire out_hsk = out_val && out_rdy;
wire in_hsk = in_val && in_rdy;

//==============================================================================
// Modeling
//==============================================================================

// Modeling incoming request for fifo
if (ASSERT_INPUTS) begin
	as__fifo_fairness: assert property (out_val |-> s_eventually(out_rdy));
end else begin
	am__fifo_fairness: assume property (out_val |-> s_eventually(out_rdy));
end

// Generate sampling signals and model
reg [3:0] fifo_transid_sampled;
wire fifo_transid_set = in_hsk && in_transid == symb_in_transid;
wire fifo_transid_response = out_hsk && out_transid == symb_in_transid;

always_ff @(posedge clk) begin
	if(!rst_n) begin
		fifo_transid_sampled <= '0;
	end else if (fifo_transid_set || fifo_transid_response ) begin
		fifo_transid_sampled <= fifo_transid_sampled + fifo_transid_set - fifo_transid_response;
	end
end
co__fifo_transid_sampled: cover property (|fifo_transid_sampled);
if (ASSERT_INPUTS) begin
	as__fifo_transid_sample_no_overflow: assert property (fifo_transid_sampled != '1 || !fifo_transid_set);
end else begin
	am__fifo_transid_sample_no_overflow: assume property (fifo_transid_sampled != '1 || !fifo_transid_set);
end


// Assert that if valid eventually ready or dropped valid
as__fifo_transid_hsk_or_drop: assert property (in_val |-> s_eventually(!in_val || in_rdy));
// Assert that every request has a response and that every reponse has a request
as__fifo_transid_eventual_response: assert property (|fifo_transid_sampled |-> s_eventually(out_val && (out_transid == symb_in_transid) ));
as__fifo_transid_was_a_request: assert property (fifo_transid_response |-> fifo_transid_set || fifo_transid_sampled);


// Modeling data integrity for fifo_transid
reg [SIZE-1:0] fifo_transid_data_model;
always_ff @(posedge clk) begin
	if(!rst_n) begin
		fifo_transid_data_model <= '0;
	end else if (fifo_transid_set) begin
		fifo_transid_data_model <= in_data;
	end
end

as__fifo_transid_data_unique: assert property (|fifo_transid_sampled |-> !fifo_transid_set);
as__fifo_transid_data_integrity: assert property (|fifo_transid_sampled && fifo_transid_response |-> (out_data == fifo_transid_data_model));

assign out_transid = fifo.buffer_tail_reg;
assign in_transid = fifo.buffer_head_reg;

//====DESIGNER-ADDED-SVA====//



// Property File for the fifo module

// Ensure that if the input is valid and the FIFO is ready to accept the input, the next position in the FIFO is updated.
as__in_hsk_buffer_head_update: assert property (fifo.in_hsk |=> fifo.buffer_head_reg == $past(fifo.buffer_head_reg) + 1'b1);

// Ensure that if the output is valid and ready to be taken, the position of the next data to be read from the FIFO is updated.
as__out_hsk_buffer_tail_update: assert property (fifo.out_hsk |=> fifo.buffer_tail_reg == $past(fifo.buffer_tail_reg) + 1'b1);

// Ensure that when data is written into the FIFO, it is stored in the correct slot.
generate
    for (genvar i = 0; i < INFLIGHT; i = i + 1) begin : check_data_storage
        // If a slot is selected to add data, the next cycle that slot should have the input data.
        as__add_data_to_buffer: assert property (fifo.add_buffer[i] |=> fifo.buffer_data_reg[i] == $past(fifo.in_data));

        // If a slot is being cleared (data is being read), it should have been valid before.
        as__clear_buffer_validity: assert property (fifo.clr_buffer[i] |=> $past(fifo.buffer_val_reg[i]));

        // Ensure that if a slot is selected to add data, it becomes valid in the next cycle.
        as__add_data_buffer_valid: assert property (fifo.add_buffer[i] |=> fifo.buffer_val_reg[i]);

        // If a slot was previously valid and is not being cleared, it remains valid.
        as__retain_data_in_buffer: assert property (((fifo.buffer_val_reg[i]) && !fifo.clr_buffer[i]) |=> fifo.buffer_val_reg[i]);
    end
endgenerate

// Ensure that the output data corresponds to the data in the slot pointed by buffer_tail_reg.
as__out_data_matches_tail: assert property (fifo.out_val |-> fifo.out_data == fifo.buffer_data_reg[fifo.buffer_tail_reg]);

// Ensure the FIFO indicates it's not empty if any of its slots are valid.
as__fifo_non_empty: assert property (|fifo.buffer_val_reg |-> fifo.out_val);

// Ensure that the FIFO indicates it's ready to accept data if not all of its slots are valid.
as__fifo_ready_to_accept: assert property (!(&fifo.buffer_val_reg) |-> fifo.in_rdy);



endmodule