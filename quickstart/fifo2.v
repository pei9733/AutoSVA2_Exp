module fifo2
  #(
    parameter INFLIGHT_IDX = 2, // Log2 of the number of slots
    parameter SIZE = 4 // Width of the data slot
  )
(
    // Clock + Reset
    input  wire                          clk,
    input  wire                          rst_n,

    /*AUTOSVA
    fifo: in -IN> out
    [INFLIGHT_IDX-1:0] in_transid = fifo2.wr_ptr_reg
    [INFLIGHT_IDX-1:0] out_transid = fifo2.rd_ptr_reg
    */
    input  wire                          in_val,
    output wire                          in_rdy,
    input  wire [SIZE-1:0]               in_data,

    output wire                          out_val,
    input  wire                          out_rdy,
    output wire [SIZE-1:0]               out_data
);

localparam INFLIGHT = 2**INFLIGHT_IDX;
// FIFO storage registers declaration
reg [SIZE-1:0] fifo_storage_reg[INFLIGHT-1:0];

// Write and read pointers registers
reg [INFLIGHT_IDX-1:0] wr_ptr_reg = 0, rd_ptr_reg = 0;

// Control registers
reg empty_reg = 1, full_reg = 0;

// Pointer calculations
wire [INFLIGHT_IDX:0] next_wr_ptr = wr_ptr_reg + 1'b1;
wire [INFLIGHT_IDX:0] next_rd_ptr = rd_ptr_reg + 1'b1;

// Update the FIFO status flags
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        empty_reg <= 1'b1;
        full_reg <= 1'b0;
    end else begin
        // Handle the case where both push and pop occur simultaneously
        if (in_val && in_rdy && out_val && out_rdy) begin
            // No change in full and empty flags
        end else if (in_val && in_rdy) begin // Data is pushed
            if (next_wr_ptr[INFLIGHT_IDX-1:0] == rd_ptr_reg) full_reg <= 1'b1;
            empty_reg <= 1'b0;
        end else if (out_val && out_rdy) begin // Data is popped
            if (wr_ptr_reg == next_rd_ptr[INFLIGHT_IDX-1:0]) empty_reg <= 1'b1;
            full_reg <= 1'b0;
        end
    end
end

// Write logic
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) wr_ptr_reg <= 0;
    else if (in_val && in_rdy) begin
        fifo_storage_reg[wr_ptr_reg] <= in_data;
        wr_ptr_reg <= next_wr_ptr[INFLIGHT_IDX-1:0]; // Wrapping around logic is inherently handled by the overflow of the pointer
    end
end

// Read logic
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) rd_ptr_reg <= 0;
    else if (out_val && out_rdy) begin
        rd_ptr_reg <= next_rd_ptr[INFLIGHT_IDX-1:0]; // Wrapping around logic is inherently handled by the overflow of the pointer
    end
end

// Output data assignment
assign out_data = fifo_storage_reg[rd_ptr_reg];

// Ready and valid signals
assign in_rdy = !full_reg;
assign out_val = !empty_reg;

endmodule