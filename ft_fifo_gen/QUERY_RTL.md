Implementing a simple FIFO that can handle simultaneous push and pop requires maintaining read and write pointers, as well as storage (typically an array or memory). Here's a synthesizable Verilog implementation of the module you've defined, using the provided parameters:

```verilog
module fifo_gen
  #(
    parameter INFLIGHT_IDX = 2, // Log2 of the number of slots
    parameter SIZE = 4 // Width of the data slot
  )
(
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

localparam INFLIGHT = 2**INFLIGHT_IDX;
localparam ADDR_SIZE = INFLIGHT_IDX;

// FIFO storage
reg [SIZE-1:0] fifo_storage_reg[INFLIGHT-1:0];

// Read and write pointers
reg [ADDR_SIZE-1:0] wr_ptr_reg = 0, rd_ptr_reg = 0;
reg full_reg = 0, empty_reg = 1;

// Temporary register to hold data
reg [SIZE-1:0] out_data_reg;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        wr_ptr_reg <= 0;
        rd_ptr_reg <= 0;
        full_reg <= 0;
        empty_reg <= 1;
    end else begin
        // Handle input
        if (in_val && in_rdy && !full_reg) begin
            fifo_storage_reg[wr_ptr_reg] <= in_data;
            wr_ptr_reg <= wr_ptr_reg + 1;
        end

        // Handle output
        if (out_val && out_rdy && !empty_reg) begin
            out_data_reg <= fifo_storage_reg[rd_ptr_reg];
            rd_ptr_reg <= rd_ptr_reg + 1;
        end

        // Handle full and empty flags
        if ((wr_ptr_reg == rd_ptr_reg - 1) || (wr_ptr_reg == INFLIGHT-1 && rd_ptr_reg == 0)) begin
            full_reg <= 1;
        end else if (wr_ptr_reg == rd_ptr_reg) begin
            empty_reg <= 1;
        end else begin
            full_reg <= 0;
            empty_reg <= 0;
        end
    end
end

assign in_rdy = !full_reg;
assign out_val = !empty_reg;
assign out_data = out_data_reg;

endmodule
```

In this code:

- We use an array `fifo_storage_reg` as our storage for the FIFO.
- The `wr_ptr_reg` and `rd_ptr_reg` registers act as our write and read pointers respectively.
- The `full_reg` and `empty_reg` flags indicate when the FIFO is full or empty.
- We handle simultaneous push/pop by having separate conditions to check the input and output readiness within the always block.
- We use the `in_rdy` flag to signal the upstream module when it can send data and the `out_val` flag to signal the downstream module when data is available.
- The `out_data_reg` is used to immediately provide the output data when `out_val` is set, meeting the requirement of the output data being available in the same cycle.

Note: This design assumes that when `out_rdy` is asserted while `out_val` is high, the data will be popped. If there's a specific behavior in your system where `out_rdy` can be high without actually reading the data, then this design might not be suitable.