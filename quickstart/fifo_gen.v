/*
This is the Specification of a FIFO queue.

# REQUIREMENTS
- The push_* interface pushes data into the FIFO
- The pop_* iterface pops data from the FIFO
- pop_data MUST BE usable the same cycle that pop_val is active.
- The module MUST handle push and pop at the same time.

Implement the following module only using synthesizable Verilog.
Append "_reg" to the name of ALL registers.
*/

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


/*
RULES:
SVA assertions are written within a property file, but DO NOT rewrite the module interface and DO NOT add includes in the property file (as we already have them in the property file).
DO NOT declare properties; DECLARE assertions named as__<NAME>: assert property (<EXPRESSION>).
DO NOT use [] within assertion NAME. Do not add @(posedge clk) to EXPRESSION.
Assertions must be as high-level as possible, to avoid repeating implementation details.
Above each assertion, write a comment explaining behavior being checked.

$countones(bitarray) returns the number of ONES in bitarray.
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
USE next-cycle assertions (|=>) when reasoning about the data being added to _reg.
DO NOT USE $past() in preconditions, ONLY in postconditions.
DO NOT USE $past() on the postcondition of same-cycle assertion (|->).
On the postcondition of next-cycle assertions (|=>), USE $past() to refer to the value of wires.
On the postcondition of next-cycle assertions (|=>), DO NOT USE $past() to refer to the updated value of _reg.
On the postcondition of next-cycle assertions (|=>), USE $past() to refer to the value of the _reg on the cycle of the precondition, before the register update.
Assertions without precondition DO NOT use |->

Internal signals are those signals NOT present in the module interface. Internal signals are declared within the module.
Referencing internal signals in the property file ALWAYS requires prepending the name of the module before the signal name, e.g., name.<internal_signal>.
NEVER reference internal signals without the module name prefix, e.g., name.<internal_signal>.
DO NOT use foreach loops in assertions; Instead, use generate loops.

TASK:
Write SVA assertions to check correctness of ALL the functionality of the module but the reset behavior.
DO NOT answer anything except for the property file, ONLY write comments within the property file.
*/