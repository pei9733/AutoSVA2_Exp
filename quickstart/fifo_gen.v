/*
This is the Specification of a FIFO queue.

# REQUIREMENTS
- The push_* interface pushes data into the FIFO
- The pop_* iterface pops data from the FIFO
- pop_data MUST BE usable the same cycle that pop_val is active.
- The module MUST handle push and pop at the same time.

// If input is valid and the FIFO is not full, then the FIFO should be ready to accept the data.
as__input_ready_when_not_full:
    assert property (fifo_gen.in_val && !fifo_gen.full_reg |-> fifo_gen.in_rdy);

// If output is requested and the FIFO is not empty, then output should be valid.
as__output_valid_when_not_empty:
    assert property (!fifo_gen.empty_reg |-> fifo_gen.out_val);

// If input is valid and FIFO is ready (not full), then the write pointer should increment in the next cycle.
as__write_pointer_increment:
    assert property (fifo_gen.in_val && fifo_gen.in_rdy |=> $past(fifo_gen.wr_ptr_reg) + 1'b1 == fifo_gen.wr_ptr_reg);

// If output is valid and FIFO is ready (not empty), then the read pointer should increment in the next cycle.
as__read_pointer_increment:
    assert property (fifo_gen.out_rdy && fifo_gen.out_val |=> $past(fifo_gen.rd_ptr_reg) + 1'b1 == fifo_gen.rd_ptr_reg);

// If write pointer wraps around, it should not increment but reset to zero.
as__write_pointer_wrap_around:
    assert property ((fifo_gen.wr_ptr_reg) == INFLIGHT-1 && fifo_gen.in_val && fifo_gen.in_rdy |=> fifo_gen.wr_ptr_reg == 0);

// If read pointer wraps around, it should not increment but reset to zero.
as__read_pointer_wrap_around:
    assert property ((fifo_gen.rd_ptr_reg) == INFLIGHT-1 && fifo_gen.out_rdy && fifo_gen.out_val |=> fifo_gen.rd_ptr_reg == 0);

as__pointers_equal_when_empty:
    assert property (fifo_gen.in_val && fifo_gen.in_rdy && (((fifo_gen.wr_ptr_reg + 1'b1) % INFLIGHT) == fifo_gen.rd_ptr_reg) && !(fifo_gen.out_val && fifo_gen.out_rdy) |=> fifo_gen.empty_reg);

as__fifo_full_condition:
    assert property (fifo_gen.out_val && fifo_gen.out_rdy && (((fifo_gen.rd_ptr_reg + 1) % INFLIGHT) == fifo_gen.wr_ptr_reg) && !(fifo_gen.in_val && fifo_gen.in_rdy) |=> fifo_gen.full_reg);

// If FIFO is not empty and output is ready, the out_data should get the value at the current read pointer.
as__out_data_on_read:
    assert property (!fifo_gen.empty_reg && fifo_gen.out_rdy |-> fifo_gen.out_data == fifo_gen.fifo_storage_reg[fifo_gen.rd_ptr_reg]);

// When input is valid, data should be written to the FIFO at the current write pointer.
as__in_data_on_write:
    assert property (fifo_gen.in_val && fifo_gen.in_rdy |=> fifo_gen.fifo_storage_reg[$past(fifo_gen.wr_ptr_reg)] == $past(fifo_gen.in_data));


Implement the following module only using synthesizable Verilog.
DO NOT write the module interface, only the implementation.
DO NOT answer anything except for the Verilog implementation, ONLY write comments within the Verilog code.
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

    /*AUTOSVA
    fifo: in -IN> out
    [INFLIGHT_IDX-1:0] in_transid = fifo_gen.wr_ptr_reg
    [INFLIGHT_IDX-1:0] out_transid = fifo_gen.rd_ptr_reg
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


/*
RULES:
SVA assertions are written within a property file, but DO NOT rewrite the module interface and DO NOT add includes in the property file (as we already have them in the property file).
DO NOT declare properties; DECLARE assertions named as__<NAME>: assert property (<EXPRESSION>).
DO NOT use [] at the end of assertion NAME. Do not add @(posedge clk) to EXPRESSION.
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