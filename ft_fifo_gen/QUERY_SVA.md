```sv
// Property File for fifo_gen module

// The FIFO should not write new data when it's full
as__write_when_full: assert property (
    fifo_gen.in_val && fifo_gen.in_rdy && fifo_gen.full_reg |-> 
    $past(fifo_gen.fifo_storage_reg[fifo_gen.wr_ptr_reg]) == fifo_gen.fifo_storage_reg[fifo_gen.wr_ptr_reg]
);

// The FIFO should write new data to the current write pointer location when not full
as__correct_write_location: assert property (
    fifo_gen.in_val && fifo_gen.in_rdy && !fifo_gen.full_reg |=> 
    $past(fifo_gen.in_data) == fifo_gen.fifo_storage_reg[$past(fifo_gen.wr_ptr_reg)]
);

// The FIFO should not read data when it's empty
as__read_when_empty: assert property (
    fifo_gen.out_val && fifo_gen.out_rdy && fifo_gen.empty_reg |-> 
    $past(fifo_gen.fifo_storage_reg[fifo_gen.rd_ptr_reg]) == fifo_gen.fifo_storage_reg[fifo_gen.rd_ptr_reg]
);

// The FIFO should give out data from the current read pointer location when not empty
as__correct_read_location: assert property (
    fifo_gen.out_val && fifo_gen.out_rdy && !fifo_gen.empty_reg |-> 
    fifo_gen.out_data == fifo_gen.fifo_storage_reg[fifo_gen.rd_ptr_reg]
);

// The write pointer should not increment when the FIFO is full
as__write_pointer_increment_full: assert property (
    fifo_gen.in_val && fifo_gen.in_rdy && fifo_gen.full_reg |=> 
    $past(fifo_gen.wr_ptr_reg) == fifo_gen.wr_ptr_reg
);

// The write pointer should increment when data is written and FIFO is not full
as__write_pointer_increment: assert property (
    fifo_gen.in_val && fifo_gen.in_rdy && !fifo_gen.full_reg |=> 
    $past(fifo_gen.wr_ptr_reg) + 1 == fifo_gen.wr_ptr_reg
);

// The read pointer should not increment when the FIFO is empty
as__read_pointer_increment_empty: assert property (
    fifo_gen.out_val && fifo_gen.out_rdy && fifo_gen.empty_reg |=> 
    $past(fifo_gen.rd_ptr_reg) == fifo_gen.rd_ptr_reg
);

// The read pointer should increment when data is read and FIFO is not empty
as__read_pointer_increment: assert property (
    fifo_gen.out_val && fifo_gen.out_rdy && !fifo_gen.empty_reg |=> 
    $past(fifo_gen.rd_ptr_reg) + 1 == fifo_gen.rd_ptr_reg
);

// The FIFO should set the full flag when the next write pointer matches the read pointer
as__fifo_full_flag: assert property (
    fifo_gen.in_val && fifo_gen.in_rdy && (fifo_gen.next_wr_ptr[INFLIGHT_IDX-1:0] == fifo_gen.rd_ptr_reg) |=> 
    fifo_gen.full_reg == 1'b1
);

// The FIFO should reset the full flag when data is read
as__fifo_full_flag_reset: assert property (
    fifo_gen.out_val && fifo_gen.out_rdy |=> 
    fifo_gen.full_reg == 1'b0
);

// The FIFO should set the empty flag when the write pointer matches the next read pointer
as__fifo_empty_flag: assert property (
    fifo_gen.out_val && fifo_gen.out_rdy && (fifo_gen.wr_ptr_reg == fifo_gen.next_rd_ptr[INFLIGHT_IDX-1:0]) |=> 
    fifo_gen.empty_reg == 1'b1
);

// The FIFO should reset the empty flag when data is written
as__fifo_empty_flag_reset: assert property (
    fifo_gen.in_val && fifo_gen.in_rdy |=> 
    fifo_gen.empty_reg == 1'b0
);

// When both push and pop occur simultaneously, no change in full and empty flags should happen
as__simultaneous_push_pop: assert property (
    fifo_gen.in_val && fifo_gen.in_rdy && fifo_gen.out_val && fifo_gen.out_rdy |=> 
    $past(fifo_gen.full_reg) == fifo_gen.full_reg &&
    $past(fifo_gen.empty_reg) == fifo_gen.empty_reg
);

// In ready signal should be asserted when FIFO is not full
as__input_ready_signal: assert property (
    !fifo_gen.full_reg |-> fifo_gen.in_rdy == 1'b1
);

// Out valid signal should be asserted when FIFO is not empty
as__output_valid_signal: assert property (
    !fifo_gen.empty_reg |-> fifo_gen.out_val == 1'b1
);

```
The provided assertions check the core functionality of the FIFO module except for the reset behavior. These assertions make sure that the FIFO is correctly writing and reading data, managing its full and empty flags, and handling simultaneous push and pop operations.