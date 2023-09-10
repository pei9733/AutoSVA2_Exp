```sv
// Property File for fifo_gen

// If input is valid and the FIFO is not full, then the FIFO should be ready to accept the data.
as__input_ready_when_not_full:
    assert property (fifo_gen.in_val && !fifo_gen.full_reg |-> fifo_gen.in_rdy);

// If output is requested and the FIFO is not empty, then output should be valid.
as__output_valid_when_not_empty:
    assert property (fifo_gen.out_rdy && !fifo_gen.empty_reg |-> fifo_gen.out_val);

// If input is valid and FIFO is ready (not full), then the write pointer should increment in the next cycle.
as__write_pointer_increment:
    assert property (fifo_gen.in_val && fifo_gen.in_rdy |=> $past(fifo_gen.wr_ptr_reg) + 1 == fifo_gen.wr_ptr_reg);

// If output is valid and FIFO is ready (not empty), then the read pointer should increment in the next cycle.
as__read_pointer_increment:
    assert property (fifo_gen.out_rdy && fifo_gen.out_val |=> $past(fifo_gen.rd_ptr_reg) + 1 == fifo_gen.rd_ptr_reg);

// If write pointer wraps around, it should not increment but reset to zero.
as__write_pointer_wrap_around:
    assert property ($past(fifo_gen.wr_ptr_reg) == INFLIGHT-1 && fifo_gen.in_val && fifo_gen.in_rdy |=> fifo_gen.wr_ptr_reg == 0);

// If read pointer wraps around, it should not increment but reset to zero.
as__read_pointer_wrap_around:
    assert property ($past(fifo_gen.rd_ptr_reg) == INFLIGHT-1 && fifo_gen.out_rdy && fifo_gen.out_val |=> fifo_gen.rd_ptr_reg == 0);

// If FIFO is empty, read pointer and write pointer should be equal.
as__pointers_equal_when_empty:
    assert property (fifo_gen.empty_reg |-> fifo_gen.rd_ptr_reg == fifo_gen.wr_ptr_reg);

// When FIFO becomes full, the write pointer should be just behind the read pointer or at the end if the read pointer is at zero.
as__fifo_full_condition:
    assert property (fifo_gen.full_reg |-> (fifo_gen.wr_ptr_reg == fifo_gen.rd_ptr_reg - 1) || (fifo_gen.wr_ptr_reg == INFLIGHT-1 && fifo_gen.rd_ptr_reg == 0));

// Data integrity: Data written to FIFO should be the same when read out.
genvar i;
for (i=0; i<INFLIGHT; i=i+1) begin : data_integrity
    as__data_integrity__offset:
        assert property (fifo_gen.in_val && fifo_gen.in_rdy && fifo_gen.wr_ptr_reg == i |=> fifo_gen.out_rdy && fifo_gen.out_val && $past(fifo_gen.in_data) == fifo_gen.fifo_storage_reg[i]);
end

// If FIFO is not empty and output is ready, the out_data should get the value at the current read pointer.
as__out_data_on_read:
    assert property (!fifo_gen.empty_reg && fifo_gen.out_rdy |-> fifo_gen.out_data == fifo_gen.fifo_storage_reg[fifo_gen.rd_ptr_reg]);

// When input is valid, data should be written to the FIFO at the current write pointer.
as__in_data_on_write:
    assert property (fifo_gen.in_val && fifo_gen.in_rdy |-> fifo_gen.fifo_storage_reg[fifo_gen.wr_ptr_reg] == fifo_gen.in_data);

```
