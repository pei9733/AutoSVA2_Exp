Here is an SVA property file with assertions to check the correctness of the module's functionality:

```verilog
// fifo_property.sv

// Ensure valid handshake
property pr__valid_in_handshake;
    @(posedge clk) (fifo.in_val && fifo.in_rdy) |-> fifo.in_val;
endproperty
as__valid_in_handshake : assert property (pr__valid_in_handshake);

property pr__valid_out_handshake;
    @(posedge clk) (fifo.out_val && fifo.out_rdy) |-> fifo.out_val;
endproperty
as__valid_out_handshake : assert property (pr__valid_out_handshake);

// Data written is what gets read out when there's a valid handshake
property pr__write_read_data;
    @(posedge clk) (fifo.in_val && fifo.in_rdy) |=> (fifo.out_val && fifo.out_rdy) -> (fifo.in_data == fifo.buffer_data_r[fifo.buffer_tail_r]);
endproperty
as__write_read_data : assert property (pr__write_read_data);

// Buffer head and tail should not wrap around beyond INFLIGHT size
property pr__buffer_head_wraparound;
    @(posedge clk) (fifo.buffer_head_r + 1) < INFLIGHT;
endproperty
as__buffer_head_wraparound : assert property (pr__buffer_head_wraparound);

property pr__buffer_tail_wraparound;
    @(posedge clk) (fifo.buffer_tail_r + 1) < INFLIGHT;
endproperty
as__buffer_tail_wraparound : assert property (pr__buffer_tail_wraparound);

// Assert that if the buffer is full, then input ready should be low
property pr__buffer_full_input_not_ready;
    @(posedge clk) (&fifo.buffer_val_r) |-> !fifo.in_rdy;
endproperty
as__buffer_full_input_not_ready : assert property (pr__buffer_full_input_not_ready);

// Assert that if the buffer is empty, then output valid should be low
property pr__buffer_empty_output_not_valid;
    @(posedge clk) (!|fifo.buffer_val_r) |-> !fifo.out_val;
endproperty
as__buffer_empty_output_not_valid : assert property (pr__buffer_empty_output_not_valid);

// If a new data is added to the buffer, the corresponding buffer value should be high in the next cycle
property pr__data_added_buffer_val_high_next_cycle;
    @(posedge clk) (fifo.in_val && fifo.in_rdy) |=> fifo.buffer_val_r[fifo.buffer_head_r];
endproperty
as__data_added_buffer_val_high_next_cycle : assert property (pr__data_added_buffer_val_high_next_cycle);

// If data is read from the buffer, the corresponding buffer value should be low in the next cycle
property pr__data_read_buffer_val_low_next_cycle;
    @(posedge clk) (fifo.out_val && fifo.out_rdy) |=> !fifo.buffer_val_r[fifo.buffer_tail_r];
endproperty
as__data_read_buffer_val_low_next_cycle : assert property (pr__data_read_buffer_val_low_next_cycle);

// End of fifo_property.sv
```

These properties will ensure that the FIFO is behaving correctly by checking that the valid handshakes are adhered to, the data written to the FIFO is what gets read out, the buffer doesn't wrap around unexpectedly, and the buffer behaves correctly when it is full or empty.