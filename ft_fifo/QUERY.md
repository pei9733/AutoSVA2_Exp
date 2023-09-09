```systemverilog
property_file.sv:

module fifo_properties (input clk, input rst_n, input in_val, output in_rdy, input [SIZE-1:0] in_data, output out_val, input out_rdy, output [SIZE-1:0] out_data);

  // Assertion 1: When input handshake occurs, the input data is loaded into the FIFO in the next cycle.
  as__input_handshake_data_load : assert property (
    in_val && in_rdy |=> fifo.buffer_data_r[fifo.buffer_head_r] == in_data
  );

  // Assertion 2: When output handshake occurs, the output data matches the FIFO tail data in the same cycle.
  as__output_handshake_data_match : assert property (
    out_val && out_rdy |-> out_data == fifo.buffer_data_r[fifo.buffer_tail_r]
  );

  // Assertion 3: If FIFO is full, input ready should be low.
  as__fifo_full_input_not_ready : assert property (
    (&fifo.buffer_val_r) |-> !in_rdy
  );

  // Assertion 4: If FIFO is empty, output valid should be low.
  as__fifo_empty_output_not_valid : assert property (
    (!|fifo.buffer_val_r) |-> !out_val
  );

  // Assertion 5: If there's an input handshake, buffer_head_r increments in the next cycle.
  as__input_handshake_head_increment : assert property (
    in_val && in_rdy |=> fifo.buffer_head_r == $past(fifo.buffer_head_r) + 1'b1
  );

  // Assertion 6: If there's an output handshake, buffer_tail_r increments in the next cycle.
  as__output_handshake_tail_increment : assert property (
    out_val && out_rdy |=> fifo.buffer_tail_r == $past(fifo.buffer_tail_r) + 1'b1
  );

  // Assertion 7: Check if the add_buffer and clr_buffer are behaving as expected.
  generate
    genvar k;
    for (k = 0; k < INFLIGHT; k = k + 1) begin: buffer_operations_gen
      
      // If input handshake occurs, the respective buffer slot should be flagged to be added in the next cycle.
      as__input_handshake_add_buffer_flagged : assert property (
        in_val && in_rdy && (fifo.buffer_head_r == k) |=> fifo.add_buffer[k]
      );

      // If output handshake occurs, the respective buffer slot should be flagged to be cleared in the next cycle.
      as__output_handshake_clear_buffer_flagged : assert property (
        out_val && out_rdy && (fifo.buffer_tail_r == k) |=> fifo.clr_buffer[k]
      );
      
    end
  endgenerate

endmodule
```

The above SystemVerilog Assertion (SVA) checks provide a comprehensive verification of the FIFO's functionality, excluding reset behavior as instructed. It covers the input and output handshakes, buffer read and write operations, and FIFO full and empty conditions.