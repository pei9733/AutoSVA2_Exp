Here are some SystemVerilog Assertion (SVA) properties to verify the behavior of the provided `fifo` module. These properties check the correctness of most of the behavior, excluding reset behavior as requested.

```systemverilog
module fifo_assertions
  #(
    parameter INFLIGHT_IDX = 2,
    parameter SIZE = 4
  )
(
    input  wire                          clk,
    input  wire                          rst_n,
    input  wire                          in_val,
    output wire                          in_rdy,
    input  wire [SIZE-1:0]               in_data,

    output wire                          out_val,
    input  wire                          out_rdy,
    output wire [SIZE-1:0]               out_data
);

//==============================================================================
// SVA Properties
//==============================================================================

// Check that if `in_hsk` is true, buffer head index will be incremented in the next cycle
property pr__in_hsk_behavior;
  @(posedge clk)
  (fifo.in_hsk && !rst_n) |-> (fifo.buffer_head_r == $past(fifo.buffer_head_r) + 1);
endproperty
as__in_hsk_behavior : assert property (pr__in_hsk_behavior);

// Check that if `out_hsk` is true, buffer tail index will be incremented in the next cycle
property pr__out_hsk_behavior;
  @(posedge clk)
  (fifo.out_hsk && !rst_n) |-> (fifo.buffer_tail_r == $past(fifo.buffer_tail_r) + 1);
endproperty
as__out_hsk_behavior : assert property (pr__out_hsk_behavior);

// Check that data will be stored into buffer_data_r when `in_hsk` is true
property pr__data_store_behavior;
  @(posedge clk)
  (fifo.in_hsk && !rst_n) |-> $rose(add_buffer[fifo.buffer_head_r]) && (fifo.buffer_data_r[fifo.buffer_head_r] == in_data);
endproperty
as__data_store_behavior : assert property (pr__data_store_behavior);

// Check that if buffer is full, in_rdy will be deasserted (not ready to accept data)
property pr__buffer_full_behavior;
  @(posedge clk)
  (&buffer_val_r && !rst_n) |-> (!in_rdy);
endproperty
as__buffer_full_behavior : assert property (pr__buffer_full_behavior);

// Check that if buffer is empty, out_val will be deasserted (no data available)
property pr__buffer_empty_behavior;
  @(posedge clk)
  (!|buffer_val_r && !rst_n) |-> (!out_val);
endproperty
as__buffer_empty_behavior : assert property (pr__buffer_empty_behavior);

// Check that the output data is equal to the data at the buffer_tail_r index
property pr__out_data_behavior;
  @(posedge clk)
  (fifo.out_val && !rst_n) |-> (out_data == fifo.buffer_data_r[fifo.buffer_tail_r]);
endproperty
as__out_data_behavior : assert property (pr__out_data_behavior);

endmodule
```

The above SVA properties check the key behaviors of the `fifo` module, such as handling of buffer indices (`buffer_head_r` and `buffer_tail_r`), storage of data into the `buffer_data_r` array, and behavior of the `in_rdy` and `out_val` signals when the buffer is full or empty respectively.