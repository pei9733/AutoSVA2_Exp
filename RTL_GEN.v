/*
This is the Specification of <MODULE_NAME>.

# REQUIREMENTS
- The iface_* interface ...
- The module MUST ...

<ADD SVA ASSERTIONS HERE>


Implement the following module only using synthesizable Verilog.
DO NOT write the module interface, only the implementation.
DO NOT answer anything except for the Verilog implementation, ONLY write comments within the Verilog code.
Append "_reg" to the name of ALL registers.
*/


module <MODULE_NAME>
  #(
    parameter PARAM = 1 // <Parameter description>
  )
(
    // Clock + Reset
    input  wire                          clk,
    input  wire                          rst_n,
    input  wire                          iface_val
);