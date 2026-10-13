// indent regression demo 12: randsequence, deferred/immediate assertions
// (assert #0 / assert final), casting and streaming operators, and a full
// parameterized interface with nested clocking/modport/function.
// Keep in sync with indent_demo12.expected.sv.

`ifndef INDENT_DEMO12_SV
`define INDENT_DEMO12_SV

class demo_cast;

  function void do_cast(uvm_object obj, int rhs);
    uvm_sequence_item it;
    int lhs;
    bit [31:0] packed_bits;
    logic [7:0] byteq[$];

    assert #0 (rhs == 0);
    assert final (rhs > 0) else $error("final failed");
    assert #1 (lhs === rhs);

    if (!$cast(it, obj))
      return;
    lhs = int'(rhs);
    packed_bits = {<<32{byteq}};
    byteq = {>>8{packed_bits}};
  endfunction

  task automatic do_randseq();
    randsequence (main)
      main : first second;
      first : { $display("first"); };
      second : { $display("second"); };
    endsequence
  endtask

endclass

interface demo_bus #(parameter int WIDTH = 8) (input logic clk);
logic [WIDTH-1:0] data;
logic valid;

clocking cb @(posedge clk);
  input data;
  output valid;
endclocking

modport master (clocking cb, output data, valid);
modport slave (clocking cb, input data, valid);

function automatic void drive(input logic [WIDTH-1:0] d);
  data = d;
  valid = 1'b1;
endfunction
endinterface

`endif
