interface demo28_if(input logic clk);
logic data;
`ifdef HAS_VALID
  logic valid;
  `include "valid_signals.svh"
`endif
`ifdef HAS_READY
  logic ready;
  modport master(output data, input ready);
`else
  modport master(output data);
`endif
endinterface
