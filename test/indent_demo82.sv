package demo82_pkg;
`define DEMO82_WIDE \
logic [31:0] demo82_data;
`define DEMO82_SUM(a, b) \
((a) + (b))
`include "demo82_extra.svh"
`undef DEMO82_WIDE
function void log_msg(string s);
`uvm_info("DEMO82", s, UVM_LOW)
endfunction
`ifdef DEMO82_ON
`define DEMO82_FLAG 1
`else
`define DEMO82_FLAG 0
`endif
endpackage
