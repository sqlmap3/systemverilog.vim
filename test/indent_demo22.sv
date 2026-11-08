`ifdef HAS_FEATURE
`define FEATURE_ON 1
`include "feature_defs.svh"
`define FEATURE_MSG(a) \
$display(a); \
$display("done");
`ifdef FEATURE_DEBUG
`define DBG(x) $display(x);
`endif
`endif
class my_block;
function void setup();
`ifdef HAS_FEATURE
feature_init();
`endif
endfunction
endclass
