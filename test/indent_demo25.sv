class demo25;
`ifdef HAS_FEATURE
`include "feature_members.svh"
int feature_count;
`define FEATURE_MAX 16
`ifdef HAS_DEBUG
`include "debug_members.svh"
int debug_level;
`endif
`else
int dummy;
`endif
function void run();
`ifdef HAS_FEATURE
feature_init();
`endif
endfunction
endclass
