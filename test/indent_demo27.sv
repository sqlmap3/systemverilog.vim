package demo27_pkg;
`ifdef HAS_TYPES
`include "demo27_types.svh"
typedef struct {
int a;
int b;
} my_t;
`define MY_MAX 32
`endif
function int get_val();
`ifdef HAS_TYPES
return MY_MAX;
`else
return 0;
`endif
endfunction
endpackage
