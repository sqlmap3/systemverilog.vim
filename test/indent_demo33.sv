class demo33;
rand int val;
`ifdef HAS_CONSTRAINT
constraint c_val {
`ifdef HAS_RANGE
val inside {[0:100]};
`else
val inside {[0:10]};
`endif
}
`endif
`define TEMP_MACRO 1
`undef TEMP_MACRO
function void run();
`ifdef HAS_CONSTRAINT
$display(val);
`endif
endfunction
endclass
