class demo34;
function void run(int sel);
case (sel)
`ifdef HAS_CASE_A
0: do_a();
`endif
1: do_b();
`ifdef HAS_CASE_C
2: do_c();
`else
2: do_default();
`endif
default: do_default();
endcase
endfunction
endclass
