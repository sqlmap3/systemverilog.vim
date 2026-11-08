class demo31;
function void gen_req(
int addr,
`ifdef HAS_DATA
int data,
`else
int dummy,
`endif
int len
);
$display(addr, len);
endfunction
endclass
