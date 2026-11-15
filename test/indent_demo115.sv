function void f();
if (c) begin
y = {a,
`ifdef X
b,
`else
c,
`endif
d
};
m = 1;
end
endfunction
