module demo86;
initial begin
if (
`ifdef COND_A
a == 1
`else
b == 2
`endif
c == 3)
`MACRO1(x);
y = 2;
end
initial begin
if (a &&
`ifdef COND_A
(b == 1))
`else
(b == 2))
`endif
`MACRO1(x);
y = 2;
end
endmodule
