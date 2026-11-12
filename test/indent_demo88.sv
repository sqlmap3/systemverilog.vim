module demo88;
initial begin
`ifdef COND_A
if (a == 1)
`else
if (b == 1 &&
b2 == 2)
`endif
`MACRO1(x);
z = 3;
end
initial begin
`ifdef COND_A
if (a == 1 &&
a2 == 2)
`else
if (b == 2)
`endif
`MACRO1(x);
z = 3;
end
initial begin
`ifdef COND_A
if (a == 1)
`else
if (b == 2)
`endif
if (c)
for (i = 0; i < 3; i++)
y = 1;
z = 3;
end
initial begin
`ifdef COND_A
if (a == 1)
`else
if (b == 2)
`endif
if (c) y = 1;
else y = 2;
z = 3;
end
initial begin
`ifdef COND_A
if (a == 1)
`else
if (b == 2)
`endif
if (c) y = 1;
else if (d) y = 2;
else y = 3;
z = 3;
end
endmodule
