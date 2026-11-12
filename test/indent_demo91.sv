module demo91;
initial begin
if (a &&
`ifdef COND_A
(b == 1))
`else
(b == 2 &&
c == 3))
`endif
x = 1;
y = 2;
end
initial begin
`ifdef COND_A
x = 1;
`else
y = 2;
`endif
z = 3;
end
initial begin
if (c) begin
`ifdef COND_A
x = 1;
`else
y = 2;
`endif
z = 3;
end
end
endmodule
