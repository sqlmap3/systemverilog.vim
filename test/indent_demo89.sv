module demo89;
initial begin
if (a &&
`ifdef COND_A
(b == 1))
`else
(b == 2))
`endif
if (c) x = 1;
y = 2;
end
initial begin
if (a &&
`ifdef COND_A
(b == 1))
`else
(b == 2))
`endif
begin
x = 1;
end
y = 2;
end
endmodule
