module demo83;
initial begin
if (
`ifdef COND_A
a == 1
`else
b == 2
`endif
)
`MACRO1(x);
if (a == 1 &&
b == 2)
begin
x = 1;
end
end
endmodule
