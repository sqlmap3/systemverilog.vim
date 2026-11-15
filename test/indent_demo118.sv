module m;
initial begin
cover sequence (@(posedge clk) a ##1 b);
x = 1;
assume sequence (@(posedge clk) a ##1 b);
x = 2;
assert sequence (@(posedge clk) a ##1 b);
x = 3;
restrict sequence (@(posedge clk) a ##1 b);
x = 4;
cover property (@(posedge clk) a |-> b);
x = 5;
end
sequence s;
a ##1 b;
endsequence
endmodule
