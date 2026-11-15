module m;
initial begin
  cover /* c */ sequence (@(posedge clk) a ##1 b);
  x = 1;
  assume /* c */ sequence (@(posedge clk) a ##1 b);
  x = 2;
  assert /* c */ sequence (@(posedge clk) a ##1 b);
  x = 3;
  restrict /* c */ property (@(posedge clk) a |-> b);
  x = 4;
  cover /* c */ property (@(posedge clk) a |-> b);
  x = 5;
  assert /* c */ [#0] property (@(posedge clk) a |-> b);
  x = 6;
  assert [#0] /* c */ property (@(posedge clk) a |-> b);
  x = 7;
  cover /* a */ /* b */ sequence (@(posedge clk) a ##1 b);
  x = 8;
  cover/* c */sequence (@(posedge clk) a ##1 b);
  x = 9;
  cover sequence (@(posedge clk) a ##1 b);
  x = 10;
  assert property (@(posedge clk) a |-> b);
  x = 11;
  assume (a);
  x = 12;
  cover (a);
  x = 13;
end
sequence s;
  a ##1 b;
endsequence
endmodule
