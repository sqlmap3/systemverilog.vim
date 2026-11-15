module m;
initial begin
  c1: cover sequence (@(posedge clk) req ##1 ack);
  x = 1;
  assert [#0] sequence (@(posedge clk) a ##1 b);
  x = 2;
  assert [#0] property (@(posedge clk) a |-> b);
  x = 3;
  restrict property (@(posedge clk) a |-> b);
  x = 4;
  cover sequence
  (@(posedge clk) a ##1 b);
  x = 5;
  assert sequence
  (@(posedge clk) a ##1 b);
  x = 6;
end
endmodule
