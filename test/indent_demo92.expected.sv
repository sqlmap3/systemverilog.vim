module m;
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c) y = 1;
      else if (d == 1 &&
      d2 == 2)
      y = 2;
  z = 3;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c == 1 &&
      c2 == 2)
      y = 1;
  z = 2;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c) y = 1;
      else if (d) y = 2;
      else if (e == 1 &&
      e2 == 2)
      y = 3;
  z = 4;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c == 1 &&
      c2 == 2) begin
        y = 1;
      end
  z = 2;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c) y = 1;
      else if (d == 1 &&
      d2 == 2) begin
        y = 2;
      end
  z = 3;
end
endmodule
