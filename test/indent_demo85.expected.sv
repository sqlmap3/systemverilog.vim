module demo85;
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      begin
        x = 1;
        y = 2;
      end
  z = 3;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c == 3)
        y = 1;
  z = 3;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c == 3)
      begin
        y = 1;
      end
  z = 3;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c) y = 1;
  z = 3;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      `MACRO2(y);
  z = 3;
end
endmodule
