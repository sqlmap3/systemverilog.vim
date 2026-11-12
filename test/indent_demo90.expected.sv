module demo90;
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c) begin
        x = 1;
      end
      else
        x = 2;
  z = 3;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c) begin
        x = 1;
      end else begin
        x = 2;
      end
  z = 3;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c)
      begin
        x = 1;
      end
      else
      begin
        x = 2;
      end
  z = 3;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c)
        y = 1;
      else if (d)
        y = 2;
      else
        y = 3;
  z = 3;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c) begin
        x = 1;
      end else if (d) begin
        x = 2;
      end else begin
        x = 3;
      end
  z = 3;
end
endmodule
