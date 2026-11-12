module m;
initial begin
  if (c) x = 1;
  else
  for (i = 0; i < n; i++)
    x = i;
  z = 2;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c) x = 1;
      else
      for (i = 0; i < n; i++)
        x = i;
  z = 2;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c)
        x = 1;
      else
      for (i = 0; i < n; i++)
        x = i;
  z = 2;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c) x = 1;
      else if (d) x = 2;
      else
      foreach (arr[i])
        x = i;
  z = 2;
end
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      if (c) x = 1;
      else begin
        for (i = 0; i < n; i++)
          x = i;
      end
  z = 2;
end
endmodule
