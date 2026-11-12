module demo87;
initial begin
  `ifdef OUTER
    x = 1;
    `ifdef INNER
      if (a)
    `endif
  `endif
  z = 2;
end
initial begin
  if (a == 1 &&
    `ifdef COND_A
      b == 2 /* ) */
    `else
      c == 3
    `endif
  )
    `MACRO1(x);
  y = 2;
end
initial begin
  if (s == "a\")x" &&
    `ifdef COND_A
      b == 2
    `else
      c == 3
    `endif
  )
    `MACRO1(x);
  y = 2;
end
endmodule
