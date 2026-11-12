module demo84;
initial begin
  `ifdef COND_A
    if (a == 1)
  `else
    if (b == 2)
  `endif
      `MACRO2(y);
end
endmodule
