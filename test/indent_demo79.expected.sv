module demo79;
clocking cb @(posedge clk);
  input req;
  output ack;
endclocking
default clocking cb;
checker c1;
  default clocking @(posedge clk);
    input req;
    output ack;
  endclocking
  assert property (p1);
endchecker
checker c2;
  default clocking @(posedge clk); endclocking
  assert property (p2);
endchecker
endmodule
