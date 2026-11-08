module demo29;
generate
  `ifdef GEN_A
    `include "gen_a.svh"
    for (genvar i = 0; i < 4; i++) begin : g_a
      submod u_sub (.clk(clk));
    end
  `else
    `include "gen_b.svh"
    for (genvar j = 0; j < 2; j++) begin : g_b
      submod u_sub (.clk(clk));
    end
  `endif
endgenerate
`ifdef HAS_TOP
  submod u_top (.clk(clk));
`endif
endmodule
