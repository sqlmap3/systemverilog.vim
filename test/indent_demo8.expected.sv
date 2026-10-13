// indent regression demo 8: SVA assertions and bind mixed with macro calls -
// a macro that generates a labeled assertion, macro fail actions on the else
// arm (single-line, multi-line, and inside begin/end), a multi-line bind
// port list with a macro connection, and several `ifdef'd bind macros.
// Keep in sync with indent_demo8.expected.sv.

`ifndef INDENT_DEMO8_SV
`define INDENT_DEMO8_SV

`define CHK_ASSERT(lbl, prop) \
  lbl: assert property (prop) \
  else `uvm_error("SVA", "assert failed")

module demo_m;

a_macro: assert property (req |-> ack)
else `uvm_error("SVA", $sformatf("req/ack failed at %0t", $time))

a_blk: assert property (req |=> ack)
else begin
  `uvm_error("SVA",
  $sformatf("failed at %0t", $time))
  err_cnt++;
end

`CHK_ASSERT(a_gen, req |-> !ack)

bind demo_dut demo_checker chk_i (
  .clk(clk),
  .rst_n(rst_n),
  .evt(`EVT_SIG)
);

`ifndef SKIP_BIND
  `MY_BIND(demo_dut, demo_checker, chk_i)
  `MY_BIND(demo_dut2, demo_checker2, chk_j)
`endif

endmodule

`endif
