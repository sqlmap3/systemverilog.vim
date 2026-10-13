// indent regression demo 10: .sv top-level units - package, program, module
// with clocking blocks, generate and always_ff/always_latch, and a checker.
// module/program/package bodies are flat by design (upstream nachumk
// behavior); clocking/checker/generate/always bodies indent one level.
// Keep in sync with indent_demo10.expected.sv.

`ifndef INDENT_DEMO10_SV
`define INDENT_DEMO10_SV

package demo_pkg;
parameter int W = 4;
function automatic int add(int a, int b);
  return a + b;
endfunction
endpackage

program demo_prog (input logic clk);
logic rst_n;
initial begin
  #5ns;
  $display("prog");
end
endprogram

module demo_tb;
logic clk, req, ack, en, q, d;
logic [3:0] w, x;

clocking cb @(posedge clk);
  input req;
  output ack;
endclocking

default clocking cb_d @(posedge clk);
  input rst_n;
  output en;
endclocking

always_ff @(posedge clk) begin
  if (req)
    ack <= 1'b1;
end

always_latch begin
  if (en)
    q <= d;
end

genvar gi;
generate
  for (gi = 0; gi < W; gi = gi + 1) begin : g_loop
    assign w[gi] = 1'b0;
  end
  if (PARAM_A) begin : g_a
    assign x = 1'b0;
  end else begin : g_b
    assign x = 1'b1;
  end
endgenerate

endmodule

checker demo_chk (logic clk, logic rst_n);
  default clocking @(posedge clk);
  a_cov: cover property (req |=> ack);
endchecker

`endif
