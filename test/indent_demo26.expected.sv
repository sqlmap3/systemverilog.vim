module demo26 (
  input logic clk,
  `ifdef HAS_RESET
    input logic rst_n,
  `endif
  output logic out
);
`include "demo26_params.svh"
`ifdef HAS_DEBUG
  `include "debug_logic.svh"
  always_ff @(posedge clk) begin
    out <= 1'b1;
  end
`else
  assign out = 1'b0;
`endif
endmodule
