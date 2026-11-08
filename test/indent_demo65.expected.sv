module demo65 #(
  parameter int WIDTH = 8,
  `ifdef HAS_PARITY
    parameter bit PARITY = 1,
  `endif
  parameter type T = logic [WIDTH-1:0]
)(
  input logic clk,
  input T data_in,
  output T data_out
);
T r_data;
always_ff @(posedge clk) begin
  r_data <= data_in;
end
assign data_out = r_data;
endmodule
module demo65_top;
logic clk;
logic [7:0] din, dout;
demo65 #(
  .WIDTH(8),
  `ifdef HAS_PARITY
    .PARITY(1),
  `endif
  .T(logic [7:0])
) u_dut (
  .clk(clk),
  .data_in(din),
  .data_out(dout)
);
endmodule
