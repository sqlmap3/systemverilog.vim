module demo50 (
  input logic clk,
  input logic rst_n,
  input logic [7:0] a,
  input logic [7:0] b,
  output logic [7:0] sum,
  output logic [7:0] diff
);
always_comb begin
  `ifdef USE_FAST
    sum = a + b;
  `else
    sum = a;
    sum = sum + b;
  `endif
end
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    diff <= '0;
  end else begin
    diff <= a - b;
  end
end
always_latch begin
  if (a > b)
    diff = a;
end
assign sum = {
  `ifdef HAS_HIGH
    a[7:4],
  `else
    4'b0,
  `endif
  a[3:0]
};
endmodule
