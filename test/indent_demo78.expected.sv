module demo78(input logic clk, input logic rst_n, input logic req);
always @(posedge clk
  `ifdef HAS_RST
    or negedge rst_n
  `endif
) begin
  if (req) begin
    $display("hi");
  end
end
always @(posedge clk) begin
  if (req) begin
    $display("ok");
  end
end
final begin
  $display("done");
end
endmodule
