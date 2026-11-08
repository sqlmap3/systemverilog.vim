module demo47 (
  input logic clk,
  input logic rst_n,
  input logic req,
  input logic ack
);
let req_ack(r, a) = r |-> ##1 a;
checker c_req_ack(clk, rst_n, req, ack);
  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n);
  assert property (req_ack(req, ack));
  cover property (req_ack(req, ack));
endchecker
c_req_ack u_check(.clk(clk), .rst_n(rst_n), .req(req), .ack(ack));
endmodule
