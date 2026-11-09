module demo74;
checker demo_chk(input logic clk, input logic req, input logic ack);
  let max_wait = 10;
  sequence s_req;
    req ##[1:max_wait] ack;
  endsequence
  property p_req;
    @(posedge clk) req |-> s_req;
  endproperty
  assert property (p_req) else $error("req timeout");
  cover property (@(posedge clk) req ##1 ack);
endchecker
module demo74_top;
logic clk, req, ack;
demo_chk u_chk(.clk(clk), .req(req), .ack(ack));
initial begin
  req = 0;
  ack = 0;
  #5 req = 1;
  #5 ack = 1;
end
endmodule
