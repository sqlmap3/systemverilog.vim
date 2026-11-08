module demo41 (
input logic clk,
input logic rst_n,
input logic req,
input logic ack
);
sequence s_req;
req ##1 ack;
endsequence
property p_req_ack;
@(posedge clk) disable iff (!rst_n)
req |-> ##[1:3] ack;
endproperty
assert property (p_req_ack)
else $error("req not acked");
cover property (p_req_ack);
assume property (@(posedge clk) req |=> ack);
endmodule
