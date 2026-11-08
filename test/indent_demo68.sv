module demo68(input logic clk, input logic req, input logic ack, input logic rst_n);
event e_req;
event e_ack;
initial begin
-> e_req;
->> e_ack;
wait_order(e_req, e_ack)
$display("ordered");
else
$display("not ordered");
end
always @(posedge clk
`ifdef HAS_RST
or negedge rst_n
`endif
)
begin
if (req)
-> e_req;
end
final begin
$display("done");
end
endmodule
