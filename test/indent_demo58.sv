module demo58(input logic clk, input logic req, input logic ack);
sequence s_a;
req ##1 ack;
endsequence
sequence s_b;
req intersect (ack ##1 req);
endsequence
property p_a;
@(posedge clk) req |-> s_eventually ack;
endproperty
property p_b;
@(posedge clk) s_always (req throughout ack);
endproperty
property p_c;
@(posedge clk) req within ack;
endproperty
clocking cb @(posedge clk);
default input #1step output #2;
input req;
output ack;
endclocking
assert property (p_a);
cover property (p_b);
endmodule
