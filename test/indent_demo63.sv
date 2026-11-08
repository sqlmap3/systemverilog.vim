module demo63(input logic clk, input logic req, input logic ack);
sequence s_rep;
req ##[1:3] ack;
endsequence
sequence s_mult;
req [*3] ##1 ack;
endsequence
sequence s_goto;
req [=2] ##1 ack;
endsequence
sequence s_nonconsec;
req [->2] ##1 ack;
endsequence
property p_not;
@(posedge clk) not (req && ack);
endproperty
property p_and;
@(posedge clk) (req |-> ack) and (ack |-> req);
endproperty
property p_or;
@(posedge clk) (req |-> ack) or (ack |-> req);
endproperty
assert property (p_not);
assert property (p_and);
assert property (p_or);
endmodule
