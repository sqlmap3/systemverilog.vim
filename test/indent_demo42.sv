interface demo42_if(input logic clk);
logic req;
logic ack;
clocking cb @(posedge clk);
default input #1 output #1;
input req;
output ack;
endclocking
modport master(clocking cb);
endinterface
program demo42_prog(demo42_if.master mp);
initial begin
mp.cb.req <= 1'b1;
@(mp.cb);
mp.cb.req <= 1'b0;
end
endprogram
