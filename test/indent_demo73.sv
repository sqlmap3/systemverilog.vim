interface demo72_if(input logic clk);
logic [7:0] data;
logic valid;
logic ready;
clocking cb @(posedge clk);
default input #1step output #2;
input data;
input valid;
output ready;
endclocking
modport master(clocking cb, output data, output valid, input ready);
modport slave(clocking cb, input data, input valid, output ready);
endinterface
program demo72_prog(demo72_if.master mp);
initial begin
mp.cb.data <= 8'hA5;
mp.cb.valid <= 1'b1;
@(mp.cb);
mp.cb.valid <= 1'b0;
end
endprogram
