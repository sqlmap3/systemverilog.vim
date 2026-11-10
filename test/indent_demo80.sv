module demo80;
timeunit 1ns;
timeprecision 1ps;
wire [7:0] a;
wire [7:0] b;
alias a = b;
chandle h;
defparam u_sub.WIDTH = 16;
initial begin
int i;
i = 0;
do begin
i++;
end while (i < 4);
repeat (3) begin
$display("r");
end
forever begin
if (i >= 10) break;
i++;
end
while (i < 20) begin
if (i == 15) continue;
i++;
end
end
sub u_sub();
endmodule
