module m;
typedef /* c */ class foo;
x = 1;
typedef class foo;
y = 2;
default /* c */ clocking cb;
z = 3;
default clocking cb;
w = 4;
default /* c */ clocking @(posedge clk);
v = 5;
default clocking @(posedge clk);
u = 6;
default /* c */ clocking cb; endclocking
t = 7;
default clocking cb; endclocking
s = 8;
initial begin
  r = 9;
end
endmodule
