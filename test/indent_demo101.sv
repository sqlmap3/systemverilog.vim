class c;
task t();
`ifdef X
if (a) begin
`endif
x = 1;
end
m1 = 1;
`ifdef Y
case (sel)
`endif
1'b0: y = 1;
endcase
m2 = 2;
`ifdef Z
for (i = 0; i < 4; i++) begin
`endif
end
m3 = 3;
endtask
endclass
