module demo60(input logic clk);
initial begin : main
fork
begin : t1
$display("t1");
end : t1
begin : t2
$display("t2");
end : t2
join_any
disable fork;
end : main
endmodule
