module demo72;
task run_fork();
fork
begin
a = 1;
#10 b = 2;
end
begin
c = 3;
wait (d == 1);
end
join_any
disable fork;
wait fork;
fork
begin
e = 4;
end
join_none
process p;
p = process::self();
p.kill();
endtask
initial begin
fork
f = 5;
join
end
endmodule
