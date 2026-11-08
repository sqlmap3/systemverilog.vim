class demo43;
task run();
fork
begin
do_a();
end
begin
do_b();
end
join
fork
wait_a();
wait_b();
join_any
fork
wait_c();
join_none
wait fork;
disable fork;
endtask
endclass
