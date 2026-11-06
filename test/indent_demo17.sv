// indent regression demo 17: wait as a control statement, and code under
// a preprocessor `else inside an if (not at function level). wait (cond)
// indents its following statement like if/for; wait (cond); and wait fork;
// are complete statements; chained controls stay at one level (as in
// if-if). Code under `else sits one deeper than the `else, even when the
// `ifdef is inside an if.
// Keep in sync with indent_demo17.expected.sv.

class demo_wait_else;

function void run();
wait (ready)
do_something();
wait (done);
x = 1;
wait (ready) begin
do_other();
end
wait fork;
y = 2;
if (a)
wait (ready)
do_third();
z = 3;
if (a)
`ifdef A
w = 1;
`else
w = 2;
`endif
endfunction

endclass
