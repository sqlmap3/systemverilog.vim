package demo81_pkg;
parameter int WIDTH = 32;
localparam int DEPTH = 16;
function int add(int a, int b);
return a + b;
endfunction
task automatic do_work();
$display("work");
endtask
class demo81_item;
int id;
function new(int i);
id = i;
endfunction
virtual function void print();
$display("id=%0d", id);
endfunction
endclass
int id_val;
covergroup demo81_cg;
option.per_instance = 1;
cp_id: coverpoint id_val;
endgroup
let max2(a, b) = (a > b) ? a : b;
endpackage
