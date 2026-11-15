import uvm_pkg::*; function void foo();
  x = 1;
  y = 2;
endfunction
z = 3;
import uvm_pkg::*; task run();
  x = 1;
endtask
y = 2;
export uvm_pkg::*; function void foo2();
  x = 1;
endfunction
y = 2;
import "DPI-C" function void dpi_foo(); function void real_foo();
  x = 1;
endfunction
y = 2;
export "DPI-C" function foo; function void bar();
  x = 1;
endfunction
y = 2;
function void foo3(); import uvm_pkg::*;
  x = 1;
endfunction
y = 2;
