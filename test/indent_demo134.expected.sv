import "DPI-C"
function void foo();
y = 2;
z = 3;
export "DPI-C"
function foo;
y = 2;
z = 3;
import "DPI-C" context
function void foo2();
y = 2;
z = 3;
import "DPI-C"
task bar();
y = 2;
z = 3;
import "DPI-C" c_foo =
function void foo3();
y = 2;
z = 3;
import
"DPI-C" function void foo4();
y = 2;
z = 3;
import "DPI-C" // dpi import
function void foo5();
y = 2;
z = 3;
import "DPI-C"
function void foo6();
y = 2;
function void real();
  x = 1;
endfunction
z = 3;
import "DPI-C" \
  function void foo7();
y = 2;
z = 3;
import "DPI-C"
pure function int bar2();
y = 2;
z = 3;
import "DPI-C"
extern function void foo8();
y = 2;
z = 3;
