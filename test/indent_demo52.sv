class demo52_inner;
int data;
function demo52_inner set(int v);
data = v;
return this;
endfunction
endclass
class demo52 #(parameter int WIDTH = 8);
`ifdef HAS_INNER
demo52_inner inner;
`endif
logic [WIDTH-1:0] val;
function void run();
demo52_inner obj = new();
obj.set(1).set(2);
val = {>>{8'hAA, 8'hBB}};
val = {<<{val}};
endfunction
endclass
