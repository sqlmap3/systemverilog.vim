interface demo45_if(input logic clk);
logic data;
endinterface
class demo45_base;
  pure virtual function void do_work();
  virtual demo45_if vif;
  extern function void helper();
endclass
function void demo45_base::helper();
  do_work();
endfunction
class demo45_child extends demo45_base;
  function void do_work();
    vif.data = 1'b1;
  endfunction
endclass
