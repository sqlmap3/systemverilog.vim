package demo70_pkg;
typedef enum logic {A, B} mode_t;
parameter int MAX = 100;
endpackage
class demo70_cg;
  rand int val;
  rand int mode;
  covergroup cg;
    cp_val: coverpoint val {
      bins low = {[0:10]};
      bins high = {[11:100]};
    }
    cp_mode: coverpoint mode {
      bins m0 = {0};
      bins m1 = {1};
    }
    cross_val_mode: cross cp_val, cp_mode {
      bins b0 = binsof(cp_val.low) intersect {[0:5]};
    }
  endgroup
  constraint c_uniq {
    unique {val, mode};
    solve mode before val;
  }
  function new();
    cg = new();
  endfunction
endclass
module demo70_top;
import demo70_pkg::*;
mode_t cur;
demo70_dut u_dut(.mode(cur));
initial begin
  $display("%0d", u_dut.count);
  $display("%0d", MAX);
end
endmodule
module demo70_dut(input demo70_pkg::mode_t mode);
int count;
endmodule
