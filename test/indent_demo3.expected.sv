// indent regression demo 3: SVA, constraints, covergroups, checkers, DPI
// imports and randcase. Keep in sync with indent_demo3.expected.sv.

`ifndef INDENT_DEMO3_SV
`define INDENT_DEMO3_SV

property demo_prop;
  @(posedge clk) disable iff (rst_n)
  req |-> ##[1:3] ack;
endproperty

a_prop: assert property (demo_prop)
else $error("demo_prop failed");

sequence demo_sva_seq;
  req ##1 ack;
endsequence

constraint demo_c {
  a inside {[0:15]};
  soft b == 1;
  if (mode) {
    c dist {0 := 1, 1 := 2};
  } else {
    c == 0;
  }
}

covergroup demo_cg @(posedge clk);
  cp_a: coverpoint a {
    bins zero = {0};
    bins lo[] = {[1:3]};
    ignore_bins hi = {8'hF0};
  }
  cx: cross cp_a, cp_b;
endgroup

checker demo_checker (logic clk);
  default clocking @(posedge clk);
  a_lbl: assert property (req |-> ack);
endchecker : demo_checker

import "DPI-C" function int add_one(input int i);
import "DPI-C" context task dpi_task(input int i);

function int demo_str_kw();
  $display("this string contains class foo end begin if");
  return "also } { /* and // here";
endfunction

randcase
  3: x = 1;
  1: x = 2;
endcase

`endif
