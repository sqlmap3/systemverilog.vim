// indent regression demo 11: complex covergroups (option/type_option/iff/
// cross with binsof/with), config blocks, specify blocks and UDP
// primitive/table. Keep in sync with indent_demo11.expected.sv.

`ifndef INDENT_DEMO11_SV
`define INDENT_DEMO11_SV

class demo_cg;

  covergroup cg @(posedge clk);
    option.per_instance = 1;
    option.comment = "cg options";
    type_option.weight = 2;

    cp_a: coverpoint a iff (en) {
      bins zero = {0};
      bins lo[] = {[1:3]};
      bins trans = (1 => 2 => 3);
      wildcard bins wc = {4'b1??0};
      illegal_bins bad = {8'hFF};
    }

    cp_b: coverpoint b {
      bins one = {1};
    }

    cr_ab: cross cp_a, cp_b {
      bins both = binsof(cp_a) intersect {1} && binsof(cp_b) intersect {2};
      ignore_bins ign = binsof(cp_a.lo) with (cp_a.lo > 5);
    }
  endgroup

  function void run_cg();
    cg.sample();
  endfunction

endclass

config cfg_demo;
  design work.demo_top;
  instance demo_top.u_if use work.demo_if;
  cell clk use lib.clk;
endconfig

module with_specify (input a, output b);
specify
  specparam t_rise = 1, t_fall = 2;
  (a => b) = (t_rise, t_fall);
  $setup(a, posedge clk, t_rise);
endspecify
endmodule

primitive udp_and (out, a, b);
  output out;
  input a, b;
  table
    0 0 : 0;
    0 1 : 0;
    1 0 : 0;
    1 1 : 1;
  endtable
endprimitive

`endif
