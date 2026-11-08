class demo30;
  covergroup cg @(posedge clk);
    `ifdef HAS_CP_A
      cp_a : coverpoint a {
        bins low = {0, 1};
        `include "cp_a_bins.svh"
      }
    `endif
    `ifdef HAS_CP_B
      cp_b : coverpoint b {
        bins high = {2, 3};
      }
    `endif
    cross_a_b : cross cp_a, cp_b;
  endgroup
  function void sample();
    cg.sample();
  endfunction
endclass
