class demo62;
  rand int val;
  rand int mode;
  covergroup cg;
    option.per_instance = 1;
    type_option.weight = 0;
    cp_val: coverpoint val {
      option.weight = 2;
      bins low = {[0:10]};
      bins high = {[11:100]};
      ignore_bins ign = {[5:6]};
      illegal_bins ill = {0};
    }
    cp_mode: coverpoint mode {
      bins m0 = {0};
      bins m1 = {1};
    }
    `ifdef HAS_CROSS
      cross_val_mode: cross cp_val, cp_mode {
        ignore_bins ign_cross = binsof(cp_val.low) && binsof(cp_mode.m1);
      }
    `endif
  endgroup
  function new();
    cg = new();
  endfunction
endclass
