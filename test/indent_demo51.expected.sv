class demo51;
  rand int val;
  rand int mode;
  covergroup cg;
    cp_val: coverpoint val {
      bins low = {[0:10]};
      bins high = {[11:100]};
    }
    cp_mode: coverpoint mode;
    `ifdef HAS_CROSS
      cross_val_mode: cross cp_val, cp_mode;
    `endif
  endgroup
  constraint c_mode {
    if (mode == 0) val inside {[0:10]};
    else val inside {[11:100]};
  }
  function void run();
    randcase
      val < 10: $display("low");
      val < 50: $display("mid");
      default: $display("high");
    endcase
  endfunction
endclass
