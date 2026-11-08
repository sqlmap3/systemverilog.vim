class my_comp;
  function void run();
    `ifdef MODE_A
      x = 1;
    `elsif MODE_B
      x = 2;
    `else
      x = 3;
    `endif
    `ifdef DEBUG
      `ifdef VERBOSE
        $display("verbose");
      `else
        $display("debug");
      `endif
    `endif
    y = 4;
  endfunction
  task do_work();
    `ifdef FAST
      fast_run();
    `else
      slow_run();
    `endif
  endtask
endclass
