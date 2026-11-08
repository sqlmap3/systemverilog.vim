class demo32;
  function void run();
    `ifdef MODE_A
      `include "mode_a.svh"
    `define MODE_VAL 1
    do_a();
    `elsif MODE_B
      `include "mode_b.svh"
    `define MODE_VAL 2
    do_b();
    `elsif MODE_C
      `include "mode_c.svh"
      do_c();
    `else
      `include "mode_default.svh"
      do_default();
    `endif
    $display("done");
  endfunction
endclass
