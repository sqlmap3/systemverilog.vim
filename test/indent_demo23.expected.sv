class demo23;
  function void run();
    `ifdef LEVEL1
    `define MSG1 "hello"
      `ifdef LEVEL2
        `include "level2.svh"
      `define MSG2 "world"
        `ifdef LEVEL3
          `include "level3.svh"
          $display(MSG1, MSG2);
        `else
          `include "level3_alt.svh"
        `endif
      `else
        `include "level2_alt.svh"
      `endif
    `elsif LEVEL1_ALT
      `include "level1_alt.svh"
    `else
      `include "level1_default.svh"
    `endif
    $display("done");
  endfunction
endclass
