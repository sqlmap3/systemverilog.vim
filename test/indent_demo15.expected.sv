// indent regression demo 15: preprocessor conditionals INSIDE function and
// task bodies - `ifdef/`else/`endif branches, nested regions, `elsif, and
// code continuing after the region. The directives sit at the enclosing
// code's level, branch statements one deeper, `else/`endif align with their
// matching `ifdef, and the statement after `endif returns to the body level.
// Keep in sync with indent_demo15.expected.sv.

`ifndef INDENT_DEMO15_SV
`define INDENT_DEMO15_SV

class demo_cond_body;

  function void configure();
    `ifdef SIM_FAST
      cycle = 1;
    `else
      cycle = 10;
    `endif
    run();
  endfunction

  task automatic drive();
    `ifndef GATE_LEVEL
      sig <= 1'b1;
    `else
      sig = 1'b1;
    `endif
    wait_done();
  endtask

  function void nested();
    `ifndef OUTER
      `ifdef INNER
        a();
      `else
        b();
      `endif
    `else
        c();
    `endif
    done = 1;
  endfunction

  task automatic multi();
    `ifdef MODE_A
      x = 1;
    `elsif MODE_B
      x = 2;
    `else
      x = 3;
    `endif
    check(x);
  endtask

endclass

`endif
