// indent regression demo 6: more group/block-close shapes around preprocessor
// conditionals that real code uses: labeled join/end after `endif, endcase
// after `endif (the case opened before the region), doubly nested `ifndef,
// and endclass after a `ifndef region that wraps the trailing method
// (uvm_component.svh and friends). Keep in sync with indent_demo6.expected.sv.

`ifndef INDENT_DEMO6_SV
`define INDENT_DEMO6_SV

class demo_cond_closes;

  // endcase after `endif: the case opened before the region
      function void pick(int sel);
          case (sel)
      0: begin
                        r = "zero";
          end
      `ifdef WIDE
                1: r = "one";
      `endif
  endcase
   endfunction

  // labeled join after `endif: the fork opened before the region
task automatic wait_all();
        fork : f
      `ifndef SKIP_WAIT
          wait_request();
      `endif
    join : f
  endtask

  // nested conditionals: the inner `endif must not steal the outer's level
  function void nested();
`ifndef OUTER
        `ifndef INNER
                inner = 1;
      `endif
          outer = 1;
    `endif
      endfunction

  // endclass after `endif: the class opened before the region
  `ifndef UVM_NO_DEPRECATED
function void legacy();
          legacy_called = 1;
      endfunction
  `endif
endclass

`endif
