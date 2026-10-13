// indent regression demo 9: macro calls whose argument is a multi-line
// constraint/block - `uvm_do_with(x, { ... }) and friends. The trailing
// '{' opens a block so the body indents one level and the closing '})'
// returns to the macro line. Keep in sync with indent_demo9.expected.sv.

`ifndef INDENT_DEMO9_SV
`define INDENT_DEMO9_SV

class demo_macro_block;

  function void run_seq();
    `uvm_do_with(demo_seq, {
      a == 1;
      b inside {[0:3]};
      (c, d) inside {[0:15]};
    })
    `uvm_do_with(demo_seq2, {
      e dist {0 := 1, 1 := 2};
    })
    `uvm_do_on_with(seq3, p_sequencer, {
      f == 0;
    })
  endfunction

endclass

`endif
