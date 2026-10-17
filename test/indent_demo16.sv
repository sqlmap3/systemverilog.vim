// indent regression demo 16: macros inside preprocessor conditionals, in
// every scope - `define (backslash body) and `undef inside `ifdef, the
// `uvm_object_utils_begin/_end pair inside `ifdef/`else in a class body,
// `uvm_info in both branches, `uvm_do_with with a multi-line constraint
// inside `ifndef, `uvm_do in the `else arm, `ifdef inside a case item's
// begin/end, a mid-line macro argument, a multi-branch `elsif chain of
// macro calls, single-line instantiation inside `ifdef, and statements
// following `endif after a macro. Keep in sync with
// indent_demo16.expected.sv.

`ifndef INDENT_DEMO16_SV
`define INDENT_DEMO16_SV

`define HDR_MSG "hdr"
`define MULTI(a, b) \
  begin \
    if ((a) > 0) \
      (b) = 1; \
  end

`ifdef EXTRA_DEFS
  `define INNER(x) \
    ((x) + 1)
  `undef UNUSED_SYM
`endif

class demo_macro_cond;

  `ifdef COVERAGE_ON
      `uvm_object_utils_begin(demo_macro_cond)
        `uvm_field_int(mode, UVM_ALL_ON)
      `uvm_object_utils_end
  `else
        `uvm_object_utils(demo_macro_cond)
  `endif

  function void build();
      `ifdef DBG
        `uvm_info("DBG", "building", UVM_LOW)
    `else
          `uvm_info("NODEBUG", "building", UVM_MEDIUM)
    `endif
    super.build();
  endfunction

  task automatic run_phase(uvm_phase phase);
    `ifndef FAST_SIM
          phase.raise_objection(this);
      `uvm_do_with(gen_seq, {
          burst_len inside {[1:8]};
        opcode == CMD_WRITE;
      })
            phase.drop_objection(this);
    `else
      `uvm_do(gen_seq)
    `endif
  endtask

  function void report();
    case (mode)
      0: begin
            `ifdef EXTRA
                  `uvm_info("CASE", "extra", UVM_LOW)
        `endif
      end
      default: begin
                `uvm_warning("CASE", "default")
      end
    endcase
  endfunction

  virtual function void phase_ended();
      `uvm_info("PH", `HDR_MSG, UVM_NONE)
    `ifdef MULTI_DEFINE
            `MULTI(a, b)
    `endif
        done = 1;
  endfunction

  function void chain();
      `ifdef MODE_A
        `uvm_info("A", "a", UVM_LOW)
    `elsif MODE_B
      `uvm_info("B", "b", UVM_LOW)
        `else
    `uvm_info("C", "c", UVM_LOW)
      `endif
      check(mode);
  endfunction

endclass

module demo_tb_top;
  `ifdef USE_IF
        demo_if u_if (.clk (clk));
  `endif

  initial begin
      `ifdef PLUSARG
      $display("plusarg");
    `else
            $display("no plusarg");
    `endif
    #10;
  end
endmodule

`endif
