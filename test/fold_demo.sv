// Fold regression sample for systemverilog.vim folding.
// Fold levels are verified by test/run_fold_test.sh.
`ifndef FOLD_DEMO_SV
`define FOLD_DEMO_SV

/* block comment
   spanning lines
   gets folded with 'comment' */

`define LONG_MACRO(a, b) \
  ((a) + \
   (b))

`ifdef FOOTPT
typedef enum { A = 1, B = 2 } mode_e;
`else
typedef enum { A = 0, B = 1 } mode_e;
`endif

package demo_pkg;
  parameter int W = 8;

  function automatic int add(int a, int b);
    return a + b;
  endfunction : add
endpackage : demo_pkg

module demo_top #(
  parameter int P = 2
) (
  input  logic clk,
  input  logic rst_n,
  output logic [P-1:0] dout
);
  demo_pkg::mode_e mode;
  assign dout = (mode == demo_pkg::A) ? '0 : '1;

  interface class printable;
    pure virtual function void print();
  endclass : printable

  class printer extends demo_pkg;
    `uvm_object_utils_begin(printer)
      `uvm_field_int(mode, UVM_ALL_ON)
    `uvm_object_utils_end

    function void print();
      $display("printer");
    endfunction
  endclass : printer

  always_ff @(posedge clk or negedge rst_n) begin : proc_a
    if (!rst_n) begin
      mode <= demo_pkg::A;
    end else if (mode == demo_pkg::B) begin
      mode <= demo_pkg::A;
    end
  end : proc_a

  // assert property must NOT open a fold
  a_lbl: assert property (@(posedge clk) rst_n |-> mode != demo_pkg::A)
    else $error("bad mode");

  demo_if u_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
endmodule : demo_top

interface demo_if (
  input logic clk
);
  modport m (input clk);
endinterface : demo_if

// {{{ temporary debug logic, remove after bring-up
module debug_helper;
  always #1ns $display("tick");
endmodule
// }}}

`endif // FOLD_DEMO_SV
