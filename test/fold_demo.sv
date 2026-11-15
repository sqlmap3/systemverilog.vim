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

// --- additional fold units ---
clocking cb @(posedge clk);
  input rst_n;
endclocking

checker demo_chk (logic clk, logic rst_n);
  a_cov: cover property (clk |=> rst_n);
endchecker

program demo_prog (input logic clk);
  initial begin
    $display("prog");
  end
endprogram

property demo_prop;
  @(posedge clk) rst_n |-> ##1 rst_n;
endproperty

sequence demo_seq;
  rst_n ##1 rst_n;
endsequence

covergroup cg @(posedge clk);
  cp: coverpoint mode {
    bins lo = {0};
  }
endgroup

config cfg_demo;
  design work.demo_top;
  instance demo_top.u_if use work.demo_if;
endconfig

module with_specify;
  specify
    specparam t_rise = 1;
    (a => b) = (t_rise);
  endspecify
endmodule

primitive udp_and (out, a, b);
  output out;
  input a, b;
  table
    0 0 : 0;
    0 1 : 0;
    1 0 : 0;
    1 1 : 1;
  endtable
endprimitive

randsequence (main)
  main : first second;
  first : { $display("first"); };
  second : { $display("second"); };
endsequence

class dpi_proto_c;
  extern function void f1();
  import "DPI-C" function void dpi_f();
  import "DPI-C" context function void dpi_ctx();
  import "DPI-C" pure function void dpi_pure();
  export "DPI-C" function exp_f;
  task real_t();
    $display("t");
  endtask
  function void real_f();
    $display("f");
  endfunction
endclass

class str_edge_c;
  function void f();
    $display("begin // x\\");
    $display("http://ok");
    $display("a\\");
  endfunction
endclass

class proto_qual_c;
  extern protected function void a();
  extern local function void b();
  extern protected virtual function void c();
  extern local task d();
  extern protected function void e();
  extern virtual protected function void f();
  extern local virtual task g();
  extern protected static function void h();
  extern local static function void i();
  function void real_fn();
    x = 1;
  endfunction
endclass

module dc_b1_m;
  default clocking cb @(posedge clk);
    input #1 a;
    output #1 b;
  endclocking
  x = 1;
endmodule

module dc_b2_m;
  default clocking cb;
  x = 1;
endmodule

module dc_b3_m;
  default clocking @(posedge clk);
  x = 1;
endmodule

checker dc_b4_c;
  default clocking @(posedge clk);
    x = 1;
  endclocking
  cover property (p1);
endchecker

checker dc_b5_c;
  default clocking @(posedge clk);
  cover property (p1);
endchecker

module dc_b6_m;
  default clocking @(posedge clk); endclocking
  x = 1;
endmodule

module dc_b7_m;
  default clocking cb @(posedge clk);
    x = 1;
  endclocking : cb
  y = 2;
endmodule

module dc_b8_m;
  default clocking cb @(posedge clk);
    /* endclocking */
    // endclocking
    x = 1;
  endclocking
  y = 2;
endmodule

module dc_b9_m;
  default clocking
    cb @(posedge clk);
    x = 1;
  endclocking
  y = 2;
endmodule

module dc_c1_m;
  default clocking cb @(posedge clk);
    input #1 a;
    /* http://example.com/spec */
    output #1 b;
  endclocking
  x = 1;
endmodule

module dc_c2_m;
  default clocking cb @(posedge clk);
    /* comment start
    // note */
    input #1 a;
  endclocking
  x = 1;
endmodule

module dc_c9b_m;
  default clocking cb @(posedge clk);
    input #1 a;
    $display("a\n/* trap");
  endclocking
  x = 1;
endmodule

module dc_c6_m;
  default clocking cb;
  /* http://example.com/spec */
  x = 1;
endmodule

module dc_c7_m;
  default clocking cb;
  /* start
  // note */
  x = 1;
endmodule

module dc_c8_m;
  default clocking cb @(posedge clk);
    input #1 a;
  endclocking
  /* http://example.com/spec */
  x = 1;
endmodule

module dc_e6_m;
  default clocking cb @(posedge clk); /* http://example.com/spec */
    input #1 a;
  endclocking
  x = 1;
endmodule

`endif // FOLD_DEMO_SV
