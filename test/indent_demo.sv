// indent regression demo: this header must stay identical in
// indent_demo.sv and indent_demo.expected.sv
`timescale 1ns/1ps
`pragma protect

`ifndef INDENT_DEMO_SV
`define INDENT_DEMO_SV

`include "uvm_macros.svh"
        `include "demo_pkg.sv"

class demo_class extends uvm_object;
            `uvm_object_utils_begin(demo_class)
   `uvm_field_int(mode, UVM_ALL_ON)
                  `uvm_object_utils_end

  function void build_phase(uvm_phase phase);
              if (mode == 0)
`uvm_info("ID", "x", UVM_LOW)
                  else
    `uvm_error("ID", "y")
   endfunction : build_phase

      function void check();
  if (a)
                  x = 1;
          else if (b)
      y = 2;
  else
              z = 3;

                        `uvm_info("ID",
$sformatf("value=%0d", v),
  UVM_LOW)
   endfunction : check

      virtual task run_phase(uvm_phase phase);
  case (op)
        2'd0: if (a == 1)
`uvm_info("ID", "z", UVM_LOW)
              else
      `uvm_error("ID", "w")
        endcase

              fork
  begin : proc
                        `uvm_do(demo_seq)
      end : proc
                join_any
        disable fork;
  wait fork;
   endtask : run_phase
endclass : demo_class

class demo_comp #(type T = int) extends uvm_component;
                `uvm_component_utils_begin(demo_comp)
      `uvm_field_int(T, UVM_ALL_ON)
      `uvm_component_utils_end

  function new(string name, uvm_component parent);
                  super.new(name, parent);
        endfunction : new
endclass : demo_comp

class macro_user extends demo_pkg;
            `uvm_object_utils(macro_user)

      function void run();
`uvm_info("ID", "begin endclass", UVM_LOW)
                `uvm_create(tr)
  `uvm_do_with(seq, { a == b; })
        `uvm_send(tr)
                          `uvm_warning("ID",
$sformatf("x=%0d", x),
    UVM_LOW)
   endfunction : run
          endclass : macro_user

    class inc_user;
                        `include "inc_user_body.svh"
        endclass : inc_user

`define uvm_demo_info(ID, MSG) \
            begin \
      if (uvm_report_enabled(ID)) \
        uvm_report_info(ID, MSG); \
    end

module demo_top (
            input logic clk,
        output logic op
    );
assign done = (op) ? 1'b1 : 1'b0;

initial begin
              mode = 2'b00;
      end

always_comb begin
          mode_n = ~mode;
   end

typedef struct packed {
    bit a;
          bit b;
} st_t;

        typedef enum logic [1:0] {S0 = 2'b00, S1 = 2'b01} state_e;

  genvar i;
generate
    if (GEN_A) begin : g_a
                  wire w_a;
      end
  else begin : g_b
                    wire w_b;
          end
      for (i = 0; i < 4; i = i + 1) begin : g_loop
                        assign w_a[i] = 1'b0;
  end
  case (GEN_SEL)
                2'd0: begin : g_sel0
              wire w_c;
        end
    default: begin : g_sel1
                wire w_d;
      end
          endcase
endgenerate

demo_if u_if (
        .clk  (clk),
  .rst_n(rst_n)
      );

covergroup cg @(posedge clk);
      cp: coverpoint mode {
  bins lo = {0};
                }
endgroup
endmodule : demo_top

interface demo_if (
            input logic clk
    );
logic rst_n;
      modport m (input clk, rst_n);
endinterface : demo_if

package demo_pkg;
parameter int W = 8;
        typedef enum {A, B} mode_e;
function automatic int add(int a, int b);
                return a + b;
      endfunction : add
endpackage : demo_pkg

interface class printable;
   pure virtual function void print();
 endclass : printable

/*
  multi-line comment
  spanning lines
*/

`ifdef UVM_NO_DPI
            `include "dpi_disable.svh"
      `include "dpi_disable2.svh"
`endif

`ifdef EXTRA
            parameter int W = 8;
`elsif ALT
  parameter int W = 4;
`endif

`undef EXTRA

`define HALF(a, b) \
      ((a) + \
          (b))

`endif
