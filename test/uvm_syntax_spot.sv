// Syntax spot-check sample for systemverilog.vim.
//
// Constructs are lifted from the UVM 1.2 library source tree
// (uvm-1.2/src: base/ comps/ seq/ tlm1/ tlm2/ reg/ dap/). Every construct
// here is exercised by a pattern/highlight pair in uvm_syntax_checks.txt
// -- keep both files in sync.

`ifndef UVM_SYNTAX_SPOT_SV
`define UVM_SYNTAX_SPOT_SV

`include "uvm_macros.svh"
`include <uvm_macros.svh>
`define spot_macro(a, b) ((a) + (b))
`ifdef spot_extra
`elsif spot_alt
`else
`endif
`undef spot_extra
`timescale 1ns/1ps
`pragma protect

typedef enum { UVM_LOW, UVM_MEDIUM, UVM_HIGH, UVM_FULL, UVM_NONE } uvm_verbosity;
typedef enum { IS_EQ, IS_LT, IS_GT, IS_NE } uvm_check_e;
typedef enum { UVM_READ, UVM_WRITE } uvm_access_e;
typedef struct packed { bit [7:0] addr; bit act; } spot_st;

class spot_seq extends uvm_sequence_base;

  uvm_verbosity verb;
  uvm_check_e chk;
  uvm_bitstream_t bits;
  uvm_active_passive_enum ap_mode;
  uvm_radix_enum radix;
  uvm_transaction tr;

  `uvm_object_utils_begin(spot_seq)
    `uvm_field_enum(uvm_verbosity, verb, UVM_ALL_ON)
    `uvm_field_int(bits, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "spot_seq");
    super.new(name);
  endfunction

  virtual task body();
    uvm_report_info("SPOT", "plain report info", UVM_LOW);
    uvm_report_fatal("SPOT", "plain report fatal", UVM_NONE);
    if (!uvm_report_enabled(UVM_MEDIUM, UVM_INFO, "SPOT"))
      return;
    uvm_wait_for_nba_region();
    `uvm_info("SPOT", "macro info", UVM_LOW)
    `uvm_error("SPOT", "macro error")
    `uvm_do(spot_item)
    uvm_config_db#(int)::set(null, "uvm_test_top", "size", 8);
    uvm_config_db#(int)::get(null, "", "size", sz);
    uvm_resource_db::get_by_name("x", rsrc, rsrc, 1);
    uvm_factory factory = uvm_factory::get();
    spot_item it = spot_item::type_id::create("it");
    $display("bits=%0d", bits);
    if (ids.size() == 0)
      ids.push_back(1);
  endtask

endclass

class spot_test extends uvm_test;

  uvm_active_passive_enum mode;
  uvm_sequencer_base sqr;
  uvm_pool#(string) names;
  uvm_queue#(int) ids;
  uvm_root top_;
  uvm_report_server rsrv;
  uvm_event_base evbase;
  uvm_resource_base rsrc;
  uvm_visitor#(uvm_component) vis;
  uvm_heartbeat hb;
  uvm_link_base lnk;
  uvm_simple_lock_dap#(int) dap;
  uvm_vreg vreg;
  uvm_mem_region mreg;
  uvm_analysis_port #(spot_item) item_ap;
  uvm_tlm_analysis_fifo #(spot_item) item_fifo;
  uvm_tlm_generic_payload gp;
  uvm_tlm_time tt;
  uvm_reg_adapter rad;
  uvm_reg_block blk;
  uvm_reg_field fld;
  uvm_objection obj;
  uvm_domain dom;
  uvm_phase ph;

  `uvm_component_utils(spot_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    uvm_config_db#(uvm_object_wrapper)::set(this, "env*", "default_seq", null);
    factory.set_type_override_by_type(spot_item::get_type(), other::get_type());
    dom = uvm_domain::get_uvm_domain();
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    fork
      begin : spot_proc
        item_fifo.get(it);
        item_ap.write(it);
      end
    join_any
    phase.drop_objection(this);
  endtask

endclass

module spot_dut (input logic clk, output bit ok);
  parameter int spot_w = 8;

  spot_if u_if (
    .clk (clk),
    .rst_n(rst_n)
  );

  timeunit 1ns;
  always @(posedge clk) begin
    #(10ns);
    ok <= ~ok;
  end

  initial begin
    bit [3:0] code = 2'b10;
    code = 'h3F;
    run_test("spot_test");
    $finish;
  end
endmodule

property spot_prop;
  @(posedge clk) req |-> ack ##1 done;
endproperty

a_lbl: assert property (spot_prop)
  else $error("spot_prop failed");

sequence spot_sva_seq;
  @(posedge clk) req ##[1:3] ack [*2] |=> done;
endsequence

property spot_sva_prop;
  @(posedge clk) disable iff (rst_n)
    a throughout b within c intersect d;
endproperty

interface spot_if (input logic clk);
  logic rst_n;
  modport m (input clk, rst_n);
endinterface

// --- .sv top-level units ---
program spot_prog (input logic clk);
  initial begin
    #5ns;
    $display("prog start");
  end
endprogram

package spot_pkg;
  parameter int PKG_W = 4;
endpackage

module spot_sva_tb;
  logic clk, rst_n, req, ack, done;
  logic [3:0] w;

  clocking cb @(posedge clk);
    input req;
    output ack;
  endclocking

  always_ff @(posedge clk) begin
    done <= req;
  end

  always_latch begin
    if (rst_n)
      done <= 0;
  end

  genvar gi;
  generate
    for (gi = 0; gi < 4; gi = gi + 1) begin : g_w
      assign w[gi] = 1'b0;
    end
  endgenerate

  // remaining SVA operators and keywords
  a_assume: assume property (a ##2 b);
  a_restrict: restrict property (a[=2] b);
  a_expect: expect (a[->2] b) else $error("x");
  a_first: assert property (first_match(a) until b);
  a_cover: cover property (a #-# b);
  a_equiv: cover property (a #=# b);
  a_let: let spot_let(x) = x;
  a_implies: assert property (a implies b);
  a_eventually: assert property (s_eventually a);
  a_accept: assert property (accept_on(b) a);
  a_weak: assert property (weak(a) and strong(b));
endmodule

checker spot_chk (logic clk, logic rst_n);
  default clocking cb2 @(posedge clk);
  a_cov2: cover property (req |=> ack);
endchecker

// --- storage/direction keywords, structures, covergroups, this/super ---
module spot_cg;
  localparam int LP = 2;
  const int CV = 1;
  var logic lv;
  static int si;
  automatic int ai;

  logic [3:0] cpa, cpb;

  covergroup cg @(posedge clk);
    cp_a: coverpoint cpa {
      bins zero = {0};
      bins lo[] = {[1:3]};
      ignore_bins hi = {8'hF0};
    }
    cp_b: coverpoint cpb;
    cr_ab: cross cp_a, cp_b;
  endgroup

  function automatic void worker(ref int ri);
    lv = ri;
  endfunction

  union tagged {
    int i;
    bit b;
  } ut;

  enum { ON, OFF } st;
endmodule

class spot_this_super extends spot_seq;
  rand int rf;
  local int li;
  function void use_this_super();
    this.rf = super.rf;
  endfunction
endclass

export "DPI-C" task spot_dpi_task;

/**
 * @brief DVT doc comment block
 * @param req_data Transaction request data
 * @return Success flag
 */
function int spot_doc_fn(int req_data);
  /// @note single line DVT doc comment
  string msg = $sformatf("Value: %0d, hex=0x%08h\n", req_data, req_data);
  my_custom_t my_typed_var;
  my_scope_pkg::my_scoped_call();
  return 1;
endfunction

`endif
