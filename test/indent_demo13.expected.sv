// indent regression demo 13: multi-line function/task prototype signatures.
// The argument continuation lines and the closing ');' column-align their
// type keywords under the first argument (a definition keeps the plain flat tail). Keep in sync with indent_demo13.expected.sv.

`ifndef INDENT_DEMO13_SV
`define INDENT_DEMO13_SV

class demo_protos;

  extern virtual function void set_config_int (string inst_name,
                                               string field_name,
                                               uvm_bitstream_t value);
  extern function void configure (uvm_reg_block parent,
                                  uvm_mem mem = null,
                                  uvm_reg_addr_t offset = 0);
  extern virtual function bit do_compare (uvm_object rhs,
                                          uvm_comparer comparer);
  pure virtual function void print();

  virtual function void raised (uvm_objection objection,
                                uvm_object source_obj,
                                string description, int count);
    $display("raised: %s", description);
  endfunction

  virtual function void dropped (uvm_objection objection,
                                 string description, int count);
  endfunction

endclass

`endif
