class demo61 extends uvm_component;
  `uvm_component_utils(demo61)
  int cfg_val;
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(int)::get(this, "", "cfg_val", cfg_val))
      cfg_val = 0;
    uvm_config_db#(int)::set(this, "child", "cfg_val", cfg_val);
  endfunction
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    #100;
    phase.drop_objection(this);
  endtask
  task main_phase(uvm_phase phase);
    phase.jump(uvm_pre_reset_phase::get());
  endtask
endclass
