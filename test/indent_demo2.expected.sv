// indent regression demo 2: constructs lifted from uvm_component::new
// (uvm-1.2/src/base/uvm_component.svh) - bare begin blocks, multi-line
// calls under if, string concatenations, multi-line macros with
// concatenations. Keep in sync with indent_demo2.expected.sv.

`ifndef INDENT_DEMO2_SV
`define INDENT_DEMO2_SV

function demo_new (string name, uvm_component parent);
  string error_str;
  uvm_root top;
  uvm_coreservice_t cs;

  super.new(name);

  if (parent==null && name == "__top__") begin
    set_name("");
    return;
  end

  cs = uvm_coreservice_t::get();
  top = cs.get_root();

  begin
    uvm_phase bld;
    uvm_domain common;
    common = uvm_domain::get_common_domain();
    bld = common.find(uvm_build_phase::get());
    if (bld == null)
    uvm_report_fatal("COMP/INTERNAL",
    "attempt to find build phase object failed",UVM_NONE);
    if (bld.get_state() == UVM_PHASE_DONE) begin
      uvm_report_fatal("ILLCRT", {"It is illegal to create a component ('",
        name,"' under '",
        (parent == null ? top.get_full_name() : parent.get_full_name()),
        "') after the build phase has ended."},
      UVM_NONE);
    end
  end

  if (name == "") begin
    name.itoa(m_inst_count);
    name = {"COMP_", name};
  end

  if(parent == this) begin
    `uvm_fatal("THISPARENT", "cannot set the parent of a component to itself")
  end

  if (parent == null)
    parent = top;

  if(uvm_report_enabled(UVM_MEDIUM+1, UVM_INFO, "NEWCOMP"))
    `uvm_info("NEWCOMP", {"Creating ",
    (parent==top?"uvm_top":parent.get_full_name()),".",name},UVM_MEDIUM+1)

  if (parent.has_child(name) && this != parent.get_child(name)) begin
    if (parent == top) begin
      error_str = {"Name '",name,"' is not unique to other top-level ",
      "instances. If parent is a module, build a unique name by combining the ",
      "the module name and component name."};
      `uvm_fatal("CLDEXT",error_str)
    end
    else
      `uvm_fatal("CLDEXT",
    $sformatf("Cannot set '%s' as a child of '%s', %s",
      name, parent.get_full_name(),
      "which already has a child by that name."))
    return;
  end

  m_parent = parent;

  if (!m_parent.m_add_child(this))
    m_parent = null;

  if (!uvm_config_db #(uvm_bitstream_t)::get(this, "", "recording_detail", recording_detail))
    void'(uvm_config_db #(int)::get(this, "", "recording_detail", recording_detail));
end
endfunction

`endif
