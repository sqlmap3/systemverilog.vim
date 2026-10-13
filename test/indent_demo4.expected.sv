// indent regression demo 4: group/block closes that follow a preprocessor
// conditional. They close something opened OUTSIDE the `ifndef...`endif
// region (UVM 1.2 has this in uvm_component.svh do_print, uvm_resource.svh,
// uvm_traversal.svh, uvm_misc.svh, uvm_sequencer_base.svh, and a bare `end'
// in uvm_report_server.svh), so they must resolve through the region instead
// of aligning with it. Keep in sync with indent_demo4.expected.sv.

`ifndef INDENT_DEMO4_SV
`define INDENT_DEMO4_SV

class demo_guarded extends uvm_object;

  function void do_print_work(uvm_printer printer);
    if (recording_detail != 0)
    case (recording_detail)
      UVM_LOW : printer.print_generic("recording_detail", "uvm_verbosity",
      $bits(recording_detail), "UVM_LOW");
      default : printer.print_field_int("recording_detail", recording_detail,
      $bits(recording_detail), UVM_DEC, , "integral");
    endcase

    `ifndef UVM_NO_DEPRECATED
      if (enable_stop_interrupt != 0) begin
        printer.print_field_int("enable_stop_interrupt", enable_stop_interrupt,
        $bits(enable_stop_interrupt), UVM_BIN, ".", "bit");
      end
    `endif
  endfunction

  task automatic drain();
    foreach (q[i]) begin
      `ifndef UVM_ENABLE_DRAIN
        break;
      `endif
    end
  endtask

  function string label();
    `ifdef USE_SUFFIX
      return "suffix";
    `endif
    return "plain";
  endfunction

  function void after_all();
    `ifndef UVM_NO_DEPRECATED
      warn("deprecated");
    `endif
    ok = 1;
  endfunction

endclass

`endif
