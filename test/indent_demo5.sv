// indent regression demo 5: brace-heavy excerpts from the real UVM 1.2
// library (uvm_port_base.svh, uvm_reg_mem_built_in_seq.svh, uvm_reg_map.svh,
// uvm_sequence_base.svh). The '{' of a concatenation, assignment pattern or
// call argument must not open a block, in every shape the library actually
// uses: '= {ident', '{' at line start (continuation), ternary '? {a}:{b}',
// call-arg '({"str"' with ')' before the matching '}', the assignment
// pattern ''{ ... }', string arguments containing \n and '(', and
// 'inside {...}' sets. Keep in sync with indent_demo5.expected.sv.

`ifndef INDENT_DEMO5_SV
`define INDENT_DEMO5_SV

class demo_port_base;

function void debug_connected_to(int level, int max_level=-1);
      string save = "";
          string indent = "  ";
  int num, curr_num;
                    uvm_port_base port;
    if (m_provided_by.num() != 0) begin
         foreach (m_provided_by[nm]) begin
                                curr_num++;
                port = m_provided_by[nm];
  save = {save, indent, "  | \n"};
      save = {save, indent, "  |_",nm," (",port.get_type_name(),")\n"};
                    indent = (num > 1 && curr_num != num) ?  {indent,"  | "}:{indent, "    "};
  indent = indent.substr(0,indent.len()-4-1);
      end
          end
              if (level == 0) begin
    if (save != "") begin
          save = {"This port's fanout network:\n\n  ",
  get_full_name()," (",get_type_name(),")\n",save,"\n"};
      end
        end
m_comp.uvm_report_warning("Late Connection",
      {"Attempt to connect ",this.get_full_name()," (of type ",this.get_type_name(),
      ") at or after end_of_elaboration phase.  Ignoring."});
endfunction

  function bit tests_enabled();
        if (uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
      "NO_REG_TESTS", 0) == null &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
  "NO_REG_HW_RESET_TEST", 0) == null ) begin
      return 1;
    end
      return 0;
  endfunction

function void set_range();
                uvm_reg_map_addr_range range = '{ min, max, stride };
  uvm_resource_db#(bit)::set({"REG::", get_full_name()},
      "NO_REG_TESTS", 1);
   endfunction

      function bit state_ok();
  if (!(m_sequence_state inside {UVM_CREATED,UVM_STOPPED,UVM_FINISHED})) begin
            return 0;
        end
      return 1;
  endfunction

endclass

`endif
