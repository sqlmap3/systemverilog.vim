class demo56 extends uvm_object;
rand int count;
rand bit [7:0] data;
`uvm_object_utils_begin(demo56)
`uvm_field_int(count, UVM_ALL_ON)
`uvm_field_int(data, UVM_ALL_ON)
`uvm_object_utils_end
function new(string name = "demo56");
super.new(name);
endfunction
endclass
class demo56_comp extends uvm_component;
`uvm_component_utils(demo56_comp)
demo56 obj;
function new(string name, uvm_component parent);
super.new(name, parent);
endfunction
function void build_phase(uvm_phase phase);
obj = demo56::type_id::create("obj", this);
endfunction
endclass
