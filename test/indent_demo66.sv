class demo66_item extends uvm_sequence_item;
rand int data;
`uvm_object_utils_begin(demo66_item)
`uvm_field_int(data, UVM_ALL_ON)
`uvm_object_utils_end
function new(string name = "demo66_item");
super.new(name);
endfunction
endclass
class demo66_driver extends uvm_driver #(demo66_item);
`uvm_component_utils(demo66_driver)
uvm_blocking_put_port #(demo66_item) put_port;
uvm_analysis_port #(demo66_item) ap;
function new(string name, uvm_component parent);
super.new(name, parent);
endfunction
task run_phase(uvm_phase phase);
demo66_item req;
forever begin
seq_item_port.get_next_item(req);
put_port.put(req);
ap.write(req);
seq_item_port.item_done();
end
endtask
endclass
class demo66_env extends uvm_env;
`uvm_component_utils(demo66_env)
uvm_tlm_fifo #(demo66_item) fifo;
function new(string name, uvm_component parent);
super.new(name, parent);
endfunction
function void build_phase(uvm_phase phase);
fifo = new("fifo", this);
endfunction
endclass
