class demo69_seq extends uvm_sequence #(uvm_sequence_item);
`uvm_object_utils(demo69_seq)
rand int n;
function new(string name = "demo69_seq");
super.new(name);
endfunction
task body();
uvm_sequence_item item;
int v;
v = $urandom_range(10, 1);
`uvm_info("SEQ", $sformatf("n=%0d", n), UVM_LOW)
start_item(item);
if (!item.randomize())
`uvm_error("SEQ", "randomize failed")
finish_item(item);
if (!$cast(item, item))
`uvm_error("SEQ", "cast failed")
endtask
endclass
class demo69_vseq extends uvm_sequence;
`uvm_object_utils(demo69_vseq)
demo69_seq s1;
function new(string name = "demo69_vseq");
super.new(name);
endfunction
task body();
s1 = demo69_seq::type_id::create("s1");
s1.start(m_sequencer);
endtask
endclass
