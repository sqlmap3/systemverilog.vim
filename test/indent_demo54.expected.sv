package demo54_pkg;
typedef enum logic [1:0] {IDLE, BUSY} state_t;
`ifdef HAS_EXTRA
  typedef struct packed {logic [7:0] d; logic v;} pkt_t;
`endif
export demo54_pkg::*;
endpackage
module demo54_dut(input logic clk);
logic sig;
endmodule
bind demo54_dut demo54_mon u_mon(.clk(clk), .sig(sig));
module demo54_mon(input logic clk, input logic sig);
initial begin
  $display("bound");
end
endmodule
config demo54_cfg;
  design demo54_pkg.demo54_dut;
  default liblist demo54_pkg;
endconfig
