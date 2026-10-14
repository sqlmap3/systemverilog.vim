// indent regression demo 14: testbench instantiation - module and interface
// instances with parameter overrides and multi-line named port connections,
// wildcard connections, bind instances with port lists, and port connections
// carrying macro calls. Keep in sync with indent_demo14.expected.sv.

`ifndef INDENT_DEMO14_SV
`define INDENT_DEMO14_SV

`define CLK_SRC clk
`define RST_SRC rst_n
`define CLK_INIT clk = 1'b0

module demo_dut #(parameter int W = 8) (
  input  logic         clk,
  input  logic         rst_n,
  input  logic [W-1:0] wdata,
  output logic [W-1:0] rdata
);
logic [W-1:0] hold;
assign rdata = hold;
endmodule

interface demo_bus_if (input logic clk);
logic req, ack;
endinterface

class demo_checker #(parameter int W = 8);
  function void check(input logic [W-1:0] d);
    if (d === 'x)
      $error("x seen");
  endfunction
endclass

module demo_tb;
logic clk, rst_n;
logic [7:0]  wdata,  rdata;
logic [15:0] wdata16, rdata16;

// simple instantiation, named ports across lines
demo_dut u_dut (
  .clk   (clk),
  .rst_n (rst_n),
  .wdata (wdata),
  .rdata (rdata)
);

// wildcard connection
demo_dut u_dut_star (.*);

// parameter override + port list
demo_dut #(.W(16)) u_dut_wide (
  .clk    (clk),
  .rst_n  (rst_n),
  .wdata  (wdata16),
  .rdata  (rdata16)
);

// interface instantiation
demo_bus_if u_bus (
  .clk (clk)
);

// port connections carrying macro calls
demo_dut u_dut_mc (
  .clk   (`CLK_SRC),
  .rst_n (`RST_SRC),
  .wdata (wdata),
  .rdata (rdata)
);

// bind: checker bound to the dut, parameterized, port list across lines
bind demo_dut demo_checker #(.W(8)) u_chk (
  .clk   (clk),
  .rst_n (rst_n),
  .wdata (wdata)
);

// bind with the connection given by a macro
bind demo_dut demo_checker u_chk2 (
  .clk (`CLK_SRC),
  .rst_n (`RST_SRC)
);

initial begin
  u_bus.req = 1'b0;
  `CLK_INIT
  u_bus.ack  = 1'b1;
end

endmodule

`endif
