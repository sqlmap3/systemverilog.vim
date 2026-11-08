interface demo53_if(input logic clk);
logic req;
logic ack;
task do_handshake();
  @(posedge clk);
  req <= 1'b1;
  @(posedge clk);
  req <= 1'b0;
endtask
modport master(
  output req,
  input ack,
  import task do_handshake()
);
modport slave(
  input req,
  output ack,
  export task do_handshake()
);
`ifdef HAS_MON
  modport monitor(
    input req,
    input ack
  );
`endif
endinterface
