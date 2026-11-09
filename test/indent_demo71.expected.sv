module demo71;
initial begin
  if (a) begin
    dut_cfg.sigle_write_read(0, y, {my_sig, 2'b0, 4'b0}, rd_data, `REG);
  end
  else begin
    dut_cfg.sigle_write_read(0, y, {pkg::my_sig, 2'b0, 4'b0}, rd_data, `REG);
    dut_cfg.sigle_write_read(0, y, {varg_video_routing::varg_video_routing_in_chan_link_sel[1], varg_video_routing::varg_video_routing_in_chan_link_sel[0]}, rd_data, `REG);
  end
  y = {my_sig, 2'b0};
end
covergroup cg;
  cp: coverpoint x {
    bins b0 = {8'hF0};
    bins b1 = {[0:15]};
    bins b2 = {0};
  }
endgroup
typedef enum logic [1:0] {
  S0 = 2'b00,
  S1 = 2'b01
} state_t;
endmodule
