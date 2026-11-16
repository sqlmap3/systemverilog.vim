// indent regression demo 173: the reported transcript, round 17. Five
// single-line randomize with pairs, each leaking one level on the
// pristine plugin and accumulating past the enclosing end.
// Keep in sync with indent_demo173.expected.sv.

for (int i=0; i<`SER_CHIP_NUM; i++) begin
if (varg_common::varg_common_rlink_lane_rate[i] == 16 && varg_common::varg_common_des_port_disable[i] == 0) begin
varg_common::varg_common_ser_tx_cfg1[i] = 3'b110;
varg_common::varg_common_ser_lane_max_speed[i] = 3'b000;
`uvm_fatal("", $sformatf("varg_common_rlink_lane_rate is ok !!!"))
end
else if (varg_common::varg_common_rlink_lane_rate[i] == 12 && varg_common::varg_common_des_port_disable[i] == 0) begin
varg_common::varg_common_ser_tx_cfg1[i] = 3'b010;
varg_common::varg_common_ser_lane_max_speed[i] = 3'b001;
`uvm_error("", $sformatf("varg_common_rlink_lane_rate is error, ser_chip not support 12.8G when Rlinc Mode !!!"))
end
else if (varg_common::varg_common_rlink_lane_rate[i] == 8 && varg_common::varg_common_des_port_disable[i] == 0) begin
std::randomize(vr_cfg1) with {vr_cfg1 inside {3'b010, 3'b101, 3'b110};};
varg_common::varg_common_ser_tx_cfg1[i] = vr_cfg1;
varg_common::varg_common_ser_lane_max_speed[i] = 3'b010;
end
else if (varg_common::varg_common_rlink_lane_rate[i] == 6 && varg_common::varg_common_des_port_disable[i] == 0) begin
std::randomize(vr_cfg1) with {vr_cfg1 inside {3'b001, 3'b010, 3'b101, 3'b110};};
varg_common::varg_common_ser_tx_cfg1[i] = vr_cfg1;
varg_common::varg_common_ser_lane_max_speed[i] = 3'b011;
end
else if (varg_common::varg_common_rlink_lane_rate[i] == 4 && varg_common::varg_common_des_port_disable[i] == 0) begin
std::randomize(vr_cfg1) with {vr_cfg1 inside {3'b100, 3'b001, 3'b010, 3'b101, 3'b110};};
varg_common::varg_common_ser_tx_cfg1[i] = vr_cfg1;
varg_common::varg_common_ser_lane_max_speed[i] = 3'b100;
end
else if (varg_common::varg_common_rlink_lane_rate[i] == 3 && varg_common::varg_common_des_port_disable[i] == 0) begin
std::randomize(vr_cfg1) with {vr_cfg1 inside {3'b000, 3'b100, 3'b001, 3'b010, 3'b101, 3'b110};};
varg_common::varg_common_ser_tx_cfg1[i] = vr_cfg1;
varg_common::varg_common_ser_lane_max_speed[i] = 3'b101;
end
else if (varg_common::varg_common_rlink_lane_rate[i] == 2 && varg_common::varg_common_des_port_disable[i] == 0) begin
std::randomize(vr_cfg1) with {vr_cfg1 inside {3'b111, 3'b000, 3'b100, 3'b001, 3'b010, 3'b101, 3'b110};};
varg_common::varg_common_ser_tx_cfg1[i] = vr_cfg1;
varg_common::varg_common_ser_lane_max_speed[i] = 3'b111;
end
end
