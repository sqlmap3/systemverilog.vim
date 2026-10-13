// indent regression demo 7: advanced SVA - labeled concurrent assertions
// with action blocks, cover property, expect, multi-line sequence operators,
// properties with formal args, assertions nested under control flow, and
// the bind directive. Keep in sync with indent_demo7.expected.sv.

`ifndef INDENT_DEMO7_SV
`define INDENT_DEMO7_SV

sequence s_handshake;
  req ##[1:3] ack;
endsequence

sequence s_long;
  first_match(req ##0 ack or
  req ##1 !ack ##1 ack);
endsequence

property p_multi;
  @(posedge clk) disable iff (rst_n)
  (req && ack) |-> ##[0:2] s_handshake;
endproperty

property p_args(logic req, logic ack);
  req |-> ack;
endproperty

a_multi: assert property (p_multi)
else begin
  $error("p_multi failed at %0t", $time);
  err_cnt++;
end

c_cov: cover property (req |-> ack)
begin
  cov_cnt++;
end

r_expect: expect (req ##1 ack)
else $error("expect failed");

function void check_all();
  if (rst_n) begin
    a_nest: assert property (req |-> ack)
    else $warning("nested assert");
  end
  else begin
    a_idle: assert property (!(req || ack));
  end
endfunction

bind demo_dut demo_checker chk_i (.clk(clk), .rst_n(rst_n));

`endif
