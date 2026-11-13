class c;
task t();
if (en) begin
dut_cfg.sigle_write_read(0, ral.CFG, {'h0,
varg_common::en[1],
cfg.tunnel_ind[0]},
rd_data, 'REG_BACK_FRONT_IND);
x1 = 1;
y1 = {'h0, sig[0]};
x2 = 2;
z1 = {3'b0, sig[0]};
x3 = 3;
a1 = {(p+q), sig[0]};
m1 = 1;
a3 = {~mask, sig[0]};
m3 = 3;
a4 = {!flg, sig[0]};
m4 = 4;
a5 = {-v, sig[0]};
m5 = 5;
a6 = {'h0, 'h1};
m6 = 6;
a7 = {+v, sig[0]};
m7 = 7;
a8 = {`FOO, sig[0]};
m8 = 8;
a9 = {{a}, {b}};
m9 = 9;
end
w = 10;
endtask
endclass
