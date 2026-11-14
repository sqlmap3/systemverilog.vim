class c;
task t();
y = {a, b}[3:0];
m1 = 1;
dut_cfg.sigle_write_read(0, ral.REG, {a, b}[3:0], rd_data, 0);
m2 = 2;
y = {a, b}[3:0] + {c, d}[1:0];
m3 = 3;
y = foo[{a, b}];
m4 = 4;
y = {2{a, b}}[3:0];
m5 = 5;
y = arr[{a, b}][0];
m6 = 6;
y = {a, b}.foo;
m7 = 7;
dut_cfg.sigle_write_read(0, ral.REG,
{a, b}[3:0], rd_data, 0);
m8 = 8;
y = {a,
b}[3:0];
m9 = 9;
endtask
endclass
