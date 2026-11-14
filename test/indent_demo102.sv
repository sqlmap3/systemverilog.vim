class c;
task t();
y = {a, b} + {c, d};
m1 = 1;
y = {a, b} - {c, d};
m2 = 2;
y = {a, b} * {c, d};
m3 = 3;
y = {a, b} & {c, d};
m4 = 4;
y = {a, b} << {c, d};
m5 = 5;
y = {a, b} && {c, d};
m6 = 6;
y = ~{a, b};
m7 = 7;
return {a, b};
m8 = 8;
y = {a, b}.foo;
m9 = 9;
endtask
endclass
