// indent regression demo 174: single-line word plus brace pairs whose
// closer the tail-drop rule eats, fixed by stripping both braces of
// each qualifying pair before the brace gate, round 17.
// The first block stacks neutral probes, each following block pins one
// keyword opener against its no-brace control baseline.
// Keep in sync with indent_demo174.expected.sv.

begin
foo with {a == 1;};
foo bar {a == 1;};
std::randomize(vr_cfg1) with {vr_cfg1 inside {3'b010, 3'b101, 3'b110};};
std::randomize(vr_cfg1) with {vr_cfg1 inside 3'b010;};
std::randomize(vr_cfg1) with {vr_cfg1 == 3'b010;};
std::randomize(vr_cfg1) with {vr_cfg1 inside {3'b010, 3'b101, 3'b110}};
foo with {a inside {1, 2};};
std::randomize(vr_cfg1) with {vr_cfg1 == 1};
foo with{a == 1;};
foo with {a == 1};
coverpoint x {a == 1;};
bins b {a == 1;};
assert (a) {b == 1;};
f(a) {b == 1;};
x.randomize() with {a == 1;};
constraint c {a == 1;};
constraint c {a inside {1, 2};};
do {a == 1;};
while (a) {b = 1;};
repeat (3) {b = 1;};
forever {b = 1;};
wait_order (a) {b = 1;};
foreach (a[i]) {b = 1;};
foreach arr {b == 1;};
wait (a) {b = 1;};
wait {a == 1;};
if (a) {b = 1;};
cfg1 {a;};
x = 1; foo {a;};
f(2) {a;};
a[2] {b;};
foo with {a == "}";};
foo with {a == "x"};
foo with {a == "x\"}";};
foo with {a inside {"}", "x"};};
foo with {a inside {1}; b inside {2};};
foo with{a inside{1,2};};
foo with {a inside {1, 2}; b == 2;};
foo with {};
foo {a;}; bar {b;};
foo with {bar {b;};};
foo with {a dist {1:=1, 2:=2};};
foo with {unique {a, b};};
x = check(foo with {a == 1;});
x = arr[foo with {a == 1;}];
foo with {a == 1;}; // done
foo with {a == 1;}; // }
foo with {a == 1;}; // 中文注释
y = 1;
end
z = 2;

clocking cb {a == 1;};
y = 1;
endclocking
z = 2;
class foo {a == 1;};
y = 1;
endclass
z = 2;
class foo extends bar {a == 1;};
y = 1;
endclass
z = 2;
function foo {a == 1;};
y = 1;
endfunction
z = 2;
task t {a == 1;};
y = 1;
endtask
z = 2;
covergroup cg {a == 1;};
y = 1;
endgroup
z = 2;
sequence s {a == 1;};
y = 1;
endsequence
z = 2;
checker c {a == 1;};
y = 1;
endchecker
z = 2;
primitive p {a == 1;};
y = 1;
endprimitive
z = 2;
specify {a == 1;};
y = 1;
endspecify
z = 2;
config c {a == 1;};
y = 1;
endconfig
z = 2;
randsequence (m) {a == 1;};
y = 1;
endsequence
z = 2;
