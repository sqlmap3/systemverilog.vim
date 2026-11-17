// indent regression demo 179: multi-line with and constraint spans
// whose closer line takes the opener line level, round 18. The
// e2/e4 spans, the 3/3c with and constraint forms, and the S4
// three-line span. Closer lines sit at the opener level by design
// (S3 portrait).
// Keep in sync with indent_demo179.expected.sv.

begin
foo with {
a == 1;
b == 2;};
y = 1;
end
z = 2;

begin
foo with {a == 1;
b == 2;};
y = 1;
end
z = 2;

begin
ok = std::randomize(v) with {
a == 1;
b == 2; };
y = 1;
end

class t;
constraint c {
a == 1;
b == 2; };
int z;
endclass

class t;
function void f();
begin
std::randomize(x) with {
a == 1;
b == 2; };
y = 2;
end
endfunction
endclass
