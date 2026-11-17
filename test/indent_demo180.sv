// indent regression demo 180: the e8 early-close span and the six
// B-group single-line shapes whose phantom opener leaked one level,
// round 18. The early-close line takes the opener level; each
// B-group statement keeps the following lines at the enclosing
// level. The unterminated-string shape closes the file.
// Keep in sync with indent_demo180.expected.sv.

begin
foo with {
a == 1;};
b == 2;
y = 1;
end
z = 2;

begin
foo {x == {2{a}};};
y = 1;
end
z = 2;

begin
foo with {a == {2{b}};};
y = 1;
end
z = 2;

begin
f(x, foo {a);};
y = 1;
end
z = 2;

begin
foo with {a inside {1, {2}};};
y = 1;
end
z = 2;

begin
foo {a == {};};
y = 1;
end
z = 2;

begin
foo with {a == "x;};
y = 1;
end
z = 2;
