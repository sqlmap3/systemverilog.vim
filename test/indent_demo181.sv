// indent regression demo 181: Group C shapes whose inner phantom
// closer already cancels the outer opener, so the outer closer must
// be blocked, plus the dist/intersect/return guards, round 18. The
// p_2b nested-concatenation gap is a known residual and is
// deliberately not pinned here; it keeps its standing vector.
// Keep in sync with indent_demo181.expected.sv.

begin
foo {a == {b, c} d;};
y = 1;
end
z = 2;

begin
foo {a == {b, c}[0];};
y = 1;
end
z = 2;

begin
foo {a == {b, c} foo;};
y = 1;
end
z = 2;

begin
foo {a == {b /* } */, c};};
y = 1;
end
z = 2;

begin
ok = std::randomize(v) with { x dist {0:=1, 1:=2}; };
y = 1;
end

class t;
function void f();
begin
std::randomize(x) with { x dist {0:=1, 1:=2}; };
y = 2;
end
endfunction
endclass

begin
foo with { x dist {0:=1}; };
y = 1;
end
z = 2;

begin
foo with { x dist {0:=1, 1:=2}; y == 1 };
y = 1;
end
z = 2;

begin
foo with { x intersect {1, 2}; };
y = 1;
end
z = 2;

begin
foo with { x return {a, b}; };
y = 1;
end
z = 2;
