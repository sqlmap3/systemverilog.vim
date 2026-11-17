// indent regression demo 178: macro arguments whose brace pair the
// gate drops but the tail-drop rule keeps, fixed by stripping both
// braces of each dropped pair, round 18. The C1 fork/join and
// minimal spellings, the split C2 form, comma-split guards, and
// the m07/m08/u36/g23 forward-pairing wins.
// Keep in sync with indent_demo178.expected.sv.

task t();
fork
if (c) `svt_xvm_do_on_with(s, q, {phy_enable == 1'b1;})
join
x = 1;
endtask

begin
if (c) `svt_xvm_do_on_with(s, q, {phy_enable == 1'b1;})
x = 1;
end

begin
`do_with(seq, seqr,
{a == 1; b == 2;})
x = 1;
end

begin
if (c) `svt_xvm_do_on_with(s, q, {a == 1; b == 2})
x = 1;
end

begin
x = foo(q, {a == 1;
b == 2;});
y = 1;
end

begin
x = foo(q, {a == 1;
b == 2;};
y = 1;
end

begin
{vr_cfg1 inside {3'b010};};
y = 1;
end
z = 2;

begin
a = f({x, {y, z};});
y = 1;
end
z = 2;

begin
foo {a == {b == {c};};};
y = 1;
end
z = 2;

begin
foo '{a;};
y = 1;
end
z = 2;
