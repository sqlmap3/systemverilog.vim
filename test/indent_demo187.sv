// indent regression demo 187: based-literal strip must never be gated
// on the open brace. End-of-line close variant of demo 186: the nest
// rule fires only with the apostrophe residue present. Pins the
// corrected grouping. Round 20, gate-2 probe g2j.
// Keep in sync with indent_demo187.expected.sv.
begin
x = 'hFF}
y = 1;
end
z = 2;
