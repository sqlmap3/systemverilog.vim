// indent regression demo 185: based-literal strip must never be gated
// on the open brace. The double close after an unsized based literal
// needs the apostrophe residue the strip leaves behind. Pins the
// corrected grouping: the based-literal strip stays ungated.
// Round 20, gate-2 probe g2g.
// Keep in sync with indent_demo185.expected.sv.
begin
  x = {a,
'hFF}}
y = 1;
end
z = 2;
