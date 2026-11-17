// indent regression demo 186: based-literal strip must never be gated
// on the open brace. Without the strip, the predecessor class of the
// close brace flips and the line over-indents. Pins the corrected
// grouping: the based-literal strip stays ungated. Round 20, g2i.
// Keep in sync with indent_demo186.expected.sv.
begin
x = 'hFF};
y = 1;
end
z = 2;
