// indent regression demo 182: SLP gate hole. A close brace before the
// first open brace must not skip stripping of a later same-line pair
// on the same line. Pins the corrected gate: the close brace must come
// after the open brace. Round 20, gate-1 probe g1a.
// Keep in sync with indent_demo182.expected.sv.
begin
}; foo {a == 1;};
y = 1;
end
z = 2;
