// indent regression demo 183: SLP gate hole, randomize-with form. A
// close brace before the first open brace must not skip stripping of
// the later same-line constraint pair. Pins the corrected gate: the
// close brace must come after the open brace. Round 20, probe g1b.
// Keep in sync with indent_demo183.expected.sv.
begin
}; std::randomize(v) with {v == 1;};
y = 1;
end
z = 2;
