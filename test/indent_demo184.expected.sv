// indent regression demo 184: SLP gate hole, statement then close
// brace then pair. The pair after the close brace must still be
// stripped. Pins the corrected gate: the close brace must come after
// the open brace. Round 20, gate-1 probe g1c.
// Keep in sync with indent_demo184.expected.sv.
begin
  foo(); }; bar {a == 1;};
  y = 1;
end
z = 2;
