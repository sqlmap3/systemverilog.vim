// indent regression demo 18: quoted `inside {...}` sets. A set containing
// string literals must be dropped whole before the concatenation '}' drop,
// or that drop eats the set's closing '}' and leaves an unmatched '{'
// (codes 'xb' instead of 'x'), so the line after the if is over-indented.
// Covers: quoted set, unquoted set, a '}' inside a string, two sets on one
// line, and a range mixed with a string. Keep in sync with
// indent_demo18.expected.sv.

class demo_inside_quoted;

task run();
if (y inside {"a", "b"})
x = 1;
if (y inside {P, Q})
x = 2;
if (y inside {"}", "b"})
x = 3;
if ((a inside {"x", "y"}) && (b inside {P, Q}))
x = 4;
if (y inside {[0:15], "z"})
x = 5;
if (y inside {"a", "b"}) begin
x = 6;
end
endtask

endclass
