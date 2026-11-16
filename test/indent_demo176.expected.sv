// indent regression demo 176: nested and vanishing pairs, guard shapes,
// and coverpoint and constraint context blocks, round 17. The final
// four blocks are known gap anchors: their all column zero vectors are
// the standing gap signatures, preserved by design, not ideal indent.
// Keep in sync with indent_demo176.expected.sv.

begin
  foo {a == {b, c};};
  coverpoint x { bins b = {1}; };
  coverpoint x { bins b = {1, 2}; };
  coverpoint x { bins b = {[0:3]}; };
  foo {a == {b, c}; d == {e, f};};
  foo {a inside {1}; b == {c};};
  foo {a == {"x", "y"};};
  foo {a == {b == {c};};};
  coverpoint x { bins b = {1} iff (y); };
  with {a inside {1, 2}; b == 3;};
  foo with {a inside {1, 2}; b == 3;};
  foo with {bar with {a == 1;};};
  foo {a;}; bar {b;};
  foo {a;}; bar {b;}; baz {c;};
  foo with {a dist {1 := 1};};
  foo with {a intersect {1, 2};};
  foo with {unique {a, b};};
  foo with {a inside {1, 2}};
  foo {a == {b, c} + d;};
  foo {a == {b, c} d;};
  foo {a == {b, c}[0];};
  foo {a == {b, c} foo;};
  foo {a == {b /* } */, c};};
  foo {{a, b}};
  coverpoint x { bins b = {1}; }
  foo with {a == {b, c};};
  foo with {a == 1;}; foo with {b == 2;};
  y = 1;
end
z = 2;

begin
  x = {2{data}};
  x = {2{a, b}};
  x = {<<{a, b}};
  x = {>>{a, b}};
  x = {a, b};
  x = {sig, 2'b0};
  bins b = {[0:15]};
  bins b = {0};
  bins b = {8'hF0};
  first: {val++;} ;
  x = cond ? {a} : {b};
  f({a, b});
  y = f({a, b});
  $display("{a};");
  $display("{a == 1;};");
  x = '{a, b};
  x = {a, b} & mask;
  x = {sig[1], sig[0]};
  x = {'h0, sig[0]};
  x = {2 {data}};
  x = c ? {a} : {b};
  constraint c {unique {a, b};};
  a = f({x, {y, z};});
  std::randomize(vr_cfg1);
  y = 1;
end
z = 2;

covergroup cg;
  coverpoint x { bins b = {1}; }
  coverpoint y { bins c = {[0:3]}; }
endgroup

constraint c {a == 1;}
constraint d {a inside {1, 2};}
constraint e {a dist {1:=1};}
constraint f {unique {a, b};}

begin
  typedef struct { int a; } foo;
  typedef enum {A, B} e_t;
  y = 1;
end

covergroup cg;
  coverpoint x { bins b = {1} iff (y); }
endgroup

begin
  x = {a,
  b};
  y = 1;
end
z = 2;

function void f();
  x = {
    a,
    b};
  y = 1;
endfunction

class c;
  constraint cc {
  foo with {a == 1;}; }
  y = 1;
endclass

covergroup cg;
  coverpoint x { bins b = {1}; };
endgroup

class c;
  constraint cc {
    foo with {a == 1;};
  }
endclass

class c;
  constraint cc {
  x = 1; }
  y = 1;
endclass

begin
x = {a, {b, c}};
y = 1;
end
z = 2;

begin
x = {a,{b,c}};
y = 1;
end
z = 2;

begin
foo {a == {b, c}};
y = 1;
end
z = 2;

begin
foo with {a == 1; /* } */ };
y = 1;
end
z = 2;
