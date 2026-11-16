// indent regression demo 175: closer suffix boundaries, round 17. The
// first block pins every terminator and operator suffix of the
// tail-drop rule plus the iff and with word suffixes and trailing
// comments. The second block pins keep-side shapes whose closer the
// rule keeps, including word boundaries that must not match.
// Keep in sync with indent_demo175.expected.sv.

begin
foo {a == 1;}, y = 1;
f(foo {a == 1;});
z = foo {a == 1;} + b;
z = foo {a == 1;} & b;
foo {a == 1;} iff (c);
x = foo {a == 1;} with (b);
foo {a == 1;}.x;
foo with {a == 1;} // comment
foo with {a == 1;} /* c */
x = c ? foo {a == 1;} : b;
z = foo {a == 1;} | b;
z = foo {a == 1;} ^ b;
z = foo {a == 1;} - b;
z = foo {a == 1;} * b;
z = foo {a == 1;} % b;
z = foo {a == 1;} == b;
z = foo {a == 1;} < b;
z = foo {a == 1;} > b;
z = foo {a == 1;} != b;
z = foo {a == 1;} ? b : c;
z = foo {a == 1;} / b;
foo {a == 1;} within (b);
foo {a == 1;} iffx (c);
y = 1;
end
z = 2;

begin
foo with {a == 1;}
foo with {a == 1}
foo {a == 1;} bar;
f(foo {a == 1;} bar);
foo {a, b}[0];
foo {a == 1;}[0];
struct {int a;} foo_t;
enum {A, B} e;
typedef struct {int a;} foo_t;
typedef enum {A, B} e_t;
union {int a;} u;
constraint c {a == 1;}
{vr_cfg1 inside {3'b010};};
foo with {a == 1 /* c */};
foo with {a == 1; /* 中文 */};
foo '{a;};
x = {a inside {1, 2}};
a dist {1 := 1, 2 := 2};
a dist {foo := 1, bar := 2};
a intersect {1, 2};
a intersect {foo, bar};
return {a, b};
return {1, 2};
unique {a, b};
x = (a inside {1, 2});
y = 1;
end
z = 2;
