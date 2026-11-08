`define LONG_MACRO(a, \
  b, \
  c) \
  do_something(a, b, c);
`define BODY_MACRO(x) \
  `ifdef HAS_X \
  `include "body_x.svh" \
  `endif \
  do_final(x);
class demo38;
  function void run();
    `LONG_MACRO(1, 2, 3);
    `BODY_MACRO(4);
  endfunction
endclass
