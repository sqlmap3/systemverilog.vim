// indent regression demo 19: `ifdef/`endif inside a multi-line `define
// body are macro text, not real conditional compilation. An `ifdef opener
// that immediately follows such a define must not align with the define's
// internal `ifdef (one level too deep); the define's directives must not
// be counted at all. Covers: opener right after a define at file top and
// inside a task, plus a balanced define with `else followed by a real
// `ifdef. Keep in sync with indent_demo19.expected.sv.

`define FOO(x) \
  `ifdef BAR \
  x + 1 \
  `endif
`ifdef BAZ
  y = 1;
`endif

task run();
  `define FOO2(x) \
    `ifdef BAR \
    x + 1 \
    `endif
  `ifdef BAZ
    y = 2;
  `endif
  w = 3;
endtask

`define FOO3(x) \
  `ifdef BAR \
  x + 1 \
  `else \
  x + 2 \
  `endif
`ifdef BAZ
  y = 3;
`endif
