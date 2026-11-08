task t;
  `ifdef A
    x = 1;
  `endif
  `define MULTI(a) \
    y = a; \
    z = a + 1;
  `ifdef B
    w = 2;
  `endif
endtask
