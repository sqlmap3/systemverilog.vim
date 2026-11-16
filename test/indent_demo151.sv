class c;
  extern function void foo(
                           input int a);
  `ifdef X
    extern function void bar(
                             input int b);
  `endif
  int y;
endclass
