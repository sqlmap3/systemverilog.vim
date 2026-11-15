class c;
  covergroup cg;
    coverpoint x {
      bins b = {1, 2} iff (en);
    }
    bins d = {3, 4};
  endgroup
endclass
