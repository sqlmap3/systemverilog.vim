class c;
  covergroup cg;
    bins b = {1, 2} iff (en);
    bins d = {3, 4};
    bins e = {1, 2} with (item > 0);
    bins f = {[0:15]} iff (en);
    bins g = {1, 2} iff (en) with (item > 0);
    bins h = {3, 4} iff (en);
    bins i = {5, 6} iff (en);
    bins j = {7, 8};
  endgroup
endclass
