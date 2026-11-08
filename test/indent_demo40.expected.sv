`define WRAP(x) `INNER(x)
`define DOUBLE(x) `WRAP(x)
class demo40;
  function void run();
    `WRAP(1);
    `DOUBLE(2);
    `FOO(x);
    `BAR(y);
    `CHECK(`INNER(a) == `INNER(b));
  endfunction
endclass
