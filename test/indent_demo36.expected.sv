class demo36;
  function void run();
    `OUTER(`MIDDLE(`INNER(x)), y);
    `OUTER(`MIDDLE(a), `MIDDLE(b));
    foo(`BAR(x), `BAZ(y));
    `CHECK(`GET_VAL(a) == `EXPECTED(b), "mismatch");
  endfunction
endclass
