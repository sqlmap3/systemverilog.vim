class c;
  task t();
    begin /* open
    more
*/
      x = 1;
    end
    if (a) begin
      x = 2;
    end /* open
    more
*/
    m1 = 1;
    if (b)
      y = 3; /* open
    more
*/
    m2 = 1;
    if (c) /* open
    more
*/
      x = 4;
    m3 = 1;
  endtask
  function void f() /* open
    more
*/
    x = 5;
  endfunction
endclass
