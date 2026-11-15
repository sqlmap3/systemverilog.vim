module m;
initial begin
  fork
    disable /* stop */ fork;
    x = 1;
    wait /* x */ fork;
    y = 2;
    disable /* a */ /* b */ fork;
    z = 3;
    disable/* c */fork;
    w = 4;
    disable fork;
    v = 5;
    wait fork;
    u = 6;
  join_any
  t = 7;
end
initial begin
  disable /* c */ fork;
  x = 1;
  wait /* c */ fork;
  y = 2;
  disable fork;
  z = 3;
  wait fork;
  w = 4;
end
endmodule
