module demo64(input logic a, input logic b, input logic c, output logic y, output logic z);
and u_and(y, a, b);
or u_or(z, a, b);
xor u_xor(y, a, c);
buf u_buf(z, a);
not u_not(y, a);
nand u_nand(y, a, b);
nor u_nor(z, a, b);
assign #5 y = a & b;
assign (strong0, pull1) z = a | b;
function int compute(int x, int y);
  return x + y;
endfunction
initial begin
  int r;
  r = compute(
    a,
    `ifdef USE_B
      b,
    `else
      c,
    `endif
    1
  );
  $display("%0d", r);
end
endmodule
