module demo55(input logic a, input logic b, output logic y);
specify
specparam tpd = 5;
(a => y) = tpd;
(b => y) = tpd;
$setup(a, posedge b, 2);
$hold(posedge b, a, 1);
endspecify
and u_and(y, a, b);
endmodule
primitive udp_mux(out, sel, a, b);
output out;
input sel, a, b;
table
0 0 ? : 0;
0 1 ? : 1;
1 ? 0 : 0;
1 ? 1 : 1;
endtable
endprimitive
