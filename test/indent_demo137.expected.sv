module m;
function void f1();
  begin
    a = '{
      '{1, 2},
      '{3, 4}
    };
    b = 1;
    b = 2;
  end
endfunction
generate
  begin : g
    assign a = '{ '{1, 2}, '{3, 4} };
    assign b = 1;
    assign c = 2;
  end
endgenerate
function void f2();
  begin
    a = '{ '{1, 2}, '{3, 4} }
    b = 1;
    b = 2;
  end
endfunction
function void f3();
  begin
    a = '{1, 2}
    b = 1;
    b = 2;
  end
endfunction
endmodule
