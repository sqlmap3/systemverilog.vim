module m;
function void f1();
  begin
    x = '{ '{1, 2}, '{3, 4} };
    b = 1;
    b = 2;
  end
endfunction
function void f2();
  begin
    a = '{ '{1, 2} };
    b = 1;
    b = 2;
  end
endfunction
function void f3();
  begin
    a='{'{1,2},'{3,4}};
    b = 1;
    b = 2;
  end
endfunction
function void f4();
  begin
    a = '{ '{ '{1, 2}, '{3, 4} }, '{5, 6} };
    b = 1;
    b = 2;
  end
endfunction
endmodule
