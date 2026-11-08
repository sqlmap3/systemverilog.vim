class demo44;
rand int val;
sequence s1;
a ##1 b;
endsequence
property p1;
@(posedge clk) a |-> b;
endproperty
function void run();
randsequence(main)
main: first second;
first: {val++;} ;
second: {val--;} ;
endsequence
endfunction
endclass
