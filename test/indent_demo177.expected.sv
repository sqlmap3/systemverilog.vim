// indent regression demo 177: randsequence productions whose action
// braces the gate rescues but the tail-drop rule eats, fixed by
// stripping both braces of each rescued pair, round 18. One, two
// and three productions, the F1s/F1s2 no-begin variants, the
// demo44/demo12 spellings, and the RQ3b/RQ10 nested and two-pair
// tails.
// Keep in sync with indent_demo177.expected.sv.

class c;
  function void run();
    randsequence(main)
      main: first second;
      first: { begin a = 1; end };
      second: {c = 3;};
    endsequence
  endfunction
endclass

class c;
  function void run();
    randsequence(main)
      main: first;
      first: { begin a = 1; end };
    endsequence
  endfunction
endclass

class c;
  function void run();
    randsequence(main)
      main: first second;
      first: {a = 1; b = 2};
      second: {c = 3;};
    endsequence
  endfunction
endclass

class c;
  function void run();
    randsequence(main)
      main: first second third;
      first: {v = 1;};
      second: {a = 1; b = 2};
      third: {w = 2;};
    endsequence
  endfunction
endclass

class c;
  function void run();
    randsequence(main)
      main: first second;
      first: {val++;} ;
      second: {val--;} ;
    endsequence
  endfunction
endclass

class c;
  task automatic do_randseq();
    randsequence (main)
      main : first second;
      first : { $display("first"); };
      second : { $display("second"); };
    endsequence
  endtask
endclass

begin
  first: { begin a = 1; b = {c, d}; end };
  z = 1;
end

begin
  first: { begin a = 1; end }; second: { begin b = 2; end };
  z = 1;
end
