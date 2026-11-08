class demo39;
  function int get_val();
    return `GET_VAL(x);
  endfunction
  function void run(int sel);
    out_val = `COMPUTE(a, b);
    case (sel)
      0: `DO_A();
      1: `DO_B();
      default: `DO_DEFAULT();
    endcase
    `CHECK(a ? `VAL_B : `VAL_C);
  endfunction
endclass
