class demo77;
  extern function void configure(int mode, string name = "default", bit enable = 1);
  extern virtual function int compute(input int a, input int b = 0, output int c);
  function void demo77::configure(int mode, string name = "default", bit enable = 1);
    if (enable) begin
      $display("mode=%0d name=%s", mode, name);
    end
  endfunction
  function int demo77::compute(input int a, input int b = 0, output int c);
    c = a + b;
    return c;
  endfunction
  task automatic run_task(
                          input int count,
                          ref int result[4],
                          output bit done
  );
    foreach (result[i]) begin
      result[i] = count + i;
    end
    done = 1;
  endtask
endclass
