class demo46;
  rand int val;
  rand int arr[];
  constraint c_val {
    solve val before arr;
    soft val inside {[0:100]};
    val dist {0:=1, [1:10]:/2};
  }
  function void run();
    foreach (arr[i]) begin
      arr[i] = i;
    end
    do begin
      val++;
    end while (val < 10);
  endfunction
endclass
