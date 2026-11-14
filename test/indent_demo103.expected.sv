class c;
  task t();
    y = 2;
    /* c
    more
    */ begin
      x = 1;
    end
    /* c
    more
    */ x = 2;
    if (a) begin
      /* c
    more
      */ begin
        x = 3;
      end
    end
    /* c
    more
    */ if (b) begin
      x = 4;
    end
    if (c) begin
      x = 5;
      /* c
    more
    */ end
    m1 = 1;
  endtask
endclass
