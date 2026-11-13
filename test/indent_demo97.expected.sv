class c;
  task t1();
    x = 1;
    if (a1) begin b1 = 1; end
    m1 = 1;
    if (a2) begin b2 = 2; end
    m2 = 2;
    while (w) begin d = 1; end
    m3 = 3;
    for (i = 0; i < 3; i++) begin e = 1; end
    m4 = 4;
    foreach (arr[i]) begin f = 1; end
    m5 = 5;
    if (a) begin b = 1; end else begin c = 2; end
    m6 = 6;
    if (a) begin b = 1; end else if (c) begin d = 2; end
    m7 = 7;
    if (q) begin
      z = 1;
    end else begin g = 1; end
    m8 = 8;
  endtask
  task t2();
    x = 1;
    if (q) begin
      z = 1;
    end
    m1 = 1;
    if (r) s = 1;
    m2 = 2;
    if (a) begin foo();
      y = 2;
    end
    m3 = 3;
    begin g = 1; end
    m4 = 4;
    if (a) begin b = 1; end else
      h = 1;
    m5 = 5;
  endtask
  task t3();
    x = 1;
    case (sel)
      0: begin a = 1; end
      1: begin b = 2; end
    endcase
    m1 = 1;
    if (a) fork j = 1; join
    m2 = 2;
    if (a) case (s) 0: k = 1; default: k = 2; endcase
    m3 = 3;
    if (a) begin $display("end"); end
    m5 = 5;
    if (a) begin b = 1; end // trailing end word
    m6 = 6;
  endtask
endclass
