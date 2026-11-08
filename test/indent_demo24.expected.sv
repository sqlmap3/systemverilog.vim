class demo24;
  task check();
    if (is_tx) begin
      `MY_CHECK_EXECUTE(!is_active, (msg_code inside {8'hAA, 8'hBA}), $sformatf("msg %h", code));
      if (is_rx) begin
        `MY_CHECK_EXECUTE(!is_active, (msg_subcode inside {[8'h01:8'h04]}), $sformatf("sub %h", sub));
      end
      else begin
        `MY_CHECK_EXECUTE(`INNER_MACRO(x), (v inside {1, 2, 3}), "done");
      end
    end
  endtask
endclass
