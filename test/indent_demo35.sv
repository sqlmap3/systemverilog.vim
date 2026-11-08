class demo35;
function void run();
`MY_CHECK(!is_active,
(msg_code inside {8'hAA, 8'hBA}),
$sformatf("msg %h", code));
if (is_rx) begin
`MY_CHECK(!is_active,
(msg_subcode inside {[8'h01:8'h04]}),
$sformatf("sub %h", sub));
end
endfunction
endclass
