module demo48;
import "DPI-C" function void dpi_print(input string msg);
import "DPI-C" function int dpi_compute(input int a, input int b);
import "DPI-C" context function void dpi_context_call();
export "DPI-C" function sv_callback;
function void sv_callback(input int val);
$display("callback %0d", val);
endfunction
initial begin
dpi_print("hello");
$display("%0d", dpi_compute(1, 2));
end
endmodule
