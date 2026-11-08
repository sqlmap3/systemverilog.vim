module demo67(input logic [3:0] sel, input logic [7:0] data, output logic [7:0] o1, output logic [7:0] o2, output logic [7:0] o3, output logic [7:0] o4);
logic [7:0] tmp;
always_comb begin
unique case (sel)
4'b0001: tmp = data;
4'b0010: tmp = {2{data[3:0]}};
4'b0100: tmp = data[7:4];
default: tmp = '0;
endcase
end
always_comb begin
priority casez (sel)
4'b1???: o1 = tmp;
4'b01??: o1 = data;
default: o1 = '0;
endcase
end
always_comb begin
casex (sel)
4'bxx01: o2 = data[3:0];
default: o2 = tmp;
endcase
end
assign o3 = (sel[0]) ? data[7:4] : (sel[1]) ? data[3:0] : '0;
assign o4 = data[sel[1] +: 4];
endmodule
