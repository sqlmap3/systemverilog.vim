module demo76 #(parameter WIDTH = 8, parameter DEPTH = 4) (
  input logic clk,
  input logic [WIDTH-1:0] din,
  output logic [WIDTH-1:0] dout
);
genvar g;
generate
  for (g = 0; g < DEPTH; g++) begin : gen_stage
    logic [WIDTH-1:0] stage_data;
    always_ff @(posedge clk) begin
      if (g == 0)
        stage_data <= din;
      else
        stage_data <= gen_stage[g-1].stage_data;
    end
  end
  if (DEPTH > 1) begin : gen_out
    assign dout = gen_stage[DEPTH-1].stage_data;
  end else begin : gen_bypass
    assign dout = din;
  end
  case (WIDTH)
    8: begin : gen_w8
      assign dout[7:0] = din[7:0];
    end
    16: begin : gen_w16
      assign dout[15:0] = din[15:0];
    end
    default: begin : gen_wd
      assign dout = '0;
    end
  endcase
endgenerate
endmodule
