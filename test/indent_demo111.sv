`define PRINT_INT(F) \
      begin \
max__ = $right(F)+1; \
// max__=$size(F); \
p__.print_array_header(F, max__); \
k__ = p__.knobs; \
if((p__.knobs.depth == -1)) \
begin \
  foreach(F[i__]) begin \
    if(k__.begin_elements == -1) begin \
      `PRINT_ELEM(F[curr]) \
    end \
    else break; \
    curr++; \
  end \
end \
p__.print_array_footer(max__); \
      end
x = 1;
