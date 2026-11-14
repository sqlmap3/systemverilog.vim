`define FIELD_UTILS_END \
      if(what__ inside {UVM_SETINT}) begin \
// remove all scopes recorded \
void'(scopes.pop_back()); \
status.container = scopes; \
      end \
    end \
endfunction \
// MACRO: `OBJ_UTILS
// MACRO: `OBJ_PARAM_UTILS
// MACRO: `OBJ_UTILS_BEGIN
`define OBJ_UTILS(TYPE) \
      class utils_``TYPE; \
function void f(); \
endfunction \
      endclass
// MACRO: `OBJ_UTILS2
// MACRO: `OBJ_PARAM_UTILS2
y = 2;
