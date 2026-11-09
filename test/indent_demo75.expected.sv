package demo75_pkg;
typedef struct packed {
  logic [3:0] op;
  logic [7:0] addr;
  logic [31:0] data;
} pkt_hdr_t;
typedef union packed {
  logic [47:0] raw;
  pkt_hdr_t hdr;
} pkt_t;
typedef enum logic [1:0] {
  IDLE = 2'b00,
  BUSY = 2'b01,
  DONE = 2'b10
} state_t;
typedef struct {
  int x;
  int y;
  string name;
} point_t;
endpackage
class demo75_base;
  virtual function void run();
  endfunction
  pure virtual function int get_id();
endclass
class demo75_child extends demo75_base;
  local int id;
  protected string label;
  static int count;
  function new(int i);
    id = i;
    count++;
  endfunction
  function int get_id();
    return id;
  endfunction
endclass
