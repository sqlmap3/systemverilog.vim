typedef enum logic [1:0] {
IDLE,
`ifdef HAS_WAIT
WAIT,
`endif
BUSY,
DONE
} state_t;
typedef struct packed {
logic [7:0] data;
`ifdef HAS_PARITY
logic parity;
`endif
logic valid;
} pkt_t;
typedef union tagged {
int int_val;
logic [31:0] bits;
} tagged_u;
class demo49;
state_t cur;
pkt_t pkt;
function void run();
cur = IDLE;
endfunction
endclass
