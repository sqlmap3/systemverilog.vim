class demo57_base;
  int base_val;
  function new();
    base_val = 0;
  endfunction
endclass
class demo57 extends demo57_base;
  static int instance_count = 0;
  static function int get_count();
    return instance_count;
  endfunction
  mailbox mbx;
  semaphore sem;
  process proc_h;
  function new();
    super.new();
    mbx = new();
    sem = new(1);
    instance_count++;
  endfunction
  task run();
    fork
      begin
        mbx.put(1);
      end
      begin
        int v;
        mbx.get(v);
      end
    join
    sem.get(1);
    sem.put(1);
    proc_h = process::self();
  endtask
endclass
