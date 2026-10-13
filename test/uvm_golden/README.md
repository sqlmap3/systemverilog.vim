# UVM indent golden snapshot

These are the indent engine's canonical `gg=G` output (shiftwidth=2) for
every `.svh`/`.sv` under the UVM 1.2 reference library:

  https://github.com/gchinna/uvm-1.2  (commit a3cb911)

`run_uvm_golden_test.sh` re-indents the local UVM source tree and requires
byte-identical output. It is stricter than the idempotency test: any change
to the engine's formatting - including a stable-but-different one - fails,
so a regression is caught before it ships.

To regenerate after an INTENDED change to the indent engine:

  sh test/regen_uvm_golden.sh
