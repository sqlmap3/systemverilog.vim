#!/bin/sh
# Indent idempotency regression test for systemverilog.vim over the real
# UVM 1.2 library sources.
#
# For every file under test: re-indent with gg=G twice; the second pass must
# not change anything, no line may exceed 40 columns of indent (runaway),
# and the indent engine must not raise. The first pass normalizes to the
# engine's own style, so the library's original formatting is irrelevant -
# only the stability of the engine is asserted.
#
# By default a curated set of representative files is checked (the macro
# heavy defines plus the largest/most complex classes) so the run stays
# under a couple of minutes. Set UVM_SRC to a directory to check every
# .svh/.sv under it instead (slow: ~10 minutes for the full tree).
#
# Usage:  sh test/run_uvm_indent_test.sh
#         VIM=nvim sh test/run_uvm_indent_test.sh          (other Vim)
#         UVM_SRC=/path/to/uvm-1.2/src sh ...              (full tree)
set -u

VIM="${VIM:-vim}"
PLUGDIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
UVM_ROOT="${UVM_ROOT-$HOME/test/uvm-1.2/src}"
WORK=$(mktemp -d) || exit 2
trap 'rm -rf "$WORK"' EXIT

command -v "$VIM" >/dev/null 2>&1 || { echo "ERROR: Vim not found: $VIM"; exit 2; }

# curated representative subset: the macro-heavy defines (nested if/begin/end,
# macro-calling-macro) plus a few classes. The very large files are omitted
# from the default run - the indent engine walks back through comment and
# backslash-continuation blocks on every line, so re-indenting a 3k+ line
# macro file takes minutes (known performance limitation). Set UVM_SRC to a
# directory to check everything instead.
SUBSET="
macros/uvm_message_defines.svh
macros/uvm_sequence_defines.svh
macros/uvm_reg_defines.svh
macros/uvm_phase_defines.svh
macros/uvm_callback_defines.svh
macros/uvm_version_defines.svh
macros/uvm_deprecated_defines.svh
macros/uvm_global_defines.svh
seq/uvm_sequence.svh
comps/uvm_driver.svh
dap/uvm_set_get_dap_base.svh
"

if [ -n "${UVM_SRC:-}" ]; then
    if [ ! -d "$UVM_SRC" ]; then
        echo "SKIP: UVM_SRC not a directory ($UVM_SRC)"
        exit 0
    fi
    find "$UVM_SRC" \( -name '*.svh' -o -name '*.sv' \) >"$WORK/files.txt"
else
    for f in $SUBSET; do
        [ -f "$UVM_ROOT/$f" ] && printf '%s\n' "$UVM_ROOT/$f"
    done >"$WORK/files.txt"
fi

if [ ! -s "$WORK/files.txt" ]; then
    echo "SKIP: no UVM sources found (set UVM_SRC=/path/to/uvm-1.2/src, or UVM_ROOT=)"
    exit 0
fi

"$VIM" -Nu NONE -n -es \
    -c "set rtp^=$PLUGDIR" \
    -c "filetype plugin indent on" \
    -c "let g:sv_files_list='$WORK/files.txt'" \
    -c "let g:sv_result='$WORK/result.txt'" \
    -c "source $PLUGDIR/test/uvm_indent_idem.vim"

if [ ! -f "$WORK/result.txt" ]; then
    echo "ERROR: indent idempotency runner produced no result"
    exit 2
fi
cat "$WORK/result.txt"
if head -1 "$WORK/result.txt" | grep -q '^PASS'; then
    exit 0
fi
exit 1
