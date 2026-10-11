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
# .svh/.sv under it instead (run in NPAR parallel chunks, see below).
#
# Usage:  sh test/run_uvm_indent_test.sh
#         VIM=nvim sh test/run_uvm_indent_test.sh          (other Vim)
#         UVM_SRC=/path/to/uvm-1.2/src sh ...              (full tree)
#         NPAR=8 sh ...                                    (more parallelism)
set -u

VIM="${VIM:-vim}"
NPAR="${NPAR:-4}"
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

# distribute the files over NPAR chunks, largest first round-robin, so one
# chunk does not end up with all the multi-thousand-line files while the
# others idle (find output groups big directories together). -1 forces one
# path per line even though ls goes to a pipe.
ls -1S $(cat "$WORK/files.txt") | awk -v n="$NPAR" -v d="$WORK" '
    { f = sprintf("%s/c%d", d, (NR - 1) % n); print >> f; close(f) }'

# run the chunks in parallel: each vim instance re-indents its chunk twice
pids=""
for chunk in "$WORK"/c*; do
    [ -e "$chunk" ] || continue
    "$VIM" -Nu NONE -n -es \
        -c "set rtp^=$PLUGDIR" \
        -c "filetype plugin indent on" \
        -c "let g:sv_files_list='$chunk'" \
        -c "let g:sv_result='$chunk.res'" \
        -c "source $PLUGDIR/test/uvm_indent_idem.vim" &
    pids="$pids $!"
done
wait $pids

# merge results
rc=0
total=0
for res in "$WORK"/c*.res; do
    [ -e "$res" ] || { echo "ERROR: a chunk produced no result"; rc=2; continue; }
    if ! head -1 "$res" | grep -q '^PASS'; then
        rc=1
        cat "$res"
    else
        n=$(sed -n 's/^PASS.*over \([0-9][0-9]*\) UVM files.*/\1/p' "$res")
        total=$((total + ${n:-0}))
    fi
done

if [ "$rc" -eq 0 ]; then
    echo "PASS: indent idempotency over $total UVM files"
fi
exit $rc
