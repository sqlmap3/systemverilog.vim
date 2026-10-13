#!/bin/sh
# Golden snapshot test for systemverilog.vim over the real UVM 1.2 library.
#
# Re-indents every .svh/.sv under UVM_SRC and requires byte-identical output
# to test/uvm_golden/ (the engine's canonical formatting for
# gchinna/uvm-1.2 @ a3cb911). Stricter than run_uvm_indent_test.sh: any
# change to the engine's formatting fails, even a stable-but-different one.
#
# Usage:  sh test/run_uvm_golden_test.sh
#         UVM_SRC=/path/to/uvm-1.2/src sh ...   (override the source tree)
#         NPAR=8 sh ...                          (more parallelism)
set -u

VIM="${VIM:-vim}"
NPAR="${NPAR:-4}"
PLUGDIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
UVM_ROOT="${UVM_ROOT-$HOME/test/uvm-1.2/src}"
GOLDEN="$PLUGDIR/test/uvm_golden"
WORK=$(mktemp -d) || exit 2
trap 'rm -rf "$WORK"' EXIT

command -v "$VIM" >/dev/null 2>&1 || { echo "ERROR: Vim not found: $VIM"; exit 2; }

if [ -n "${UVM_SRC:-}" ]; then
    if [ ! -d "$UVM_SRC" ]; then
        echo "SKIP: UVM_SRC not a directory ($UVM_SRC)"
        exit 0
    fi
    find "$UVM_SRC" \( -name '*.svh' -o -name '*.sv' \) >"$WORK/files.txt"
else
    find "$UVM_ROOT" \( -name '*.svh' -o -name '*.sv' \) >"$WORK/files.txt"
fi

if [ ! -s "$WORK/files.txt" ]; then
    echo "SKIP: no UVM sources found (set UVM_SRC=/path/to/uvm-1.2/src)"
    exit 0
fi

# distribute files over NPAR chunks, largest first round-robin
ls -1S $(cat "$WORK/files.txt") | awk -v n="$NPAR" -v d="$WORK" '
    { f = sprintf("%s/c%d", d, (NR - 1) % n); print >> f; close(f) }'

# re-indent each chunk into $WORK/out, preserving relative paths
pids=""
for chunk in "$WORK"/c*; do
    [ -e "$chunk" ] || continue
    "$VIM" -Nu NONE -n -es \
        -c "set rtp^=$PLUGDIR" \
        -c "filetype plugin indent on" \
        -c "let g:sv_files_list='$chunk'" \
        -c "let g:sv_srcroot='${UVM_SRC:-$UVM_ROOT}'" \
        -c "let g:sv_outdir='$WORK/out'" \
        -c "source $PLUGDIR/test/uvm_golden_indent.vim" &
    pids="$pids $!"
done
wait $pids

# diff against the committed golden snapshot
rc=0
total=0
while IFS= read -r f; do
    rel="${f#${UVM_SRC:-$UVM_ROOT}/}"
    out="$WORK/out/$rel"
    g="$GOLDEN/$rel"
    if [ ! -f "$g" ]; then
        echo "FAIL: no golden snapshot for $rel"
        rc=1
        continue
    fi
    total=$((total + 1))
    if ! cmp -s "$out" "$g"; then
        echo "FAIL: $rel"
        diff -u "$g" "$out" | head -40
        echo
        rc=1
    fi
done <"$WORK/files.txt"

if [ "$rc" -eq 0 ]; then
    echo "PASS: golden snapshot matches over $total UVM files"
fi
exit $rc
