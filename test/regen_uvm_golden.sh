#!/bin/sh
# Regenerate the UVM indent golden snapshot (test/uvm_golden/) after an
# INTENDED change to the indent engine. Re-indents every .svh/.sv under
# UVM_SRC (default ~/test/uvm-1.2/src) and writes the result into the
# golden tree. Review the diff before committing it.
set -u

VIM="${VIM:-vim}"
PLUGDIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
UVM_ROOT="${UVM_ROOT-$HOME/test/uvm-1.2/src}"
GOLDEN="$PLUGDIR/test/uvm_golden"
WORK=$(mktemp -d) || exit 2
trap 'rm -rf "$WORK"' EXIT

command -v "$VIM" >/dev/null 2>&1 || { echo "ERROR: Vim not found: $VIM"; exit 2; }

if [ -n "${UVM_SRC:-}" ]; then
    [ -d "$UVM_SRC" ] || { echo "ERROR: UVM_SRC not a directory ($UVM_SRC)"; exit 2; }
    SRCROOT="$UVM_SRC"
else
    SRCROOT="$UVM_ROOT"
    [ -d "$SRCROOT" ] || { echo "ERROR: no UVM sources (set UVM_SRC=...)"; exit 2; }
fi

find "$SRCROOT" \( -name '*.svh' -o -name '*.sv' \) >"$WORK/files.txt"

# re-indent every file directly into the golden tree
"$VIM" -Nu NONE -n -es \
    -c "set rtp^=$PLUGDIR" \
    -c "filetype plugin indent on" \
    -c "let g:sv_files_list='$WORK/files.txt'" \
    -c "let g:sv_srcroot='$SRCROOT'" \
    -c "let g:sv_outdir='$GOLDEN'" \
    -c "source $PLUGDIR/test/uvm_golden_indent.vim"

echo "regenerated $(find "$GOLDEN" -type f -name '*.svh' -o -name '*.sv' | wc -l | tr -d ' ') golden files"
echo "review 'git diff test/uvm_golden' before committing"
