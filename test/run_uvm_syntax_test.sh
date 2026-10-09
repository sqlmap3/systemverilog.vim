#!/bin/sh
# Syntax regression test for systemverilog.vim against UVM 1.2 constructs.
#
# Part 1 (self-contained): verifies that representative tokens in
# test/uvm_syntax_spot.sv -- constructs lifted from the UVM 1.2 library
# (uvm-1.2/src) -- get the expected highlight, using search()+synID so the
# expectations survive edits to the sample.
#
# Part 2 (optional): loads every .sv/.svh of a real UVM 1.2 source tree and
# fails if any file errors out or does not get the systemverilog
# filetype/syntax applied.
#
# Usage:  sh test/run_uvm_syntax_test.sh
#         VIM=nvim sh test/run_uvm_syntax_test.sh          (other Vim)
#         UVM_SRC=/path/to/uvm-1.2/src sh ...              (other library)
#         UVM_SRC= sh ...                                  (skip part 2)
#
# NOTE: "vim -es" (silent ex) suppresses :echo, so the Vim-side runners
# write their results to files which this wrapper prints.
set -u

VIM="${VIM:-vim}"
PLUGDIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
WORK=$(mktemp -d) || exit 2
trap 'rm -rf "$WORK"' EXIT

command -v "$VIM" >/dev/null 2>&1 || { echo "ERROR: Vim not found: $VIM"; exit 2; }

rc=0

# part 1: syntax spot checks on the bundled sample
"$VIM" -Nu NONE -n -es \
    -c "set rtp^=$PLUGDIR" \
    -c "syntax on" \
    -c "filetype plugin indent on" \
    -c "let g:sv_checks_file='$PLUGDIR/test/uvm_syntax_checks.txt'" \
    -c "let g:sv_result='$WORK/spot.txt'" \
    -c "edit $PLUGDIR/test/uvm_syntax_spot.sv" \
    -c "source $PLUGDIR/test/uvm_syntax_check.vim"
if [ ! -f "$WORK/spot.txt" ]; then
    echo "ERROR: spot-check runner produced no result"; rc=2
else
    cat "$WORK/spot.txt"
    head -1 "$WORK/spot.txt" | grep -q '^PASS' || rc=1
fi

# part 2: smoke-load the real UVM 1.2 library
UVM_SRC="${UVM_SRC-$HOME/test/uvm-1.2/src}"
if [ -z "$UVM_SRC" ]; then
    echo "SKIP: UVM_SRC empty - smoke test over the library not run"
elif [ ! -d "$UVM_SRC" ]; then
    echo "SKIP: UVM source tree not found ($UVM_SRC) - smoke test not run"
else
    "$VIM" -Nu NONE -n -es \
        -c "set rtp^=$PLUGDIR" \
        -c "syntax on" \
        -c "filetype plugin indent on" \
        -c "let g:uvm_src='$UVM_SRC'" \
        -c "let g:sv_result='$WORK/smoke.txt'" \
        -c "source $PLUGDIR/test/uvm_syntax_smoke.vim"
    if [ ! -f "$WORK/smoke.txt" ]; then
        echo "ERROR: smoke-test runner produced no result"; [ "$rc" -eq 0 ] && rc=2
    else
        cat "$WORK/smoke.txt"
        if head -1 "$WORK/smoke.txt" | grep -q '^FAIL'; then [ "$rc" -eq 0 ] && rc=1; fi
    fi
fi

exit $rc
