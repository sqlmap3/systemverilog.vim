#!/bin/sh
# Golden-file indent regression tests for systemverilog.vim
#
# Re-indents each test/indent_demo*.sv with gg=G in a headless Vim and
# compares the result with the matching test/indent_demo*.expected.sv.
# Blank-line indentation is ignored (the indent engine does not define it).
#
#   indent_demo.sv   core constructs (case labels, macros, ifdef, define...)
#   indent_demo2.sv  uvm_component::new constructs (bare begin blocks,
#                    multi-line calls under if, concatenations, macros)
#
# To regenerate an expected file after an INTENDED behavior change:
#   vim -Nu NONE -n -es -c "set rtp^=$(dirname $0)/.." \
#     -c "filetype plugin indent on" -c "edit test/indent_demo2.sv" \
#     -c "setlocal shiftwidth=2 tabstop=2 expandtab" -c "normal! gg=G" \
#     -c "w! test/indent_demo2.expected.sv" -c "qa!"
#
# Usage:  sh test/run_indent_test.sh        (override Vim with VIM=nvim)
set -u

VIM="${VIM:-vim}"
PLUGDIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
WORK=$(mktemp -d) || exit 2
trap 'rm -rf "$WORK"' EXIT

command -v "$VIM" >/dev/null 2>&1 || { echo "ERROR: Vim not found: $VIM"; exit 2; }

rc=0
for demo in "$PLUGDIR"/test/indent_demo*.sv; do
    [ -e "$demo" ] || continue
    name=$(basename "$demo")
    case "$name" in *.expected.sv) continue ;; esac
    expected="$PLUGDIR/test/${name%.sv}.expected.sv"
    [ -e "$expected" ] || { echo "SKIP: no expected file for $name"; continue; }

    cp "$demo" "$WORK/input.sv"

    "$VIM" -Nu NONE -n -es \
        -c "set rtp^=$PLUGDIR" \
        -c "filetype plugin indent on" \
        -c "e $WORK/input.sv" \
        -c "setlocal shiftwidth=2 tabstop=2 expandtab" \
        -c "normal! gg=G" \
        -c "wq" >/dev/null 2>&1

    grep -v '^[[:space:]]*$' "$expected" >"$WORK/expected.txt"
    grep -v '^[[:space:]]*$' "$WORK/input.sv" >"$WORK/actual.txt"

    if diff -u "$WORK/expected.txt" "$WORK/actual.txt" >"$WORK/diff.txt"; then
        echo "PASS: $name indent matches expected ($(wc -l <"$WORK/actual.txt" | tr -d ' ') lines)"
    else
        echo "FAIL: $name indent differs from expected:"
        echo "------------------------------------"
        cat "$WORK/diff.txt"
        echo "------------------------------------"
        echo "input:  $demo"
        echo "wanted: $expected"
        rc=1
    fi
done

exit $rc
