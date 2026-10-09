#!/bin/sh
# Golden-file indent regression test for systemverilog.vim
#
# Re-indents test/indent_demo.sv with gg=G in a headless Vim and compares
# the result with test/indent_demo.expected.sv. Blank-line indentation is
# ignored (the indent engine does not define it).
#
# Usage:  sh test/run_indent_test.sh        (override Vim with VIM=nvim)
set -u

VIM="${VIM:-vim}"
PLUGDIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
WORK=$(mktemp -d) || exit 2
trap 'rm -rf "$WORK"' EXIT

command -v "$VIM" >/dev/null 2>&1 || { echo "ERROR: Vim not found: $VIM"; exit 2; }

cp "$PLUGDIR/test/indent_demo.sv" "$WORK/input.sv"

# -Nu NONE  : isolated environment (no user config)
# rtp^      : put the plugin AHEAD of $VIMRUNTIME so our indent file wins
#             over the built-in indent/systemverilog.vim
"$VIM" -Nu NONE -n -es \
    -c "set rtp^=$PLUGDIR" \
    -c "filetype plugin indent on" \
    -c "e $WORK/input.sv" \
    -c "setlocal shiftwidth=2 tabstop=2 expandtab" \
    -c "normal! gg=G" \
    -c "wq" >/dev/null 2>&1

# blank-line indentation is not part of the contract
grep -v '^[[:space:]]*$' "$PLUGDIR/test/indent_demo.expected.sv" >"$WORK/expected.txt"
grep -v '^[[:space:]]*$' "$WORK/input.sv" >"$WORK/actual.txt"

if diff -u "$WORK/expected.txt" "$WORK/actual.txt" >"$WORK/diff.txt"; then
    echo "PASS: indent matches expected ($(wc -l <"$WORK/actual.txt" | tr -d ' ') lines)"
    exit 0
fi

echo "FAIL: indent differs from expected:"
echo "------------------------------------"
cat "$WORK/diff.txt"
echo "------------------------------------"
echo "input:  $PLUGDIR/test/indent_demo.sv"
echo "wanted: $PLUGDIR/test/indent_demo.expected.sv"
exit 1
