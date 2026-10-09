#!/bin/sh
# Golden-file fold-level regression test for systemverilog.vim
#
# Computes the fold level of every line of test/fold_demo.sv through the
# plugin's foldexpr engine and compares against test/fold_demo.expected.txt.
#
# Usage:  sh test/run_fold_test.sh   (override Vim with VIM=nvim)
set -u

VIM="${VIM:-vim}"
PLUGDIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
WORK=$(mktemp -d) || exit 2
trap 'rm -rf "$WORK"' EXIT

command -v "$VIM" >/dev/null 2>&1 || { echo "ERROR: Vim not found: $VIM"; exit 2; }

# Levels must be collected WITHOUT modifying the buffer: mutating it
# (e.g. via setline) bumps b:changedtick on every step and invalidates the
# engine's per-tick scan cache mid-run, corrupting later lines' levels.
"$VIM" -Nu NONE -n -es \
    -c "let g:systemverilog_syntax_fold='all'" \
    -c "set rtp^=$PLUGDIR" \
    -c "filetype plugin indent on" \
    -c "e $PLUGDIR/test/fold_demo.sv" \
    -c "let g:sv_levels=map(range(1,line('\$')),'printf(\"%2d|%s\",foldlevel(v:val),getline(v:val))')" \
    -c "enew!" \
    -c "call append(0,g:sv_levels)" \
    -c "%p" \
    -c "qa!" >"$WORK/actual.raw" 2>/dev/null

# drop the stray empty line left by the scratch buffer (may hold a space)
grep -v '^[[:space:]]*$' "$WORK/actual.raw" >"$WORK/actual.txt"
grep -v '^[[:space:]]*$' "$PLUGDIR/test/fold_demo.expected.txt" >"$WORK/expected.txt"

if diff -u "$WORK/expected.txt" "$WORK/actual.txt" >"$WORK/diff.txt"; then
    echo "PASS: fold levels match expected ($(wc -l <"$WORK/actual.txt" | tr -d ' ') lines)"
    exit 0
fi

echo "FAIL: fold levels differ from expected:"
echo "----------------------------------------"
cat "$WORK/diff.txt"
echo "----------------------------------------"
echo "sample:  $PLUGDIR/test/fold_demo.sv"
echo "wanted: $PLUGDIR/test/fold_demo.expected.txt"
exit 1
