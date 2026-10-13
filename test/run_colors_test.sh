#!/bin/sh
# Colorscheme regression test: loads colors/systemverilog_uvm.vim in dark and
# light backgrounds and verifies the semantic groups get distinct colors.
#
# Usage:  sh test/run_colors_test.sh
set -u

VIM="${VIM:-vim}"
PLUGDIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
WORK=$(mktemp -d) || exit 2
trap 'rm -rf "$WORK"' EXIT

command -v "$VIM" >/dev/null 2>&1 || { echo "ERROR: Vim not found: $VIM"; exit 2; }

"$VIM" -Nu NONE -n -es \
    -c "set rtp^=$PLUGDIR" \
    -c "let g:sv_result='$WORK/result.txt'" \
    -c "source $PLUGDIR/test/colors_check.vim"

if [ ! -f "$WORK/result.txt" ]; then
    echo "ERROR: colorscheme runner produced no result"; exit 2
fi
cat "$WORK/result.txt"
head -1 "$WORK/result.txt" | grep -q '^PASS'
