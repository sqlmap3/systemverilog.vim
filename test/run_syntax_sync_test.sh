#!/bin/sh
# Syntax sync regression test for systemverilog.vim.
#
# Verifies that jumping into the middle of a long region (block comment,
# backslash-continued `define, instantiation statement) highlights the
# same as parsing from the start of the file. Without a `syntax sync'
# line the jump-into-middle state desyncs: code inside a long comment
# is highlighted as code, define bodies lose svDefine, and instance
# ports lose their enclosing svInstStmt.
#
# Method (from the round-16 probe-D harness): two generated fixtures
# with long regions are probed with a FRESH vim per probe -- one run in
# jump mode (no sync command at all, cursor moved to the probe) and one
# in fromstart mode (`syntax sync fromstart`, the ground truth). Each
# probe compares the raw group, the translated group, and the full
# synstack; the stack matters (instance ports keep their leaf group
# but lose svInstStmt when desynced). No hardcoded expectations: jump
# must equal fromstart within the plugin under test, so the gate also
# fails on a plugin with no sync line at all (negative control).
#
# Fixture 1 (437 lines): comment 21..271, define 280..350, inst 360..431.
# Fixture 2 (1167 lines): comment 21..531, define 540..845, inst 855..1161,
# with probes up to 499 lines into a region.
#
# Usage:  sh test/run_syntax_sync_test.sh
#         VIM=nvim sh test/run_syntax_sync_test.sh          (other Vim)
#
# NOTE: "vim -es" (silent ex) suppresses :echo, so the comparison
# writes its verdict to a file which this wrapper prints.
set -u

VIM="${VIM:-vim}"
PLUGDIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
WORK=$(mktemp -d) || exit 2
trap 'rm -rf "$WORK"' EXIT

command -v "$VIM" >/dev/null 2>&1 || { echo "ERROR: Vim not found: $VIM"; exit 2; }
command -v python3 >/dev/null 2>&1 || { echo "ERROR: python3 not found"; exit 2; }

# --- step 1: generate both fixtures + probe lists (columns computed) ---
if ! python3 - "$WORK" >"$WORK/gen.log" 2>&1 <<'PYGEN_EOF'
import os
import sys

BASE = sys.argv[1]
BS = chr(92)  # backslash; continuation lines must end with exactly this

# ---- fixture 1: probe.sv, 437 lines ----
lines = []
lines.append("// probe file for syntax sync desync test")          # 1
lines.append("`timescale 1ns/1ps")                                 # 2
lines.append("")                                                    # 3
lines.append("module tb;")                                          # 4
lines.append("  logic clk;")                                        # 5
lines.append("  logic rst_n;")                                      # 6
lines.append("  logic [7:0] data_in;")                              # 7
lines.append("  logic [7:0] data_out;")                             # 8
lines.append("  initial begin")                                     # 9
lines.append("    clk = 1'b0;")                                     # 10
lines.append("  end")                                               # 11
lines.append("  always #5 clk = ~clk;")                             # 12
for i in range(7):                                                  # 13..19
    lines.append("  logic filler_%d;" % i)
lines.append("")                                                    # 20
lines.append("  /* BEGIN LONG BLOCK COMMENT")                       # 21
for ln in range(22, 260):                                           # 22..259
    lines.append("   comment filler line %d describing signal behavior and reset values" % ln)
lines.append("   module fake_mod; begin end endmodule")             # 260 probe A1
for ln in range(261, 271):                                          # 261..270
    lines.append("   comment filler line %d describing signal behavior and reset values" % ln)
lines.append("   END OF LONG BLOCK COMMENT */")                    # 271
lines.append("")                                                    # 272
lines.append("  logic [7:0] post_data;")                            # 273 probe A3
for i in range(6):                                                  # 274..279
    lines.append("  logic post_filler_%d;" % i)
lines.append("`define LONG_MACRO(a, b) ((a) + (b) + " + BS)         # 280
for ln in range(281, 345):                                          # 281..344
    lines.append("    (VALUE_%d * 3) + " % ln + BS)
lines.append("    (`INNER_MACRO + \"probe string\") + " + BS)       # 345 probes D1a/D1b/D1c
for ln in range(346, 350):                                          # 346..349
    lines.append("    (VALUE_%d * 3) + " % ln + BS)
lines.append("    (LAST_TERM))")                                    # 350 no backslash
lines.append("")                                                    # 351
lines.append("  logic [7:0] mid_data;")                             # 352 probe D3
for i in range(6):                                                  # 353..358
    lines.append("  logic mid_filler_%d;" % i)
lines.append("")                                                    # 359
lines.append("  my_module #(.WIDTH(32), .DEPTH(16)) u_dut (")       # 360
for i in range(64):                                                 # 361..424
    lines.append("    .port_%d (sig_%d)," % (i, i))
lines.append("    .probe_port (probe_sig),")                        # 425 probe I1
for i in range(4):                                                  # 426..429
    lines.append("    .tail_%d (tail_sig_%d)," % (i, i))
lines.append("    .last_port (last_sig)")                           # 430
lines.append("  );")                                                # 431
lines.append("  logic [7:0] tail_data;")                            # 432 probe I3
lines.append("  initial begin")                                     # 433
lines.append("    data_in = 8'h00;")                                # 434
lines.append("  end")                                               # 435
lines.append("endmodule")                                           # 436
lines.append("// end of probe file")                                # 437

assert len(lines) == 437, len(lines)
assert lines[20].lstrip().startswith("/*"), lines[20]
assert lines[259].strip().startswith("module"), lines[259]
assert lines[270].rstrip().endswith("*/"), lines[270]
assert lines[279].endswith(BS) and not lines[279].endswith(" " + BS + " "), repr(lines[279])
assert lines[344].endswith(BS), repr(lines[344])
assert not lines[349].endswith(BS), repr(lines[349])
assert "u_dut (" in lines[359], lines[359]
assert lines[430] == "  );", repr(lines[430])
for ln in list(range(281, 345)) + list(range(346, 350)):
    assert lines[ln - 1].endswith(BS), (ln, repr(lines[ln - 1]))
    assert lines[ln - 1][-2] == " ", (ln, repr(lines[ln - 1]))

def col1(ln, needle):
    return lines[ln - 1].index(needle) + 1

d1c_col = lines[344].rindex("+") + 1
assert lines[344][d1c_col - 1] == "+", (lines[344], d1c_col)
assert lines[344].rindex(")") < d1c_col - 1, lines[344]

probes1 = [
    ("A2", 30, col1(30, "comment")),
    ("A1", 260, col1(260, "module")),
    ("A3", 273, col1(273, "logic")),
    ("D2", 285, col1(285, "VALUE_285")),
    ("D1a", 345, col1(345, "`")),
    ("D1b", 345, col1(345, '"')),
    ("D3", 352, col1(352, "logic")),
    ("I2", 365, col1(365, "port_4")),
    ("I1", 425, col1(425, "probe_port")),
    ("I3", 432, col1(432, "logic")),
    ("D1c", 345, d1c_col),
]

with open(os.path.join(BASE, "probe.sv"), "w") as f:
    f.write("\n".join(lines) + "\n")
with open(os.path.join(BASE, "probes.txt"), "w") as f:
    for label, ln, co in probes1:
        f.write("%s %d %d\n" % (label, ln, co))

# ---- fixture 2: probe2.sv, 1167 lines ----
lines = []
lines.append("// probe2 file: very long regions for minlines discrimination")  # 1
lines.append("`timescale 1ns/1ps")                                             # 2
lines.append("")                                                                # 3
lines.append("module tb2;")                                                     # 4
lines.append("  logic clk;")                                                    # 5
lines.append("  logic rst_n;")                                                  # 6
lines.append("  logic [7:0] data_in;")                                          # 7
lines.append("  logic [7:0] data_out;")                                         # 8
lines.append("  initial begin")                                                 # 9
lines.append("    clk = 1'b0;")                                                 # 10
lines.append("  end")                                                           # 11
lines.append("  always #5 clk = ~clk;")                                         # 12
for i in range(7):                                                              # 13..19
    lines.append("  logic filler_%d;" % i)
lines.append("")                                                                # 20
lines.append("  /* BEGIN VERY LONG BLOCK COMMENT")                             # 21
for ln in range(22, 520):                                                       # 22..519
    lines.append("   comment filler line %d describing signal behavior and reset values" % ln)
lines.append("   module deep_fake; begin end endmodule")                        # 520 probe B1
for ln in range(521, 531):                                                      # 521..530
    lines.append("   comment filler line %d describing signal behavior and reset values" % ln)
lines.append("   END VERY LONG BLOCK COMMENT */")                              # 531
lines.append("")                                                                # 532
lines.append("  logic [7:0] post2_data;")                                      # 533 probe B3
for i in range(6):                                                              # 534..539
    lines.append("  logic post2_filler_%d;" % i)
lines.append("`define HUGE_MACRO(a, b) ((a) + (b) + " + BS)                    # 540
for ln in range(541, 840):                                                      # 541..839
    lines.append("    (VALUE_%d * 3) + " % ln + BS)
lines.append("    (`INNER2_MACRO + \"deep string\") + " + BS)                  # 840 probes C1a/C1c
for ln in range(841, 845):                                                      # 841..844
    lines.append("    (VALUE_%d * 3) + " % ln + BS)
lines.append("    (LAST2_TERM))")                                              # 845 no backslash
lines.append("")                                                                # 846
lines.append("  logic [7:0] mid2_data;")                                       # 847 probe C3
for i in range(6):                                                              # 848..853
    lines.append("  logic mid2_filler_%d;" % i)
lines.append("")                                                                # 854
lines.append("  my_module #(.WIDTH(32), .DEPTH(16)) u_dut2 (")                 # 855
for i in range(299):                                                            # 856..1154
    lines.append("    .port_%d (sig_%d)," % (i, i))
lines.append("    .deep_port (deep_sig),")                                      # 1155 probe E1
for i in range(4):                                                              # 1156..1159
    lines.append("    .tail_%d (tail_sig_%d)," % (i, i))
lines.append("    .last2_port (last2_sig)")                                     # 1160
lines.append("  );")                                                            # 1161
lines.append("  logic [7:0] tail2_data;")                                      # 1162 probe E3
lines.append("  initial begin")                                                 # 1163
lines.append("    data_in = 8'h00;")                                            # 1164
lines.append("  end")                                                           # 1165
lines.append("endmodule")                                                       # 1166
lines.append("// end of probe2 file")                                           # 1167

assert len(lines) == 1167, len(lines)
assert lines[20].lstrip().startswith("/*"), lines[20]
assert lines[519].strip().startswith("module"), lines[519]
assert lines[530].rstrip().endswith("*/"), lines[530]
assert lines[539].endswith(BS), repr(lines[539])
assert lines[839].endswith(BS), repr(lines[839])
assert not lines[844].endswith(BS), repr(lines[844])
assert "u_dut2 (" in lines[854], lines[854]
assert lines[1160] == "  );", repr(lines[1160])
for ln in list(range(541, 840)) + list(range(841, 845)):
    assert lines[ln - 1].endswith(BS), (ln, repr(lines[ln - 1]))

def col2(ln, needle):
    return lines[ln - 1].index(needle) + 1

probes2 = [
    ("B2", 30, col2(30, "comment")),
    ("B1", 520, col2(520, "module")),
    ("B3", 533, col2(533, "logic")),
    ("C2", 545, col2(545, "VALUE_545")),
    ("C1a", 840, col2(840, "`")),
    ("C1c", 840, lines[839].rindex("+") + 1),
    ("C3", 847, col2(847, "logic")),
    ("E2", 860, col2(860, "port_4")),
    ("E1", 1155, col2(1155, "deep_port")),
    ("E3", 1162, col2(1162, "logic")),
]

with open(os.path.join(BASE, "probe2.sv"), "w") as f:
    f.write("\n".join(lines) + "\n")
with open(os.path.join(BASE, "probes2.txt"), "w") as f:
    for label, ln, co in probes2:
        f.write("%s %d %d\n" % (label, ln, co))
print("GEN_DONE probes=%d+%d" % (len(probes1), len(probes2)))
PYGEN_EOF
then
    echo "ERROR: fixture generation failed"
    cat "$WORK/gen.log"
    exit 2
fi

# --- step 2: one-shot probe script (fresh vim per probe, no priming) ---
cat >"$WORK/probe_one.vim" <<'VIM_EOF'
" One-shot syntax probe. Params via env vars:
"   PROBE_LAYOUT PROBE_LNAME PROBE_FILE PROBE_LINE PROBE_COL
"   PROBE_MODE (jump|fromstart) PROBE_OUT PROBE_LABEL
" Jump mode: NO sync command at all (measures jump-into-middle behavior).
" Fromstart mode: 'syntax sync fromstart' before any synID call (ground truth).
" Exactly one probe per vim invocation: no earlier synID call may prime state.
execute 'set rtp^=' . $PROBE_LAYOUT
syntax on
execute 'edit ' . fnameescape($PROBE_FILE)
setlocal filetype=systemverilog
if $PROBE_MODE ==# 'fromstart'
  syntax sync fromstart
endif
let s:ln = str2nr($PROBE_LINE)
let s:co = str2nr($PROBE_COL)
call cursor(s:ln, 1)
let s:stack = map(synstack(s:ln, s:co), 'synIDattr(v:val, "name")')
let s:leaf0 = synIDattr(synID(s:ln, s:co, 0), 'name')
let s:leaf1 = synIDattr(synID(s:ln, s:co, 1), 'name')
if s:leaf0 ==# '' | let s:leaf0 = 'NONE' | endif
if s:leaf1 ==# '' | let s:leaf1 = 'NONE' | endif
let s:line = $PROBE_LNAME . "\t" . $PROBE_LABEL . "\t" . $PROBE_MODE . "\t" . s:ln . "\t" . s:co . "\t" . s:leaf0 . "\t" . s:leaf1 . "\t" . join(s:stack, ',') . "\t" . get(b:, 'current_syntax', 'MISSING')
call writefile([s:line], $PROBE_OUT, 'a')
qall!
VIM_EOF

# --- step 3: probe matrix (2 fixtures x 2 modes x probes, fresh vim each) ---
rm -f "$WORK/results.tsv"
run_fixture() {
  fx_tag=$1; fx_file=$2; fx_probes=$3
  for mode in jump fromstart; do
    while IFS=' ' read -r label ln co; do
      if [ -z "$label" ]; then continue; fi
      PROBE_LAYOUT=$PLUGDIR PROBE_LNAME=$fx_tag PROBE_FILE=$WORK/$fx_file PROBE_LINE=$ln PROBE_COL=$co PROBE_MODE=$mode PROBE_OUT=$WORK/results.tsv PROBE_LABEL=$label "$VIM" -Nu NONE -n -es -S "$WORK/probe_one.vim" < /dev/null
    done < "$WORK/$fx_probes"
  done
}
run_fixture probe probe.sv probes.txt
run_fixture probe2 probe2.sv probes2.txt

# --- step 4: compare jump vs fromstart per probe ---
if ! python3 - "$WORK/results.tsv" "$WORK/probes.txt" "$WORK/probes2.txt" "$WORK/result.txt" >"$WORK/cmp.log" 2>&1 <<'PYCMP_EOF'
import sys

results_path, probes1_path, probes2_path, out_path = sys.argv[1:5]
fixtures = {}
for tag, path in (("probe", probes1_path), ("probe2", probes2_path)):
    labels = []
    with open(path) as f:
        for line in f:
            parts = line.split()
            if parts:
                labels.append(parts[0])
    fixtures[tag] = labels

rows = {}
try:
    with open(results_path) as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 9:
                rows[(parts[0], parts[1], parts[2])] = parts[3:]
except FileNotFoundError:
    rows = {}

fails = []
total = 0
for tag, labels in fixtures.items():
    for lb in labels:
        total += 1
        j = rows.get((tag, lb, "jump"))
        g = rows.get((tag, lb, "fromstart"))
        if j is None or g is None:
            fails.append("  %s %s: MISSING %s row (jump=%s fromstart=%s)"
                         % (tag, lb, "jump" if j is None else "fromstart",
                            "present" if j else "absent",
                            "present" if g else "absent"))
            continue
        if j[5] != "systemverilog" or g[5] != "systemverilog":
            fails.append("  %s %s: syntax not applied (jump syn=%s fromstart syn=%s)"
                         % (tag, lb, j[5], g[5]))
            continue
        if j[2:5] != g[2:5]:
            fails.append("  %s %s: jump leaf0=%s leaf1=%s stack=[%s] vs fromstart leaf0=%s leaf1=%s stack=[%s]"
                         % (tag, lb, j[2], j[3], j[4], g[2], g[3], g[4]))

if fails:
    out = ["FAIL: %d/%d syntax sync probes differ (jump vs fromstart)" % (len(fails), total)] + fails
else:
    out = ["PASS: %d/%d syntax sync probes (jump matches fromstart)" % (total, total)]
with open(out_path, "w") as f:
    f.write("\n".join(out) + "\n")
PYCMP_EOF
then
    echo "ERROR: comparison failed"
    cat "$WORK/cmp.log"
    exit 2
fi

if [ ! -f "$WORK/result.txt" ]; then
    echo "ERROR: sync-test comparison produced no result"; exit 2
fi
cat "$WORK/result.txt"
head -1 "$WORK/result.txt" | grep -q '^PASS' || exit 1
exit 0
