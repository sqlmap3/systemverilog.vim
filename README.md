# systemverilog.vim

**Vim/Neovim Indent & Syntax Plugin for SystemVerilog & UVM**

[![License: GPL-2.0](https://img.shields.io/badge/License-GPL%20v2-blue.svg)](LICENSE)

**Language:** English  
**Maintainer:** [sqlmap3](https://github.com/sqlmap3/systemverilog.vim)  
**Version:** 0.3  
**First Change:** 2025-12-06  
**Last Change:** Fri Oct 09 2026  

---

This plugin extends [nachumk/systemverilog.vim](https://github.com/nachumk/systemverilog.vim) to add UVM support and refine SystemVerilog editing.  
It fixes indentation edge cases (case labels, single-line `if`, grouping blocks), adds UVM-specific syntax highlighting, and completes matchit pairs for common UVM/SV constructs.

---

## Features

- Accurate indentation for SystemVerilog and UVM, including:
  - Case branch labels (`{10,11}:`, numeric/literal, `default:`) align with subsequent `if/else`
  - UVM macro lines (e.g., `` `uvm_info ``, `` `uvm_error ``) treated as statement terminators
  - Stable grouping for `class/endclass`, `function/endfunction`, `task/endtask`
  - Handles block/line comments and strings robustly
  - UVM-specific syntax highlighting and matchit pairs
  - Indentation fixes for single-line `if ... begin ... end` and `else` on next line
  - Lower priority for `assert`/`else` in multi-line conditions (if/else jump preferred)

- Syntax highlighting improvements for SystemVerilog/UVM, including:
  - `include` path highlighting (`"file.svh"` / `<file.sv>`) and file extension emphasis
  - Macro usage highlighting for `` `uvm_* `` and user macros; macro args highlighting for `` `define NAME(args) ``
  - Time unit highlighting (`fs/ps/ns/us/ms/s/step`, case-insensitive, supports real delays)
  - UVM phase helpers (e.g., `uvm_*_phase::get`)
  - Enum enumerator highlighting, struct field highlighting
  - Instantiation readability: named port `.port(...)` highlighting
  - Assertion labels highlighting: `label: assert/assume/cover ...`

- Optional code folding in the style of [vhda/verilog_systemverilog.vim](https://github.com/vhda/verilog_systemverilog.vim): modules, classes, tasks, functions, packages, `` `uvm_*_utils_begin/_end ``, `/* */` comments, `` `ifdef `` blocks, multi-line `` `define `` and (opt-in) `begin/end` blocks or instantiations.

## Recent Changes (2026-10-09)

- Fix indent regression: multi-line `` `define `` bodies (backslash
  continuations) now indent structurally again (`begin`/`if`/`end` inside a
  macro body), while an expression split across continuation lines stays
  flat — verified against the golden indent test.
- Fix syntax items that a `\zs` in a `:syntax match` silently disables (the
  match is anchored at `\zs`, so a leading keyword/class never matches):
  - module/interface/package/class/covergroup names via `nextgroup`
  - `` ::set ``/`` ::get ``/`` ::exists ``/`` ::get_by_name ``/... and generic
    `uvm_class::method` static calls
  - `super.new` / `this.new` and `type_id::create`
- Fix precedence so the specific UVM groups win over the generic catch-alls
  (`` uvm_reg_adapter ``→`uvmRegAdapterClass`, `` uvm_tlm_generic_payload ``
  →`uvmGenericPayloadClass`, ...): the `uvm_reg_*`/`uvm_tlm_*`/port/socket
  catch-alls are now defined before the specific class groups.
- Stop `` `define ``/`` `ifdef `` name groups from leaking into instance,
  port, enum and struct regions (`contains=ALLBUT`).
- Add UVM 1.2 library coverage: base classes, scalar types, and the
  `uvm_report_*` global functions (see below).

## Recent Changes (2026-02-11)

- Expand TODO markers in comments: `TODO/FIXME/XXX/BUG/...` (case-insensitive)
- Fix macro name regex so `` `uvm_info/`uvm_error `` highlight as a whole token
- Unify preprocessor directive coloring (e.g., `ifdef/ifndef/elsif/else/endif/define`)
- Add/extend SV highlighting:
  - Time units, uppercase identifiers, generic `$system_call` highlighting
  - `include` path + extension, enum enumerators, struct fields
  - Module/interface/class/task/function/typedef/parameter naming
  - Instantiation: instance names + named port `.port` names

## Installation

**Manual:**
- Vim:
  - `indent/systemverilog.vim` → `~/.vim/indent/`
  - `syntax/systemverilog.vim` → `~/.vim/syntax/`
- Neovim:
  - `indent/systemverilog.vim` → `~/.config/nvim/indent/`
  - `syntax/systemverilog.vim` → `~/.config/nvim/syntax/`
- Windows:
  - `indent/systemverilog.vim` → `~/vimfiles/indent/` or `~/AppData/Local/nvim/indent/`
  - `syntax/systemverilog.vim` → `~/vimfiles/syntax/` or `~/AppData/Local/nvim/syntax/`

**Plugin manager (vim-plug):**
```vim
Plug 'sqlmap3/systemverilog.vim'
```
Ensure `indent/systemverilog.vim` is under your `runtimepath`’s `indent/` directory.

**Pathogen:**
```vim
runtime macros/matchit.vim
execute pathogen#infect()
filetype plugin indent on
```
Clone:
```bash
git clone https://github.com/sqlmap3/systemverilog.vim ~/.vim/bundle/systemverilog.vim
```
PowerShell:
```powershell
git clone https://github.com/sqlmap3/systemverilog.vim $HOME/vimfiles/bundle/systemverilog.vim
```
Verify:
- Open a `*.sv` or `*.svh` file → `:set ft?` shows `filetype=systemverilog`
- `:set shiftwidth?` shows `2`; `%` jumps between `uvm_object_utils_begin/_end`

## Quick Start

- Install via vim-plug or Pathogen
- Enable matchit: `runtime macros/matchit.vim`
- Optional folding: `let g:systemverilog_syntax_fold = 'default'` (see Folding below)
- Open an SV/UVM file and verify:
  - `:set ft?` → `filetype=systemverilog`
- Use `%` to jump between `uvm_*_utils_begin/_end` or `covergroup/endgroup`
- Indentation respects case labels and single-line `if`

## Folding (optional)

Code folding in the style of [vhda/verilog_systemverilog.vim](https://github.com/vhda/verilog_systemverilog.vim), implemented on this plugin's own construct classification.

Enable it in your `vimrc` **before** opening an SV file:

```vim
let g:systemverilog_syntax_fold = 'default'
```

Values:

| Value | Folds |
|---|---|
| `'default'` | `block` + `comment` + `conditional` + `define` + `marker` |
| `'all'` | everything below |
| `['block', ...]` | a list of individual options |

Individual options (combine freely in a list):

| Option | Folds |
|---|---|
| `block` | `module`/`class`/`task`/`function`/`interface`/`package`/`program`/`covergroup`/`property`/`sequence`/`clocking`/... plus `` `uvm_*_utils_begin `` / `` `uvm_*_utils_end `` |
| `begin_blocks` | `begin`/`end`, `case`/`endcase`, `fork`/`join` (can be noisy) |
| `comment` | `/* ... */` block comments |
| `conditional` | `` `ifdef `` / `` `ifndef `` / `` `elsif `` / `` `else `` / `` `endif `` |
| `define` | multi-line `` `define `` (backslash continuations) |
| `instance` | multi-line instantiations (heuristic) |
| `marker` | manual `// {{{` / `// }}}` fold markers |

Manual marker folds coexist with keyword folds in the same buffer — both run
through the same `foldexpr` engine, so there is no need to switch
`foldmethod` to `marker` or `syntax`:

```systemverilog
class my_driver extends uvm_driver;  " zc here folds the whole class
  ...
endclass

// {{{ temporary debug logic, remove after bring-up
always @(posedge clk) begin
  ...
end
// }}}
```

A collapsed marker fold shows only the description written after `{{{`
(`+-- 4 lines: temporary debug logic, remove after bring-up`).

Correctness notes:

- `extern`/`pure virtual` function or task prototypes, DPI `import "..." function` declarations and `typedef class` forward declarations never open a fold.
- `assert property`, `default clocking`, `virtual interface` declarations, `disable fork` / `wait fork` and `covergroup ... with function sample()` are recognized and do not open spurious folds.
- Single-line `begin ... end` / `case ... endcase` never create an empty fold.

With folding enabled, `za`/`zA`/`zr`/`zm` work as usual, and a collapsed block renders as:

```
+-- 12 lines: class my_class extends uvm_component;
```

A sample file exercising all of the above is in [test/fold_demo.sv](test/fold_demo.sv).

## UVM version flavor

Syntax highlighting cannot auto-detect which UVM library a project uses —
the class names are nearly identical across versions — so the version is a
configuration option. In your `vimrc` (or per-project via an autocmd):

```vim
let g:systemverilog_uvm_version = '1.1'   " UVM 1.1
let g:systemverilog_uvm_version = '1.2'   " UVM 1.2 (default)
```

What it changes:

- **UVM 1.1**: phase callbacks are highlighted with their 1.1 names
  (`build`, `connect`, `end_of_elaboration`, `run`, `extract`, `check`,
  `report`, plus the dynamic `configure`/`main`/`shutdown` phases), and the
  1.1-era globals `uvm_test_done` / `global_stop_request` get their own
  group.
- **UVM 1.2** (default): the `*_phase` callback names (already highlighted
  regardless) are joined by the 1.2 phase-schedule classes (`uvm_domain`,
  `uvm_topdown_phase`, `uvm_bottomup_phase`, `uvm_task_phase`,
  `uvm_runtime_phase`, `uvm_tlm_time`).

A buffer-local `b:systemverilog_uvm_version` overrides the global, which is
handy for monorepos mixing UVM 1.1 and 1.2 testbenches.

Extra project-specific class names (any UVM version, custom VIPs) can be
highlighted as types:

```vim
let g:systemverilog_uvm_names = ['my_agent', 'my_scoreboard', 'vip_pkg']
```

## Syntax highlight notes

- `uvm_config_db#(int)::set(...)` / `uvm_config_db::get(...)`: the class is
  highlighted as `Structure` (`uvm_config_db`) and the `::set`/`::get`/
  `::exists`/`::get_by_name`/... method as `Label`. Any other
  `::method` static call is highlighted as `Function`.
- All `$`-system calls (`$display`, `$rose`, `$past`, `$clog2`, `$cast`,
  `$fopen`, `$fscanf`, ...) share one catch-all group instead of a huge
  hardcoded list — one regex, same color, much faster to load.
- SVA operators `|->`, `|=>` and `##N` have their own operator group;
  `disable iff`, `intersect`, `throughout`, `within` are keywords.
- Built-in methods (`.size()`, `.push_back()`, `.randomize()`, ...) are
  highlighted when called with parentheses.
- `virtual my_if vif;` highlights the custom type after `virtual`.
- UVM 1.2 library coverage (verified against the actual `uvm-1.2` source
  tree): besides the well-known classes, the factory/registry, base
  classes (`uvm_sequence_base`, `uvm_sequencer_base`, `uvm_transaction`,
  `uvm_void`, ...), pools/queues, report plumbing (`uvm_report_server`,
  `uvm_report_message`), visitors, links, DAPs, RAL memory regions and
  virtual registers are highlighted as types; the lowercase scalar types
  (`uvm_verbosity`, `uvm_action`, `uvm_radix_enum`, ...) as types; and the
  `uvm_report_info/warning/error/fatal/enabled` global functions plus
  `uvm_wait_for_nba_region` as functions.

## Known limitations

- `task`/`function` names, `typedef` names, `parameter`/`localparam` names,
  instance names and `struct`/`enum` members are not highlighted: those
  rules relied on `\zs` with a leading context, which `:syntax match` does
  not support (the match is anchored at `\zs`). They are left in place but
  inert; the common `module`/`interface`/`package`/`class`/`covergroup`
  names and `::method` calls were moved to `nextgroup`/plain matches.
- `uvm_config_db::set/get/exists` and friends are matched as a plain
  `::name` group, so `::set`/`::get` after any class share the `Label`
  color (e.g. `uvm_factory::get()`), rather than only after a UVM config
  class.
- **Indent performance**: the indent engine re-scans backward through
  comment and backslash-continuation blocks for every line, so re-indenting
  a very large macro file (thousands of lines of `` `define `` bodies) takes
  a long time (minutes / possible OOM on a 3k+ line file). Small and
  medium files are unaffected. This is why `run_uvm_indent_test.sh` checks
  a curated subset by default.

## Supported Filetypes

- `*.v`, `*.vh`, `*.sv`, `*.svh`, `*.svp`, `*.svi`

## Requirements

- Vim 8+ or Neovim
- Optional: `matchit.vim` for keyword pair jumping

## Recommended Plugins

Below are some useful Vim/Neovim plugins for SystemVerilog/UVM development.  
Most are available via [vim-plug](https://github.com/junegunn/vim-plug) or other plugin managers.

- [fzf](https://github.com/junegunn/fzf): Fuzzy file finder, fast project navigation.
- [indentLine](https://github.com/Yggdroot/indentLine): Indentation guides, visually show indent levels.
- [log-highlight](https://github.com/mtdl9/vim-log-highlighting): Syntax highlight for log files.
- [NERDTree](https://github.com/preservim/nerdtree): File explorer, project tree navigation.
- [rainbow](https://github.com/luochen1990/rainbow): Rainbow parentheses/brackets, color matching pairs.
- [SrcExpl](https://github.com/wookayin/SrcExpl): Source explorer, code structure navigation.
- [Trinity](https://github.com/zhimsel/vim-trinity): Multi-pane file navigation.
- [vim-snipmate](https://github.com/garbas/vim-snipmate): Snippet engine, code templates.
- [vim-snippets](https://github.com/honza/vim-snippets): Snippet collection for snipmate/UltiSnips.
- [vim-matchup](https://github.com/andymass/vim-matchup): Enhanced matching and highlighting for keywords/regions.

**Requirements:**  
- Vim 8+ or Neovim recommended for best compatibility.
- Some plugins may require Python support or additional configuration.

## Filetype & Indentation

If SystemVerilog filetype detection isn’t enabled, add:
```vim
augroup ft_sv
  autocmd!
  autocmd BufRead,BufNewFile *.sv,*.svh setlocal filetype=systemverilog
augroup END
```

Recommended indentation:
```vim
setlocal shiftwidth=2
setlocal tabstop=2
setlocal expandtab
```

Module/package/program/interface bodies stay at the same level as the
keyword (upstream nachumk behavior). Indenting their bodies one level
requires cross-line context that this engine's per-line code
classification does not carry — if you need that, use
[vhda/verilog_systemverilog.vim](https://github.com/vhda/verilog_systemverilog.vim)
(`g:verilog_indent_modules`) instead.

Indent notes:
- `` `uvm_object_utils_begin(foo) `` / `` `uvm_object_utils_end `` indent
  like `begin`/`end`: `` `uvm_field_* `` entries get one extra level and the
  closing `_utils_end` macro dedents.
- `else` is treated as a control statement: a statement on the next line
  indents one level, and `end`/`endfunction`/`endtask` after an else-branch
  dedent correctly. `` `elsif `` is treated like `` `else `` / `` `endif ``
  (no code indent).
- Known limitation (inherited from upstream): keywords inside strings can
  disturb the code classification, e.g. `$display("class foo")` — the
  conversion runs before string stripping.

## Tests

- `sh test/run_indent_test.sh` — golden-file indent regression test:
  re-indents [test/indent_demo.sv](test/indent_demo.sv) (deliberately
  mis-indented) with `gg=G` in a headless Vim and diffs against
  [test/indent_demo.expected.sv](test/indent_demo.expected.sv). Coverage
  includes UVM field-macro blocks, single-line `if` + macro + `else`
  chains, `else if`, case labels, `fork`/`join_any`, labeled
  `generate` blocks (`if`/`else`/`for`/`case`), multi-line
  instantiations, `` `include `` chains (plain and inside `` `ifdef ``
  / `` `elsif ``), multi-line `` `define ``, `` `undef `` / `` `timescale ``
  / `` `pragma ``, `struct`/`enum`, `interface` + `modport`, flat
  `package` bodies, `function new` / `super.new`, `interface class`,
  and block comments. Use `VIM=nvim sh test/run_indent_test.sh` for
  Neovim.
- `sh test/run_fold_test.sh` — golden-file fold-level regression test:
  computes the fold level of every line of [test/fold_demo.sv](test/fold_demo.sv)
  through the `foldexpr` engine (without touching the buffer) and diffs
  against [test/fold_demo.expected.txt](test/fold_demo.expected.txt).
  Coverage: block/comment/`` `ifdef ``/`` `define ``/instance folds,
  `` `else `` branch restarts, `assert property` exclusion,
  `` `uvm_*_utils_begin/_end `` macro pairs, interface classes and manual
  `// {{{`/`// }}}` markers. Use `VIM=nvim sh test/run_fold_test.sh` for
  Neovim.
- `sh test/run_uvm_syntax_test.sh` — syntax regression test against UVM 1.2:
  1. spot-checks ~100 representative tokens in
     [test/uvm_syntax_spot.sv](test/uvm_syntax_spot.sv) (constructs lifted
     from the UVM 1.2 library: classes, scalar types, `` `include ``/`` `define ``
     /`` `ifdef `` directives, macros, `uvm_report_*` calls, config/resource
     db static calls, SVA operators and keywords, numbers, ports) against
     the expected syntax group — the pairs live in
     [test/uvm_syntax_checks.txt](test/uvm_syntax_checks.txt);
  2. loads every `.sv`/`.svh` of a real UVM 1.2 source tree and fails if
     any file errors out or misses the `systemverilog` filetype/syntax.
     Tree location defaults to `~/test/uvm-1.2/src`; override with
     `UVM_SRC=/path/to/uvm-1.2/src` or skip with `UVM_SRC=`.
- `sh test/run_uvm_indent_test.sh` — indent idempotency test over the real
  UVM 1.2 library sources (`~/test/uvm-1.2/src`, `UVM_SRC=` to override,
  skipped when the tree is absent): re-indents every file with `gg=G`
  twice — the second pass must not change anything, no line may exceed 40
  columns of indent (runaway check), and the indent engine must not raise.
  The first pass normalizes to the engine's own style, so the library's
  original formatting is irrelevant — only the stability of the engine is
  asserted. This re-indents the whole library twice and takes a few
  minutes; pass a subdirectory (e.g. `UVM_SRC=~/test/uvm-1.2/src/base`)
  for a quicker run.

## Examples

- `case` + UVM macros
```systemverilog
case (i)
  {10,11}: if (1==1)
              `uvm_info
           else
              `uvm_error
           end
  {12,13}: if (a==2)
              `uvm_info
           else
              `uvm_error
           end
endcase
```

- `class` + `task`
```systemverilog
class xxxx extends xx;
  task item();
    bit a;
    $display();
    temp_str = 0;
  endtask
endclass
```
Inner statements indent one level relative to grouping keywords (`class/task`); closing (`endtask/endclass`) reduces one level.

## Implementation (Brief)

- Keyword mapping:
  - Group start/stop: `class/config/clocking/function/task/... → f`; closing: `endclass/endfunction/endtask/... → h`
  - Block start/stop: `begin/case/fork/(/{ → b`; closing: `end/endcase/join/.../)/} → e`
  - Execution/control: `if/else/for/always/initial/... → x`
  - Preprocessor: selected backtick directives mapped to `z`
- UVM macros: backtick-prefixed lines converted to `;` (statement terminator) to consume single-line indentation from preceding `if`, not treated as control statements
- Branch labels: retained and constrained to avoid affecting `f/h` grouping (e.g., named `endfunction : name`)
- Indent logic fixes for if/else jump, single-line if/begin/end, and assert priority

## Compatibility & Limits

- Complex labeled endings (e.g., `endtask: name`) usually align correctly; please submit minimal repros for edge cases
- Heavy macro expansions or nonstandard syntax may need extra tuning

## Contributing & Issues

- Please report indentation issues via Issues/PRs with a minimal reproducible snippet (10–20 lines)
- Include Vim/Neovim version, platform, and `shiftwidth/tabstop/expandtab` settings

## Acknowledgements

- Upstream: [nachumk/systemverilog.vim](https://github.com/nachumk/systemverilog.vim)
- UVM examples referenced from official documentation
- Inspiration and prior art: https://github.com/WeiChungWu/vim-SystemVerilog
- UVM 1.2 library reference: https://github.com/gchinna/uvm-1.2
- Based on upstream ftplugin: https://github.com/nachumk/systemverilog.vim/blob/master/start/systemverilog.vim/ftplugin/systemverilog.vim (extended for UVM support)

## Enhancements by sqlmap3

- Improve indentation for special UVM/SV cases (case labels, single‑line `if`, grouping blocks)
- Add UVM syntax highlighting (classes, TLM APIs, phases, macros)
- Complete matchit pairs for common UVM/SV constructs and macros

## License

- License: GPL-2.0. See `LICENSE`.
