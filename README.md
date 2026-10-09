# systemverilog.vim

**Vim/Neovim Indent & Syntax Plugin for SystemVerilog & UVM**

[![License: GPL-2.0](https://img.shields.io/badge/License-GPL%20v2-blue.svg)](LICENSE)

**Language:** English  
**Maintainer:** [sqlmap3](https://github.com/sqlmap3/systemverilog.vim)  
**Version:** 0.2  
**First Change:** 2025-12-06  
**Last Change:** Wed Feb 11 21:08:29 CST 2026  

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
  - Instantiation readability: instance name highlighting and named port `.port(...)` highlighting
  - Assertion labels highlighting: `label: assert/assume/cover ...`

- Optional code folding in the style of [vhda/verilog_systemverilog.vim](https://github.com/vhda/verilog_systemverilog.vim): modules, classes, tasks, functions, packages, `` `uvm_*_utils_begin/_end ``, `/* */` comments, `` `ifdef `` blocks, multi-line `` `define `` and (opt-in) `begin/end` blocks or instantiations.

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
  highlighted as `Structure` and the `::set`/`::get`/`::exists` method as
  `Label`. Any other `uvm_*[#(params)]::method` static call is highlighted
  via one generic pattern.
- All `$`-system calls (`$display`, `$rose`, `$past`, `$clog2`, `$cast`,
  `$fopen`, `$fscanf`, ...) share one catch-all group instead of a huge
  hardcoded list — one regex, same color, much faster to load.
- SVA operators `|->`, `|=>` and `##N` have their own operator group;
  `disable iff`, `intersect`, `throughout`, `within` are keywords.
- Built-in methods (`.size()`, `.push_back()`, `.randomize()`, ...) are
  highlighted when called with parentheses.
- `virtual my_if vif;` highlights the custom type after `virtual`.

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

Optional module-body indentation — by default `module`/`package`/`program`/
`interface` contents stay at the same level as the keyword (upstream
nachumk behavior). Enable one level of body indentation with:

```vim
let g:systemverilog_indent_modules = 1   " or per-buffer b:systemverilog_indent_modules
```

Indent notes:
- `` `uvm_object_utils_begin(foo) `` / `` `uvm_object_utils_end `` indent
  like `begin`/`end`: `` `uvm_field_* `` entries get one extra level and the
  closing `_utils_end` macro dedents.
- `` `elsif `` is treated like `` `else `` / `` `endif `` (no code indent).
- Known limitation (inherited from upstream): keywords inside strings can
  disturb the code classification, e.g. `$display("class foo")` — the
  conversion runs before string stripping.

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
