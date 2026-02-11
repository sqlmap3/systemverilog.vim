# systemverilog.vim

**Vim/Neovim Indent & Syntax Plugin for SystemVerilog & UVM**

[![License: GPL-2.0](https://img.shields.io/badge/License-GPL%20v2-blue.svg)](LICENSE)

**Language:** English  
**Maintainer:** [sqlmap3](https://github.com/sqlmap3/systemverilog.vim)  
**Version:** 0.1  
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
- Open an SV/UVM file and verify:
  - `:set ft?` → `filetype=systemverilog`
- Use `%` to jump between `uvm_*_utils_begin/_end` or `covergroup/endgroup`
- Indentation respects case labels and single-line `if`

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
