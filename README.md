# systemverilog.vim (Vim/Neovim Plugin)
Language: English
Maintainer: sqlmap3 < https://github.com/sqlmap3 >
Version: 0.1
First Change: Sat Dec 06 11:15:30 CST 2025
Last Change: Sat Dec 06 11:15:30 CST 2025

This plugin extends the upstream systemverilog.vim to add UVM support and refine SystemVerilog editing. It focuses on fixing indentation edge cases (case labels, single‑line `if`, grouping blocks), adds UVM‑specific syntax highlighting, and completes matchit pairs for common UVM/SV constructs.

## Features
- Improved detection of `case` branch labels (e.g., `{10,11}:`, numeric/literal labels, `default:`) so branches align with subsequent `if/else`
- UVM macro lines (e.g., `` `uvm_info ``/`` `uvm_error ``) are treated as statement terminators to properly consume single-line indentation without affecting structural indentation
- Stable grouping indentation for `class/endclass`, `function/endfunction`, `task/endtask`: inner statements indent one level; closing keywords reduce one level
- Handles block/line comments and strings so they don’t interfere with indentation decisions
- Preserves upstream keyword mapping and overall algorithm with focused UVM/SV tweaks

## Installation
Pick one of the following.

- Manual
  - Vim: put `indent/systemverilog.vim` into `~/.vim/indent/`
  - Neovim: put it into `~/.config/nvim/indent/`
  - Windows: place it under your `runtimepath`’s `indent/` directory (e.g., `~/vimfiles/indent/` or `~/AppData/Local/nvim/indent/`)

- Plugin manager (vim-plug example)
  ```vim
  Plug 'sqlmap3/systemverilog.vim'
  ```
  Ensure `indent/systemverilog.vim` ends up under your `runtimepath`’s `indent/` directory.

- Pathogen (bundle directory)
  - Install Pathogen and enable it in your vimrc:
    ```vim
    runtime macros/matchit.vim
    execute pathogen#infect()
    filetype plugin indent on
    ```
  - Clone the plugin to the bundle directory (Linux/macOS):
    ```bash
    git clone https://github.com/sqlmap3/systemverilog.vim ~/.vim/bundle/systemverilog.vim
    ```
  - On Windows (PowerShell):
    ```powershell
    git clone https://github.com/sqlmap3/systemverilog.vim $HOME/vimfiles/bundle/systemverilog.vim
    ```
  - Verify:
    - Open a `*.sv` or `*.svh` file → `:set ft?` shows `filetype=systemverilog`
    - `:set shiftwidth?` shows `2`; match pairs like `uvm_object_utils_begin/_end` jump with `%`

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
- `matchit` (built-in) — https://github.com/vim/vim/blob/master/runtime/macros/matchit.vim: enables `%` to jump between matching SV/UVM keyword pairs; works with Vim 8+ and Neovim.
- `vim-matchup` — https://github.com/andymass/vim-matchup: enhanced matching and highlighting for keywords/regions; recommended Vim 8+ or Neovim 0.5+.
- Tagbar — https://github.com/preservim/tagbar or Taglist — https://github.com/vim-scripts/taglist.vim + universal-ctags — https://github.com/universal-ctags/ctags: structural browsing of SV/UVM; SystemVerilog support requires universal-ctags (development version).

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

## Compatibility & Limits
- Complex labeled endings (e.g., `endtask: name`) usually align correctly; please submit minimal repros for edge cases
- Heavy macro expansions or nonstandard syntax may need extra tuning

## Contributing & Issues
- Please report indentation issues via Issues/PRs with a minimal reproducible snippet (10–20 lines)
- Include Vim/Neovim version, platform, and `shiftwidth/tabstop/expandtab` settings

## Acknowledgements
- Upstream: nachumk/systemverilog.vim (thanks to maintainers and contributors)
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
