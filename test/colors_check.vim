" Vim-side colorscheme regression check. Sourced by test/run_colors_test.sh.
" Loads colors/systemverilog_uvm.vim in dark and light backgrounds and
" verifies that the key semantic groups get a real color, that the
" high-distinction UVM categories differ from one another and from the
" generic groups, and that dark and light actually pick different palettes.
"
" Writes PASS/FAIL lines to g:sv_result.

let s:fails = []
let s:cpo_before = &cpo

function! s:fg(group) abort
  redir => r
  silent execute 'hi' a:group
  redir END
  return matchstr(r, 'guifg=\zs[0-9a-fA-F#]\+')
endfunction

function! s:Check(bg) abort
  execute 'set background=' . a:bg
  colorscheme systemverilog_uvm
  let l:want = ['svKeyword','svType','svStorageClass','svString','svInteger',
        \ 'svMacroRef','svAssertLabel','svSVAOp','svThisSuper','uvmBaseClass',
        \ 'uvmGlobalFn','uvmEnum','uvmPort','uvmTLM','uvmReg','uvmConfig',
        \ 'uvmResource','uvmPhase','svFunctionName','uvmApiMethod']
  for l:g in l:want
    let l:c = s:fg(l:g)
    if l:c ==# ''
      call add(s:fails, a:bg . ':' . l:g . ' has no guifg')
    endif
  endfor
  " cterm mirroring: a gui=bold/italic group must carry the same
  " cterm attrs, so terminal Vim without termguicolors keeps
  " the emphasis.
  let l:cterm_attrs = [['Comment', 'italic'], ['svLineComment', 'italic'],
        \ ['svBlockComment', 'italic'], ['svDocLineComment', 'italic'],
        \ ['svDocBlockComment', 'italic'], ['svDocTag', 'bold'],
        \ ['svDocTag', 'italic'], ['svFormatSpecifier', 'bold'],
        \ ['svDirection', 'italic'], ['svThisSuper', 'italic'],
        \ ['svAssertLabel', 'bold'], ['svSVAOp', 'bold'],
        \ ['svModuleName', 'bold'], ['svInterfaceName', 'bold'],
        \ ['svPackageName', 'bold'], ['svInstanceName', 'bold'],
        \ ['svNamedPort', 'bold'], ['svModuleKw', 'bold'],
        \ ['svInterfaceKw', 'bold'], ['svPackageKw', 'bold'],
        \ ['svClassKw', 'bold'], ['svFunctionKw', 'bold'],
        \ ['svTaskKw', 'bold'], ['Keyword', 'bold'],
        \ ['uvmRunTest', 'bold'], ['Title', 'bold'], ['Todo', 'bold']]
  for l:t in l:cterm_attrs
    if synIDattr(hlID(l:t[0]), l:t[1], 'cterm') !=# '1'
      call add(s:fails, a:bg . ':' . l:t[0] . ' missing cterm ' . l:t[1])
    endif
  endfor
  " plain groups must not gain cterm= attrs
  let l:plain = ['svKeyword', 'svType', 'svString', 'svInteger', 'svMacroRef', 'Statement', 'uvmBaseClass', 'Normal']
  for l:g in l:plain
    redir => l:hi
    silent execute 'hi' l:g
    redir END
    if l:hi =~# 'cterm='
      call add(s:fails, a:bg . ':' . l:g . ' unexpectedly has cterm=')
    endif
  endfor
  " direct-line groups must pin the cterm half (no
  " terminal-dependent leftovers from Vim defaults)
  let l:leftover = [['NonText', 'fg', ''], ['NonText', 'bg', ''],
        \ ['SpecialKey', 'fg', ''], ['SpecialKey', 'bg', ''],
        \ ['EndOfBuffer', 'fg', '238'], ['Search', 'fg', ''],
        \ ['Search', 'bg', '52'], ['IncSearch', 'fg', ''],
        \ ['IncSearch', 'bg', '58'], ['IncSearch', 'reverse', ''],
        \ ['Visual', 'fg', ''], ['Visual', 'bg', '24'],
        \ ['Visual', 'reverse', ''], ['FoldColumn', 'bg', ''],
        \ ['ErrorMsg', 'bg', '']]
  for l:t in l:leftover
    if synIDattr(hlID(l:t[0]), l:t[1], 'cterm') !=# l:t[2]
      call add(s:fails, a:bg . ':' . l:t[0] . ' cterm' . l:t[1] . '=' . synIDattr(hlID(l:t[0]), l:t[1], 'cterm') . ' want=' . l:t[2])
    endif
  endfor
  " high distinction: these must be pairwise distinct
  let l:distinct = ['svKeyword','svType','uvmBaseClass','uvmGlobalFn',
        \ 'uvmEnum','uvmPort','uvmConfig','uvmResource']
  let l:i = 0
  while l:i < len(l:distinct)
    let l:j = l:i + 1
    while l:j < len(l:distinct)
      if s:fg(l:distinct[l:i]) ==# s:fg(l:distinct[l:j])
        call add(s:fails, a:bg . ':' . l:distinct[l:i] . ' == ' . l:distinct[l:j])
      endif
      let l:j += 1
    endwhile
    let l:i += 1
  endwhile
endfunction

call s:Check('dark')
call s:Check('light')

" dark and light must actually differ on the shared groups
execute 'set background=dark'
colorscheme systemverilog_uvm
let s:dark_kw = s:fg('svKeyword')
execute 'set background=light'
colorscheme systemverilog_uvm
let s:light_kw = s:fg('svKeyword')
if s:dark_kw ==# s:light_kw
  call add(s:fails, 'dark/light svKeyword identical: ' . s:dark_kw)
endif

" cpo smoke: the scheme must source cleanly with cpo+=C (its
" palette and class-list continuations need cpo&vim) and must
" leave &cpo undisturbed. No continuation lines below on purpose.
let s:cpo_save = &cpo
for s:bg in ['dark', 'light']
  let s:cpo_err = ''
  set cpo+=C
  try
    execute 'set background=' . s:bg
    colorscheme systemverilog_uvm
  catch
    let s:cpo_err = v:exception
  endtry
  if &cpo !~# 'C'
    call add(s:fails, 'cpo smoke ' . s:bg . ': scheme disturbed &cpo: ' . &cpo)
  endif
  let &cpo = s:cpo_save
  if s:cpo_err !=# ''
    call add(s:fails, 'cpo smoke ' . s:bg . ': ' . s:cpo_err)
  endif
  for s:g in ['svKeyword', 'svType', 'svMacroRef', 'uvmBaseClass', 'Todo', 'Comment']
    if !hlexists(s:g)
      call add(s:fails, 'cpo smoke ' . s:bg . ':' . s:g . ' missing')
    endif
  endfor
  if synIDattr(hlID('Normal'), 'fg', 'gui') ==# ''
    call add(s:fails, 'cpo smoke ' . s:bg . ':Normal cleared')
  endif
endfor
if &cpo !=# s:cpo_before
  call add(s:fails, 'cpo changed by colorscheme runs: ' . s:cpo_before . ' -> ' . &cpo)
endif

if empty(s:fails)
  call writefile(['PASS: colorscheme systemverilog_uvm loads and distinguishes groups'], g:sv_result)
else
  call writefile(['FAIL: colorscheme check'] + map(copy(s:fails), '"  " . v:val'), g:sv_result)
endif
qall!
