" Vim-side colorscheme regression check. Sourced by test/run_colors_test.sh.
" Loads colors/systemverilog_uvm.vim in dark and light backgrounds and
" verifies that the key semantic groups get a real color, that the
" high-distinction UVM categories differ from one another and from the
" generic groups, and that dark and light actually pick different palettes.
"
" Writes PASS/FAIL lines to g:sv_result.

let s:fails = []

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

if empty(s:fails)
  call writefile(['PASS: colorscheme systemverilog_uvm loads and distinguishes groups'], g:sv_result)
else
  call writefile(['FAIL: colorscheme check'] + map(copy(s:fails), '"  " . v:val'), g:sv_result)
endif
qall!
