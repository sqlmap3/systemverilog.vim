" Vim-side smoke test over a real UVM 1.2 source tree. Sourced by
" test/run_uvm_syntax_test.sh with g:uvm_src set to the library src dir and
" g:sv_result to the output file: every .sv/.svh file must load cleanly
" with the systemverilog filetype and syntax applied.

if !exists('g:uvm_src') || !exists('g:sv_result')
  call writefile(['ERROR: uvm_syntax_smoke.vim: g:uvm_src and g:sv_result must be set'],
        \ get(g:, 'sv_result', '/dev/null'))
  qall!
endif

" globpath(..., 0, 1) already returns a List - do not wrap in split()
let s:files = globpath(g:uvm_src, '**/*.svh', 0, 1)
      \ + globpath(g:uvm_src, '**/*.sv', 0, 1)
if empty(s:files)
  call writefile(['ERROR: uvm_syntax_smoke.vim: no sources under ' . g:uvm_src], g:sv_result)
  qall!
endif

let s:fails = []
for s:file in s:files
  try
    " enew! first: a fresh buffer guarantees no stale b: state from the
    " previously loaded file (b:current_syntax, b:did_ftplugin, ...)
    enew!
    execute 'edit' fnameescape(s:file)
    if &filetype !=# 'systemverilog'
      call add(s:fails, printf('%s: filetype=%s', s:file, &filetype))
    elseif get(b:, 'current_syntax', '') !=# 'systemverilog'
      call add(s:fails, s:file . ': syntax not applied')
    endif
  catch
    call add(s:fails, printf('%s: %s', s:file, v:exception))
  endtry
endfor

if empty(s:fails)
  call writefile([printf('PASS: UVM smoke test, %d files loaded cleanly', len(s:files))], g:sv_result)
else
  let s:out = [printf('FAIL: UVM smoke test, %d/%d files', len(s:fails), len(s:files))]
        \ + map(copy(s:fails), '"  " . v:val')
  call writefile(s:out, g:sv_result)
endif
qall!
