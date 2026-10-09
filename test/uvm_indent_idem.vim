" Vim-side indent idempotency runner. Sourced by test/run_uvm_indent_test.sh
" with g:sv_files_list (a file listing one .sv/.svh path per line) and
" g:sv_result (output file) set.
"
" For every source file:
"   1. re-indent the whole buffer with gg=G (first pass)
"   2. check no line's indent exceeds MAX_COLS (runaway indentation)
"   3. re-indent the already-indented buffer again (second pass)
"   4. the second pass must not change anything: re-running the indent
"      engine on its own output has to be a no-op (idempotency)

if !exists('g:sv_files_list') || !exists('g:sv_result')
  call writefile(['ERROR: uvm_indent_idem.vim: g:sv_files_list and g:sv_result must be set'],
        \ get(g:, 'sv_result', '/dev/null'))
  qall!
endif

let s:MAX_COLS = 40   " 20 levels at shiftwidth=2

let s:files = filter(readfile(g:sv_files_list), 'v:val =~# ''\.\(svh\|sv\)$''')
if empty(s:files)
  call writefile(['ERROR: uvm_indent_idem.vim: no files in ' . g:sv_files_list], g:sv_result)
  qall!
endif

let s:fails = []
for s:file in s:files
  try
    " enew! first: a fresh buffer guarantees no stale b: state from the
    " previously indented file (b:in_block_comment, b:did_indent, ...)
    enew!
    execute 'edit' fnameescape(s:file)
    setlocal shiftwidth=2 tabstop=2 expandtab
    " first pass: normalize indentation to the engine's own style
    keepjumps normal! gg=G
    let s:maxind = 0
    let s:lnum = 1
    while s:lnum <= line('$')
      let s:ind = indent(s:lnum)
      if s:ind > s:maxind
        let s:maxind = s:ind
      endif
      let s:lnum += 1
    endwhile
    if s:maxind > s:MAX_COLS
      call add(s:fails, printf('%s: runaway indent (%d columns)', s:file, s:maxind))
      continue
    endif
    " second pass must be a no-op on the engine's own output
    setlocal nomodified
    keepjumps normal! gg=G
    if &modified
      call add(s:fails, s:file . ': second gg=G pass still changed lines')
    endif
  catch
    call add(s:fails, printf('%s: %s', s:file, v:exception))
  endtry
endfor

if empty(s:fails)
  call writefile([printf('PASS: indent idempotency over %d UVM files', len(s:files))], g:sv_result)
else
  let s:out = [printf('FAIL: indent idempotency, %d/%d UVM files', len(s:fails), len(s:files))]
        \ + map(copy(s:fails), '"  " . v:val')
  call writefile(s:out, g:sv_result)
endif
qall!
