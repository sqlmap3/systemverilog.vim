" Vim-side runner for the syntax spot checks. Sourced by
" test/run_uvm_syntax_test.sh with the sample file already open.
" Requires g:sv_checks_file (pattern<TAB>expected pairs, see
" test/uvm_syntax_checks.txt) and g:sv_result (output file).
"
" NOTE: :echo is suppressed under "vim -es" (silent), so results are
" written to g:sv_result for the shell to print.

if !exists('g:sv_checks_file') || !exists('g:sv_result')
  call writefile(['ERROR: uvm_syntax_check.vim: g:sv_checks_file and g:sv_result must be set'],
        \ get(g:, 'sv_result', '/dev/null'))
  qall!
endif

let s:fails = []
let s:count = 0
for s:raw in readfile(g:sv_checks_file)
  let s:line = substitute(s:raw, '#.*$', '', '')
  if s:line =~# '^\s*$'
    continue
  endif
  let s:fields = split(s:line, "\t", 1)
  if len(s:fields) != 2
    call add(s:fails, 'malformed checks line: ' . s:raw)
    continue
  endif
  let s:pat  = trim(s:fields[0])
  let s:want = trim(s:fields[1])
  let s:count += 1
  " cursor(), NOT a bare address: under -es a bare line number is the
  " classic ex ":print" command and would print the line to stdout
  call cursor(1, 1)
  if !search(s:pat, 'cW')
    call add(s:fails, printf('%s: pattern not found in sample', s:pat))
    continue
  endif
  " raw group name (trans=0): colorschemes re-map the standard highlight
  " groups (Keyword->Statement, Number->Constant, ...), so asserting the
  " resolved color would be fragile; the syntax group name is stable
  let s:got = synIDattr(synID(line('.'), col('.'), 0), 'name')
  if s:got ==# ''
    let s:got = 'NONE'
  endif
  if index(split(s:want, '|', 1), s:got) < 0
    call add(s:fails, printf('%s: expected %s, got %s  (line %d: %s)',
          \ s:pat, s:want, s:got, line('.'), trim(getline('.'))))
  endif
endfor

if empty(s:fails)
  call writefile([printf('PASS: %d syntax spot checks', s:count)], g:sv_result)
else
  let s:out = [printf('FAIL: %d/%d syntax spot checks', len(s:fails), s:count)]
        \ + map(copy(s:fails), '"  " . v:val')
  call writefile(s:out, g:sv_result)
endif
qall!
