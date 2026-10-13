" Vim-side indent snapshot writer. Sourced by test/run_uvm_golden_test.sh
" (and test/regen_uvm_golden.sh) with:
"   g:sv_files_list  - file listing .svh/.sv paths, one per line
"   g:sv_srcroot     - the UVM src directory (to strip for relative paths)
"   g:sv_outdir      - where to write each re-indented file, same rel path
"
" For every file: re-indent with gg=G and write it under g:sv_outdir.

if !exists('g:sv_files_list') || !exists('g:sv_outdir')
  qall!
endif

let s:files = readfile(g:sv_files_list)
for s:f in s:files
  if s:f == ''
    continue
  endif
  enew!
  execute 'edit' fnameescape(s:f)
  setlocal shiftwidth=2 tabstop=2 expandtab
  keepjumps normal! gg=G
  let s:rel = strpart(s:f, len(g:sv_srcroot) + 1)
  let s:out = g:sv_outdir . '/' . s:rel
  call mkdir(fnamemodify(s:out, ':h'), 'p')
  execute 'w!' fnameescape(s:out)
endfor
qall!
