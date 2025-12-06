" Vim ftdetect file
" Language:	systemverilog
" Maintainer:	sqlmap3 < https://github.com/sqlmap3 >
" Version:	0.1
" First Change:	Sat Dec 06 11:15:30 CST 2025
" Last Change:	Sat Dec 06 11:15:30 CST 2025
augroup ftdetect_systemverilog
  autocmd!
  autocmd BufRead,BufNewFile *.v,*.vh,*.sv,*.svh,*.svp,*.svi setfiletype systemverilog
augroup END
