" Vim autoload file
" Language:	SystemVerilog / UVM
" Maintainer:	sqlmap3 < https://github.com/sqlmap3 >
" Description:	Code folding, in the spirit of vhda/verilog_systemverilog.vim,
"		but built on this plugin's own construct classification.
" First Change:	2026-10-08
"
" Enable in your vimrc (before opening an SV file):
"	let g:systemverilog_syntax_fold = 'default'   " or 'all', or a list
"
" Options:
"   block        module/class/task/function/interface/package/covergroup/...
"                plus `uvm_*_utils_begin/_end macro pairs
"   begin_blocks begin/end, case/endcase, fork/join (can be noisy)
"   comment      /* ... */ block comments
"   conditional  `ifdef/`ifndef/`elsif/`else/`endif
"   define       multi-line `define (backslash continuations)
"   instance     multi-line instantiations (heuristic)
"   marker       manual // {{{ / // }}} fold markers
"
" 'default' = block + comment + conditional + define + marker
" 'all'     = every option above

let s:cpo_save = &cpoptions
set cpo&vim

" Folding constructs -------------------------------------------------------
let s:GROUP_OPEN =
	\ '\<\%(module\|class\|function\|task\|interface\|program\|package\|' .
	\ 'clocking\|property\|sequence\|covergroup\|checker\|config\|' .
	\ 'primitive\|table\|generate\|specify\|randsequence\)\>'
let s:GROUP_CLOSE =
	\ '\<\%(endmodule\|endclass\|endfunction\|endtask\|endinterface\|' .
	\ 'endprogram\|endpackage\|endclocking\|endproperty\|endsequence\|' .
	\ 'endgroup\|endchecker\|endconfig\|endprimitive\|endtable\|' .
	\ 'endgenerate\|endspecify\)\>'
" Stoppers for the default-clocking lookahead: any enclosing-scope
" opener or closer other than endclocking itself, or another
" default clocking line.
let s:DC_STOP =
	\ '\<\%(module\|class\|function\|task\|interface\|program\|package\|' .
	\ 'clocking\|property\|sequence\|covergroup\|checker\|config\|' .
	\ 'primitive\|table\|generate\|specify\|randsequence\|' .
	\ 'endmodule\|endclass\|endfunction\|endtask\|endinterface\|' .
	\ 'endprogram\|endpackage\|endproperty\|endsequence\|' .
	\ 'endgroup\|endchecker\|endconfig\|endprimitive\|endtable\|' .
	\ 'endgenerate\|endspecify\)\>\|\<default\s\+clocking\>'
let s:BLOCK_OPEN  = '\<\%(begin\|case\|casex\|casez\|randcase\|fork\)\>'
let s:BLOCK_CLOSE = '\<\%(end\|endcase\|join\|join_any\|join_none\)\>'
let s:UVM_OPEN    = '`\h\w*_utils_begin\>'
let s:UVM_CLOSE   = '`\h\w*_utils_end\>'

" function/task prototypes never open a fold
" (extern/pure [protected/local/virtual/static/automatic] function/task, DPI-C imports/exports).
" NOTE: s:Scan strips string literals before this test, so the DPI
" forms below match with the "DPI-C" string already removed;
" requiring the quoted string here could never match.
let s:PROTOTYPE =
	\ '^\s*\%(\%(\%(extern\|pure\)\s\+\)\+\%(\%(protected\|local\|virtual\|static\|automatic\)\s\+\)*' .
	\ '\|\%(import\s\+\%(context\s\+\|pure\s\+\)\?\|export\s\+\)\)\%(function\|task\)\>'

" heuristic start of a multi-line instantiation: <type> [#(...)] <inst> (...
" (must not start with a keyword; module parameters/ports often get folded)
let s:INST_DENY =
	\ 'module\|macromodule\|class\|function\|task\|program\|package\|' .
	\ 'interface\|modport\|clocking\|checker\|config\|primitive\|specify\|' .
	\ 'table\|covergroup\|coverpoint\|cross\|bins\|property\|sequence\|' .
	\ 'randsequence\|randcase\|constraint\|if\|else\|for\|foreach\|while\|' .
	\ 'repeat\|forever\|do\|case\|casex\|casez\|begin\|end\|generate\|' .
	\ 'always\|always_comb\|always_ff\|always_latch\|initial\|final\|' .
	\ 'assign\|deassign\|alias\|force\|release\|wait\|disable\|fork\|join\|' .
	\ 'typedef\|struct\|union\|enum\|parameter\|localparam\|specparam\|' .
	\ 'defparam\|import\|export\|extern\|virtual\|pure\|return\|unique\|' .
	\ 'priority\|assert\|assume\|restrict\|expect\|cover\|this\|super\|' .
	\ 'new\|var\|static\|automatic\|genvar\|bind\|interconnect\|nettype\|' .
	\ 'type\|void\|byte\|shortint\|int\|longint\|integer\|time\|real\|' .
	\ 'realtime\|shortreal\|bit\|logic\|reg\|wire\|uwire\|tri\|wand\|wor\|' .
	\ 'string\|event\|chandle\|signed\|unsigned\|rand\|randc\|const\|' .
	\ 'input\|output\|inout\|ref\|cell\|design\|library\|use\|incdir\|' .
	\ 'liblist\|instance\|uvm_\w*'
let s:INST_START =
	\ '^\s*\%(' . s:INST_DENY . '\>\)\@!' .
	\ '\s*\h\w*\%(\s*#\s*([^()]*)\)\?\s\+\h\w*\%(\s*\[[^][]*\]\s*\)\?\s*('

function! s:Count(text, pat) abort
	let l:n = 0
	let l:i = match(a:text, a:pat)
	while l:i >= 0
		let l:n += 1
		let l:i = match(a:text, a:pat, l:i + 1)
	endwhile
	return l:n
endfunction

function! s:Opts() abort
	if exists('b:sv_fold_opts')
		return b:sv_fold_opts
	endif
	let l:o = {'block':0, 'begin_blocks':0, 'comment':0,
	\          'conditional':0, 'define':0, 'instance':0, 'marker':0}
	let l:raw = get(g:, 'systemverilog_syntax_fold', 'default')
	let l:items = type(l:raw) == v:t_list ? copy(l:raw)
	\   : split(l:raw, '\s*,\s*')
	for l:i in l:items
		if l:i ==# 'all'
			for l:k in keys(l:o)
				let l:o[l:k] = 1
			endfor
		elseif l:i ==# 'default'
			let l:o.block = 1
			let l:o.comment = 1
			let l:o.conditional = 1
			let l:o.define = 1
			let l:o.marker = 1
		elseif has_key(l:o, l:i)
			let l:o[l:i] = 1
		endif
	endfor
	let b:sv_fold_opts = l:o
	return l:o
endfunction

" Decide whether a `default clocking` line opens a clocking block (its
" body runs to a later `endclocking`) or is a bare reference /
" declaration. The first line cannot tell them apart: an unnamed block
" opener and an unnamed declaration share the same first line, so the
" verdict comes from the text that follows -- the first `endclocking`
" (block) or enclosing-scope boundary (declaration) wins, scanning at
" most s:DC_CAP lines ahead. Comment/string contents are stripped the
" same way s:Scan strips them, so an `endclocking` inside a comment or
" string never decides. No evidence either way degrades to a
" declaration, which is the historical behavior. Pure function over
" buffer text: never calls s:Scan, result is cached with the scan.
let s:DC_CAP = 200
function! s:DefaultClockingIsBlock(lnum, code, in_comment) abort
	let l:endpat = '\<endclocking\>'
	" same-line tail first: text after the `default clocking` match
	let l:me = matchend(a:code, '\<default\s\+clocking\>')
	let l:tail = l:me >= 0 ? a:code[l:me :] : ''
	let l:ie = match(l:tail, l:endpat)
	let l:is = match(l:tail, s:DC_STOP)
	if l:ie >= 0 && (l:is < 0 || l:ie < l:is)
		return 1
	endif
	if l:is >= 0 && (l:ie < 0 || l:is < l:ie)
		return 0
	endif
	let l:in_comment = a:in_comment
	let l:last = min([line('$'), a:lnum + s:DC_CAP])
	let l:j = a:lnum + 1
	while l:j <= l:last
		let l:t = getline(l:j)
		let l:t = substitute(l:t, "'\\.'", '', 'g')
		let l:t = substitute(l:t, '"\(\\.\|[^"\\]\)*"', '', 'g')
		if l:in_comment
			" inside a block comment // is inert: find the closer
			" before stripping line comments
			if l:t =~# '\*/'
				let l:in_comment = 0
				let l:t = substitute(l:t, '^.\{-}\*/', '', '')
			else
				let l:j += 1
				continue
			endif
		endif
		" complete /* ... */ pairs drop out before // is stripped:
		" a // inside a pair must not eat the closing */
		let l:t = substitute(l:t, '/\*.\{-}\*/', '', 'g')
		let l:t = substitute(l:t, '//.*', '', 'g')
		let l:tc = l:t
		if l:tc =~# '/\*'
			let l:in_comment = 1
			let l:tc = substitute(l:tc, '/\*.*$', '', '')
		endif
		let l:ie = match(l:tc, l:endpat)
		let l:is = match(l:tc, s:DC_STOP)
		if l:ie >= 0 && (l:is < 0 || l:ie < l:is)
			return 1
		endif
		if l:is >= 0 && (l:ie < 0 || l:is < l:ie)
			return 0
		endif
		let l:j += 1
	endwhile
	" no evidence either way: declaration (historical behavior)
	return 0
endfunction

" State-independent scan of one line. Results are cached per changedtick so
" out-of-order foldexpr evaluation can replay the state machine cheaply.
function! s:Scan(lnum) abort
	if !has_key(b:sv_fold_scan, a:lnum)
		let l:o = s:Opts()
		let l:t = getline(a:lnum)

		" strip char literals and strings first
		let l:t = substitute(l:t, "'\\.'", '', 'g')
		let l:t = substitute(l:t, '"\(\\.\|[^"\\]\)*"', '', 'g')

		" manual fold markers (// {{{ / // }}}) live inside comments, so
		" they must be counted before line comments are stripped
		let l:r = {}
		let l:r.mk = l:o.marker
			\   ? (s:Count(l:t, '\V{{{') - s:Count(l:t, '\V}}}'))
			\   : 0

		" complete /* ... */ pairs drop out before line comments are
		" stripped: a // inside a pair must not eat the closing */.
		" The closer test uses the pre-// text: inside a block comment
		" entered on an earlier line, // is inert and */ still closes.
		let l:tp = substitute(l:t, '/\*.\{-}\*/', '', 'g')
		let l:tc = substitute(l:tp, '//.*', '', 'g')
		let l:r.oc = l:tc =~# '/\*' ? 1 : 0
		let l:r.cc = (l:tp =~# '\*/' && !l:r.oc) ? 1 : 0
		let l:code = substitute(l:tc, '/\*.*$', '', '')

		let l:r.bs  = l:code =~# '\\\s*$' ? 1 : 0
		let l:r.def = l:code =~# '^\s*`define\>' ? 1 : 0

		if l:code =~# '^\s*`\s*\%(ifdef\|ifndef\)\>'
			let l:r.cond = 'open'
		elseif l:code =~# '^\s*`\s*\%(elsif\|else\)\>'
			let l:r.cond = 'restart'
		elseif l:code =~# '^\s*`\s*endif\>'
			let l:r.cond = 'close'
		else
			let l:r.cond = ''
		endif

		" code events
		let l:r.net = 0
		let l:r.restart = 0
		if l:code =~# s:PROTOTYPE
			let l:c = ''
		else
			let l:c = substitute(l:code, '\<interface\s\+class\>', 'class', 'g')
			let l:c = substitute(l:c, '\<typedef\s\+class\>', '', 'g')
			if l:o.block && l:c =~# '\<default\s\+clocking\>'
				if s:DefaultClockingIsBlock(a:lnum, l:code, l:r.oc)
					" block opener: keep one GROUP_OPEN hit, strip only `default`
					let l:c = substitute(l:c, '\<default\s\+\zeclocking\>', '', 'g')
				else
					let l:c = substitute(l:c, '\<default\s\+clocking\>', '', 'g')
				endif
			else
				let l:c = substitute(l:c, '\<default\s\+clocking\>', '', 'g')
			endif
			let l:c = substitute(l:c, '\<virtual\s\+interface\s\+\%(class\>\)\@!', '', 'g')
			let l:c = substitute(l:c, '\<\%(disable\|wait\)\s\+fork\>', '', 'g')
			let l:c = substitute(l:c, '\<with\s\+function\s\+sample\>', '', 'g')
			let l:c = substitute(l:c, '\<\%(assert\|assume\|restrict\|cover\)\s\+\%(\%(property\|sequence\)\s\+\)\=', '', 'g')
		endif

		let l:openp = []
		let l:closep = []
		if l:o.block
			call add(l:openp, s:GROUP_OPEN)
			call add(l:openp, s:UVM_OPEN)
			call add(l:closep, s:GROUP_CLOSE)
			call add(l:closep, s:UVM_CLOSE)
		endif
		if l:o.begin_blocks
			call add(l:openp, s:BLOCK_OPEN)
			call add(l:closep, s:BLOCK_CLOSE)
		endif
		let l:OP = join(l:openp, '\|')
		if l:OP !=# ''
			let l:CL = join(l:closep, '\|')
			let l:no = s:Count(l:c, l:OP)
			let l:nc = s:Count(l:c, l:CL)
			let l:r.net = l:no - l:nc
			" a closer before an opener ("end else begin") starts a new
			" fold here at the same level
			if l:no > 0 && l:nc > 0 && match(l:c, l:CL) < match(l:c, l:OP)
				let l:r.restart = 1
			endif
		endif

		if l:o.instance
			let l:r.pd = s:Count(l:code, '(') - s:Count(l:code, ')')
			let l:r.inst = (l:r.pd > 0 && l:code !~# ';\s*$'
				\   && l:code =~# s:INST_START) ? 1 : 0
		else
			let l:r.pd = 0
			let l:r.inst = 0
		endif

		let b:sv_fold_scan[a:lnum] = l:r
	endif
	return b:sv_fold_scan[a:lnum]
endfunction

" Walk one line: consume scan events, update the fold state machine and
" return the foldexpr string for this line.
function! s:Walk(lnum) abort
	let l:o = s:Opts()
	let l:r = s:Scan(a:lnum)
	let l:entry = b:sv_fold_level
	let l:net = 0
	let l:restart = 0

	if b:sv_fold_in_comment
		if l:r.cc
			let b:sv_fold_in_comment = 0
			if l:o.comment
				let l:net -= 1
			endif
		endif
	elseif b:sv_fold_in_define
		if !l:r.bs
			let b:sv_fold_in_define = 0
			if l:o.define
				let l:net -= 1
			endif
		endif
	elseif b:sv_fold_inst_depth > 0
		let b:sv_fold_inst_depth += l:r.pd
		if b:sv_fold_inst_depth <= 0
			let b:sv_fold_inst_depth = 0
			let l:net -= 1
		endif
	else
		if l:r.oc
			let b:sv_fold_in_comment = 1
			if l:o.comment
				let l:net += 1
			endif
		endif
		if l:r.def && l:r.bs
			let b:sv_fold_in_define = 1
			if l:o.define
				let l:net += 1
			endif
		endif
		if l:r.inst
			let b:sv_fold_inst_depth = l:r.pd
			let l:net += 1
		endif
		if l:o.conditional
			if l:r.cond ==# 'open'
				let l:net += 1
			elseif l:r.cond ==# 'restart'
				let l:restart = 1
			elseif l:r.cond ==# 'close'
				let l:net -= 1
			endif
		endif
		" manual // {{{ / // }}} markers fold at the current level
		let l:net += l:r.mk
		let l:net += l:r.net
		let l:restart = l:restart || l:r.restart
	endif

	let l:final = l:entry + l:net
	if l:final < 0
		let l:final = 0
	endif
	let b:sv_fold_level = l:final

	if l:final > l:entry
		return '>' . l:final
	elseif l:restart
		return '>' . l:final
	endif
	return string(l:entry)
endfunction

function! systemverilog#FoldExpr() abort
	if get(b:, 'sv_fold_tick', -1) != b:changedtick
		let b:sv_fold_tick = b:changedtick
		let b:sv_fold_scan = {}
		let b:sv_fold_level = 0
		let b:sv_fold_in_comment = 0
		let b:sv_fold_in_define = 0
		let b:sv_fold_inst_depth = 0
		let b:sv_fold_next = 1
	endif
	let l:lnum = v:lnum
	if l:lnum != b:sv_fold_next
		" Evaluation jumped (Vim may recompute folds from any line):
		" rewind the state and replay from line 1; the scan cache keeps
		" this cheap.
		let b:sv_fold_level = 0
		let b:sv_fold_in_comment = 0
		let b:sv_fold_in_define = 0
		let b:sv_fold_inst_depth = 0
		let l:l = 1
		while l:l < l:lnum
			call s:Walk(l:l)
			let l:l += 1
		endwhile
	endif
	let b:sv_fold_next = l:lnum + 1
	return s:Walk(l:lnum)
endfunction

function! systemverilog#FoldText() abort
	let l:txt = trim(getline(v:foldstart))
	if l:txt =~# '{{{'
		" manual marker fold: show only the user's description
		let l:txt = substitute(l:txt, '^\s*\(\/\/\|\/\*\)\?\s*{{{\d*\s*', '', '')
		if empty(l:txt)
			let l:txt = 'manual fold'
		endif
	else
		let l:txt = substitute(l:txt, '\s*\/\/.*$', '', '')
	endif
	if strlen(l:txt) > 64
		let l:txt = strpart(l:txt, 0, 61) . '...'
	endif
	return '+' . v:folddashes . ' ' . (v:foldend - v:foldstart + 1)
	\   . ' lines: ' . l:txt
endfunction

let &cpoptions = s:cpo_save
unlet s:cpo_save
