" Vim indent file
" Language:	systemverilog
" Maintainer:	sqlmap3 < https://github.com/sqlmap3 >
" Version:	0.1
" First Change:	Sat Dec 06 11:15:30 CST 2025
" Last Change:	Sat Dec 23 21:15:05 CST 2025
if exists("b:did_indent")
	finish
endif

let b:did_indent = 1

setlocal indentexpr=GetSystemVerilogIndent(v:lnum)
setlocal indentkeys&
setlocal indentkeys+==end,=endgenerate,=generate,=join,(,),{,},=`begin_keywords,=`celldefine,=`default_nettype,=`define,=`else,=`elsif,=`end_keywords,=`endcelldefine,=`endif,=`ifdef,=`ifndef,=`include,=`nounconnected_drive,=`pragma,=`resetall,=`timescale,=`unconnected_drive,=`undef,=`undefineall

if exists("*GetSystemVerilogIndent")
	finish
endif

let s:BLOCK_COMMENT_START = '^s.*$'
let s:BLOCK_COMMENT_STOP = '^.*p$'
let s:LINE_COMMENT = '^l$'
let s:GROUP_INDENT_START = 'f'
let s:GROUP_INDENT_STOP = 'h'
let s:BLOCK_INDENT_START = 'b'
let s:BLOCK_INDENT_STOP = 'e'
let s:LINE_INDENT = '^.*x$'
let s:EXEC_LINE = '^.*;$'
let s:PREPROCESSOR = '^z.*$'

"b - 'begin', '(', '{'
"e - 'end', ')', '{'
"f - 'class', 'function', 'task'
"h - 'endclass', 'endfunction', 'endtask'
"l - '//' -- at start of line
"s - '/*' -- start comment
"p - '*/' -- stop comment
"x - 'if', 'else', 'for', 'do, 'while', 'always', 'initial', -- execution commands
" optional arg 1: no-parens mode - ()[]{} are dropped instead of mapped to
" b/e, so unbalanced expression parens do not indent. Used for lines inside
" a backslash continuation block (`define bodies).
function! s:ConvertToCodes( codeline, ... )
	" keywords that don't affect indent: module endmodule package
	" endpackage interface endinterface (upstream nachumk behavior; their
	" bodies are not indented - see README)
	" memoize: the skip loops below re-classify the same (joined) lines many
	" times. Key on changedtick (constant during gg=G) + input + mode.
	if b:sv_conv_tick != b:changedtick
		let b:sv_conv_tick = b:changedtick
		let b:sv_conv_cache = {}
	endif
	let l:key = (a:0 ? '1:' : '0:') . a:codeline
	if has_key(b:sv_conv_cache, l:key)
		return b:sv_conv_cache[l:key]
	endif
	let delims = a:codeline
	" '{'/'}' are blocks only as struct/union/enum/constraint bodies; in a
	" concatenation or literal context (preceded by = ( , ) they must not
	" indent, otherwise a string concatenation spanning lines indents like a
	" struct body and its '}' leaves a dangling block-close. Neutralize
	" those braces (struct body braces are left alone: '{' follows the
	" struct/packed/... word, '}' follows an identifier or string).
	let delims = substitute(delims, '\(=\|(\|,\)\s*{', '\1', 'g')
	let delims = substitute(delims, '}\s*\([,;)]\)', '\1', 'g')
	" UVM field-automation macro pairs behave like block open/close so
	" `uvm_field_* entries indent one level and `..._utils_end dedents.
	" They are mapped to braces here on purpose: the keyword filter below
	" strips bare letters like 'b'/'e', while braces survive it and are
	" converted to b/e by the [({]/[)}] rules further down.
	let delims = substitute(delims, '`\h\w*_utils_begin\>', '{', 'g')
	let delims = substitute(delims, '`\h\w*_utils_end\>', '}', 'g')
	let delims = substitute(delims, '\<\(\%(initial\|always\|always_comb\|always_ff\|always_latch\|final\|begin\|generate\|disable\|if\|extern\|for\|foreach\|do\|while\|forever\|repeat\|randcase\|case\|casex\|casez\|wait\|fork\|ifdef\|ifndef\|else\|elsif\|end\|endgenerate\|endif\|begin_keywords\|celldefine\|default_nettype\|define\|end_keywords\|endcelldefine\|include\|nounconnected_drive\|pragma\|resetall\|timescale\|unconnected_drive\|undef\|undefineall\|endcase\|join\|join_any\|join_none\|class\|config\|clocking\|function\|task\|specify\|covergroup\|pure\|endclass\|endconfig\|endclocking\|endfunction\|endtask\|endspecify\|endgroup\|assume\|assert\|cover\|property\|typedef\|endproperty\|sequence\|checker\|endsequence\|endchecker\)\>\)\@!\k\+', '', 'g')
	let delims = substitute(delims, 'wait\s\+fork', '', 'g')
	let delims = substitute(delims, 'disable\s\+fork', '', 'g')
	let delims = substitute(delims, 'pure\s*\%(\/\*.\{-}\*\/\s*\)*function', '', 'g')
	let delims = substitute(delims, 'extern\s*\%(\/\*.\{-}\*\/\s*\)*function', '', 'g')
	let delims = substitute(delims, 'pure\s*\%(\/\*.\{-}\*\/\s*\)*task', '', 'g')
	let delims = substitute(delims, 'extern\s*\%(\/\*.\{-}\*\/\s*\)*task', '', 'g')
	" keywords the filter keeps but that map to no code: strip the leftovers,
	" otherwise the bare word leaks into the codes and its letters accidentally
	" match the single-letter code patterns (e.g. "extern" contains 'e' and
	" 'x', acting as a spurious block-stop and mis-dedenting a following
	" "function ..." declaration that was split onto its own line)
	let delims = substitute(delims, '\<extern\>', '', 'g')
	let delims = substitute(delims, '\<pure\>', '', 'g')
	let delims = substitute(delims, '\<disable\>', '', 'g')
	let delims = substitute(delims, '\<wait\>', '', 'g')
	let delims = substitute(delims, '\<alias\>', '', 'g')
	let delims = substitute(delims, '\<final\>', '', 'g')
	let delims = substitute(delims, 'typedef\s\+class', '', 'g')
	let delims = substitute(delims, 'typedef', '', 'g')
	let delims = substitute(delims, 'assert\s\+\%\[\(property\)\]', '', 'g')
	let delims = substitute(delims, 'assume\s\+\%\[\(property\)\]', '', 'g')
	let delims = substitute(delims, 'cover\s\+\%\[\(property\)\]', '', 'g')
	let delims = substitute(delims, '`\s*\<\(begin_keywords\|celldefine\|default_nettype\|define\|else\|elsif\|end_keywords\|endcelldefine\|endif\|ifdef\|ifndef\|include\|nounconnected_drive\|pragma\|resetall\|timescale\|unconnected_drive\|undef\|undefineall\)\>', 'z', 'g')
	let delims = substitute(delims, '\<\(begin\|generate\|randcase\|case\|casex\|casez\|fork\)\>', 'b', 'g')
	let delims = substitute(delims, '\<\(end\|endgenerate\|endcase\|join\|join_any\|join_none\)\>', 'e', 'g')
	let delims = substitute(delims, '\<\(class\|config\|clocking\|function\|task\|specify\|covergroup\|property\|sequence\|checker\)\>', 'f', 'g')
	let delims = substitute(delims, '\<\(endclass\|endconfig\|endclocking\|endfunction\|endtask\|endspecify\|endgroup\|endproperty\|endsequence\|endchecker\)\>', 'h', 'g')
	let delims = substitute(delims, '\<\(if\|for\|foreach\|do\|while\|forever\|repeat\|always\|always_comb\|always_ff\|always_latch\|initial\)\>', 'x', 'g')
	" 'else' is a control statement ('x') so a statement on the next line
	" indents one level, and the dedent rule (prev2 x + prev1 exec) can also
	" fire for end/endfunction/endtask that follow an else-branch.
	" 'assert' stays a statement terminator (lower priority, per README).
	let delims = substitute(delims, '\<assert\>', ';', 'g')
	let delims = substitute(delims, '\<else\>', 'x', 'g')
	let delims = substitute(delims, '^\s*\/\/.*$', 'l', 'g')
	let delims = substitute(delims, '\/\/.*', '', 'g')
	let delims = substitute(delims, '\".\{-}\(\\\)\@<!\"', '', 'g')
	let delims = substitute(delims, '\/\*', 's', 'g')
	let delims = substitute(delims, '\*\/', 'p', 'g')
	let delims = substitute(delims, '\[[^:\[\]]*:[^:\[\]]*\]', '', 'g')
	let delims = substitute(delims, '\@', 'x', 'g')
	if a:0
		let delims = substitute(delims, '[][(){}]', '', 'g')
	else
		let delims = substitute(delims, '[({]', 'b', 'g')
		let delims = substitute(delims, '[)}]', 'e', 'g')
	endif
	let delims = substitute(delims, '^\s*`.*$', ';', 'g')
	let delims = substitute(delims, '[/@<=#,\.\$]*', '', 'g')
	let delims = substitute(delims, '\s', '', 'g')
	let delims = substitute(delims, '^o\+:', 'x', 'g')
	let delims = substitute(delims, ':', '', 'g')
	let delims = substitute(delims, 'x\+', 'x', 'g')
	let delims = substitute(delims, 'o\+', 'o', 'g')
	while (match(delims, '\(b[^be]*e\)') != -1)
		let delims = substitute(delims, '\(b[^be]*e\)', '', 'g')
	endwhile
	while (match(delims, '\(f[^fh]*h\)') != -1)
		let delims = substitute(delims, '\(f[^fh]*h\)', '', 'g')
	endwhile
	while (match(delims, '\(s[^sp]*p\)') != -1)
		let delims = substitute(delims, '\(s[^sp]*p\)', '', 'g')
	endwhile
	let b:sv_conv_cache[l:key] = delims
	return delims
endfunction

function! s:GetPrevWholeLineNum ( line_num )
	if b:sv_conv_tick != b:changedtick
		let b:sv_conv_tick = b:changedtick
		let b:sv_conv_cache = {}
		let b:sv_prev_cache = {}
		let b:sv_whole_cache = {}
	endif
	if has_key(b:sv_prev_cache, a:line_num)
		return b:sv_prev_cache[a:line_num]
	endif
	let prev1_line_num = prevnonblank( a:line_num - 1)
	let prev2_line_num = prev1_line_num - 1
	let prev2_codeline = getline( prev2_line_num )
	while ( strpart( prev2_codeline , strlen(prev2_codeline) - 1 , 1) == '\' )
		let prev1_line_num = prev1_line_num - 1
		let prev2_line_num = prev1_line_num - 1
		let prev2_codeline = getline( prev2_line_num )
	endwhile

	let b:sv_prev_cache[a:line_num] = prev1_line_num
	return prev1_line_num
endfunction

function! s:GetWholeLine ( line_num )
	if b:sv_conv_tick != b:changedtick
		let b:sv_conv_tick = b:changedtick
		let b:sv_conv_cache = {}
		let b:sv_prev_cache = {}
		let b:sv_whole_cache = {}
	endif
	if has_key(b:sv_whole_cache, a:line_num)
		return b:sv_whole_cache[a:line_num]
	endif
	let line_num = a:line_num
	let codeline = getline( line_num )
	while ( strpart( codeline , strlen(codeline) - 1 , 1) == '\' )
		let line_num = line_num + 1
		let codeline = strpart( codeline , 0 , strlen( codeline ) - 2 ) . " " . getline (line_num)
	endwhile

	let b:sv_whole_cache[a:line_num] = codeline
	return codeline
endfunction

function! s:GetCodeIndent ( indnt, prev2_codes, prev1_codes, this_codes )
	let indnt = a:indnt
	if a:prev2_codes =~ s:LINE_INDENT && a:prev1_codes =~ s:EXEC_LINE
		let indnt = indnt - &shiftwidth
	endif

	if a:prev1_codes =~ s:GROUP_INDENT_START
		let indnt = indnt + &shiftwidth
	endif

	if a:this_codes =~ s:GROUP_INDENT_STOP
		return indnt - &shiftwidth
	endif

	if a:prev1_codes =~ s:BLOCK_INDENT_START
		let indnt = indnt + &shiftwidth
	endif
	if a:this_codes =~ s:BLOCK_INDENT_STOP
		return indnt - &shiftwidth
	endif

	if a:prev1_codes =~ s:LINE_INDENT && a:prev1_codes !~ s:BLOCK_INDENT_START
		let indnt = indnt + &shiftwidth
		if a:this_codes =~ s:LINE_INDENT || a:this_codes =~ s:BLOCK_INDENT_START
			let indnt = indnt - &shiftwidth
		endif
	endif

	return indnt
endfunction

" Return the line number of the `ifdef/`ifndef that a `else/`elsif/`endif at
" a:line_num matches, walking back through nested conditionals (comments and
" plain code are skipped), or 0 if none (an unbalanced/standalone directive).
function! s:FindIfdefMatch( line_num )
	let l:depth = 0
	let l:ln = prevnonblank(a:line_num - 1)
	while l:ln > 0
		let l:line = getline(l:ln)
		if l:line =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/'
			let l:ln = prevnonblank(l:ln - 1)
			continue
		endif
		if l:line =~ '^\s*`\s*\cendif\>'
			let l:depth += 1
			let l:ln = prevnonblank(l:ln - 1)
			continue
		endif
		if l:line =~ '^\s*`\s*\c\(ifdef\|ifndef\)\>'
			if l:depth == 0
				return l:ln
			endif
			let l:depth -= 1
			let l:ln = prevnonblank(l:ln - 1)
			continue
		endif
		" plain code or other preprocessor directive: keep walking up
		let l:ln = prevnonblank(l:ln - 1)
	endwhile
	return 0
endfunction

" Indent for a preprocessor conditional line (`ifdef/`ifndef/`elsif/`else/
" `endif): align it with the enclosing code, matching the UVM library style
" where a nested `ifdef sits one level deeper than its enclosing code and
" `else/`elsif/`endif align with their matching `ifdef. The top-level file
" guard (`ifndef ..._SVH at column 0) falls through to the base indent (0).
function! s:GetPreprocIndent( line_num, base_indnt )
	let l:ln = prevnonblank(a:line_num - 1)
	if getline(a:line_num) =~ '^\s*`\s*\c\(ifdef\|ifndef\)\>'
		" opener: sit at the code level, one deeper per enclosing ifdef
		let l:nest = 0
		while l:ln > 0
			let l:line = getline(l:ln)
			if l:line =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/'
				let l:ln = prevnonblank(l:ln - 1)
				continue
			endif
			if l:line =~ '^\s*`\s*\cendif\>'
				let l:nest -= 1
			elseif l:line =~ '^\s*`\s*\c\(ifdef\|ifndef\)\>'
				let l:nest += 1
			elseif l:line =~ '^\s*`'
				" other preprocessor directive - transparent
			else
				break
			endif
			let l:ln = prevnonblank(l:ln - 1)
		endwhile
		return a:base_indnt + (l:nest > 0 ? l:nest * &shiftwidth : 0)
	endif
	" closer (`else/`elsif/`endif): align with the matching `ifdef
	let l:m = s:FindIfdefMatch(a:line_num)
	return l:m > 0 ? indent(l:m) : a:base_indnt
endfunction

let b:in_block_comment = 0
" must exist before GetSystemVerilogIndent() compares them, otherwise the
" first indent evaluation in a fresh buffer aborts with E121
let b:block_comment_change = 0
let b:block_comment_line = 0
" memoization for s:ConvertToCodes(): it is a pure function, yet the
" comment/preprocessor skip loops re-classify the same (joined) lines over
" and over (O(n^2) on macro-heavy files). The cache is keyed on changedtick,
" which does not change during a whole-buffer re-indent (gg=G computes every
" indent against the same buffer state before applying), so the cache is
" reused across the whole pass and reset on the next real edit.
let b:sv_conv_cache = {}
let b:sv_prev_cache = {}
let b:sv_whole_cache = {}
let b:sv_conv_tick = -1

" A function/task whose signature sits on a line after a bare qualifier line
" (extern / pure / virtual / protected ... with no ';') is a split prototype:
" its group opener 'f' must not stay open past the signature's closing ');',
" or every following declaration cascades one level deeper. Strip the 'f'.
function! s:StripPrototypeF( line_num, codeline, codes )
	if a:codeline =~ '^\s*\%(\%(virtual\|pure\|static\|automatic\|local\)\s\+\)*\%(function\|task\)\>'
		let l:prev = getline(prevnonblank(a:line_num - 1))
		if l:prev =~ '^\s*\%(extern\|virtual\|protected\|pure\|static\|local\)\%(\s\+\%(extern\|virtual\|protected\|pure\|static\|local\)\)*\s*$'
			return substitute(a:codes, 'f', '', 'g')
		endif
	endif
	return a:codes
endfunction

" If the line at a:line_num is the tail of a multi-line macro call (a line
" ending in ')' or ');' whose continuation chain of ', ( [ {'-ending lines
" reaches a backtick line), return that macro head's line number; otherwise
" return 0. A real multi-line call/declaration (extern function ...( ... );)
" has no backtick in the chain and returns 0.
function! s:MacroTailHead( line_num )
	let l:line = getline(a:line_num)
	if l:line !~ ')\s*;\?\s*$'
		return 0
	endif
	if l:line =~ '^\s*[;)}]'
	  \ || l:line =~ '^\s*\%(end\|endcase\|endgenerate\|endmodule\|endinterface\|endpackage\|endclass\|endfunction\|endtask\|endgroup\|endproperty\|endsequence\|endchecker\|endconfig\|endclocking\|endspecify\|join\|join_any\|join_none\)\>'
		return 0
	endif
	let l:ln = prevnonblank(a:line_num - 1)
	while l:ln > 0
		let l:l = getline(l:ln)
		if l:l !~ '[,([{]\s*$'
			return 0
		endif
		if l:l =~ '^\s*`'
			return l:ln
		endif
		let l:ln = prevnonblank(l:ln - 1)
	endwhile
	return 0
endfunction

function! GetSystemVerilogIndent( line_num )
	let this_codeline = getline( a:line_num )
	let prev1_line_num = prevnonblank( a:line_num - 1)
	let prev1_codeline = getline( prev1_line_num )
	let prev2_line_num = prev1_line_num - 1
	let prev2_codeline = getline( prev2_line_num )

	let indnt = indent( prev1_line_num )

	if ( strpart( prev1_codeline , strlen(prev1_codeline) - 1 , 1) == '\' )
		if ( strpart( prev2_codeline , strlen(prev2_codeline) - 1 , 1) == '\' )
			" middle of a backslash continuation block (a multi-line
			" `define body): keep the previous line's level, adjusted only
			" by the keyword structure of the surrounding lines. Parens are
			" ignored so an expression split across lines stays flat
			" (`define HALF(a,b) ((a) + \ (b))), while begin/if/end still
			" indent (`define uvm_info ... begin \ if (...) \ ...).
			let p1 = substitute(prev1_codeline, '\\\s*$', '', '')
			let p2 = substitute(prev2_codeline, '\\\s*$', '', '')
			let pc1 = s:ConvertToCodes(p1, 1)
			let pc2 = s:ConvertToCodes(p2, 1)
			let tc  = s:ConvertToCodes(substitute(this_codeline, '\\\s*$', '', ''), 1)
			return s:GetCodeIndent( indent( prev1_line_num ), pc2, pc1, tc )
		else
			return indnt + &shiftwidth
		endif
	else
		if ( strpart( prev2_codeline , strlen(prev2_codeline) - 1 , 1) == '\' )
			let indnt = indnt - &shiftwidth
		endif
	endif
	if this_codeline =~ '^\s*`\s*\cinclude\>'
		let ln = prevnonblank(a:line_num - 1)
		while ln > 0
			let l = getline(ln)
			if l =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/'
				let ln = prevnonblank(ln - 1)
				continue
			endif
			if l =~ '^\s*`\s*\cendif\>'
				let l:m = s:FindIfdefMatch(ln)
				if l:m > 0
					return indent(l:m)
				endif
				break
			endif
			if l =~ '^\s*`\s*\c\(ifdef\|ifndef\|elsif\)\>'
				return indent(ln) + &shiftwidth
			endif
			if l =~ '^\s*`\s*\cinclude\>'
				let ln = prevnonblank(ln - 1)
				continue
			endif
			break
		endwhile
	endif
	if this_codeline !~ '^\s*`'
		let ln = prevnonblank(a:line_num - 1)
		while ln > 0
			let l = getline(ln)
			if l =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/\|^\s*`\s*\cinclude\>'
				let ln = prevnonblank(ln - 1)
				continue
			endif
			if l =~ '^\s*`\s*\cendif\>'
				let l:m = s:FindIfdefMatch(ln)
				if l:m > 0
					return indent(l:m)
				endif
				break
			endif
			if l =~ '^\s*`\s*\c\(ifdef\|ifndef\|elsif\)\>'
				return indent(ln) + &shiftwidth
			endif
			break
		endwhile
	endif
	if this_codeline =~ '^\s*//'
		let ln = prevnonblank(a:line_num - 1)
		while ln > 0
			let l = getline(ln)
			if l =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/'
				let ln = prevnonblank(ln - 1)
				continue
			endif
			if l =~ '^\s*`\s*\cendif\>'
				let l:m = s:FindIfdefMatch(ln)
				if l:m > 0
					return indent(l:m)
				endif
				break
			endif
			if l =~ '^\s*`\s*\c\(ifdef\|ifndef\|elsif\)\>'
				return indent(ln) + &shiftwidth
			endif
			if l =~ '^\s*`\s*\cinclude\>'
				let ln = prevnonblank(ln - 1)
				continue
			endif
			break
		endwhile
	endif

	let prev1_line_num = s:GetPrevWholeLineNum (a:line_num)
	let prev1_for_comment_line = prev1_line_num
	let prev1_codeline = s:GetWholeLine (prev1_line_num)
	let prev1_codes = s:ConvertToCodes(prev1_codeline)
	let in_comment = 0
	while ( prev1_codes =~ s:LINE_COMMENT || in_comment || prev1_codes =~ s:BLOCK_COMMENT_STOP || prev1_codes =~ s:BLOCK_COMMENT_START || prev1_codes =~ s:PREPROCESSOR)
		if (prev1_codes =~ s:BLOCK_COMMENT_STOP)
			let in_comment = 1
		endif
		if (prev1_codes =~ s:BLOCK_COMMENT_START)
			let in_comment = 0
		endif
		let prev1_line_num = s:GetPrevWholeLineNum (prev1_line_num)
		let prev1_codeline = s:GetWholeLine (prev1_line_num)
		let prev1_codes = s:ConvertToCodes(prev1_codeline)
	endwhile

	let prev2_line_num = s:GetPrevWholeLineNum (prev1_line_num)
	let prev2_codeline = s:GetWholeLine (prev2_line_num)
	let prev2_codes = s:ConvertToCodes(prev2_codeline)
	let in_comment = 0
	while ( prev2_codes =~ s:LINE_COMMENT || in_comment || prev2_codes =~ s:BLOCK_COMMENT_STOP || prev2_codes =~ s:BLOCK_COMMENT_START || prev2_codes =~ s:PREPROCESSOR)
		if (prev2_codes =~ s:BLOCK_COMMENT_STOP)
			let in_comment = 1
		endif
		if (prev2_codes =~ s:BLOCK_COMMENT_START)
			let in_comment = 0
		endif
		let prev2_line_num = s:GetPrevWholeLineNum (prev2_line_num)
		let prev2_codeline = s:GetWholeLine (prev2_line_num)
		let prev2_codes = s:ConvertToCodes(prev2_codeline)
	endwhile

	let prev1_codes = s:StripPrototypeF(prev1_line_num, prev1_codeline, prev1_codes)
	let prev2_codes = s:StripPrototypeF(prev2_line_num, prev2_codeline, prev2_codes)

	" if prev1 is the tail of a multi-line macro, it is the statement's
	" terminator: treat it as 'exec' and resolve prev2 to the code before the
	" macro head, so the "prev2 x + prev1 exec" rule dedents the next line
	" back to the enclosing control level (e.g. a following if/endfunction)
	let l:mhead = s:MacroTailHead(prev1_line_num)
	if l:mhead > 0
		let prev1_codes = ';'
		let prev2_line_num = s:GetPrevWholeLineNum(l:mhead)
		let prev2_codeline = s:GetWholeLine(prev2_line_num)
		let prev2_codes = s:ConvertToCodes(prev2_codeline)
	endif

	let this_codes = s:ConvertToCodes( this_codeline )
	let this_codes = s:StripPrototypeF(a:line_num, this_codeline, this_codes)

	" Tail of a multi-line MACRO call, e.g. the closing "UVM_LOW)" or
	" "actual, exp),UVM_DEBUG);" line of a `uvm_info that spans lines without
	" backslash continuation. The macro's open line is wiped to ';' by
	" ConvertToCodes, so the tail's ')' has no matching '(' and would dedent
	" spuriously and cascade. Keep the tail flat with the macro head.
	let l:mhead = s:MacroTailHead(a:line_num)
	if l:mhead > 0
		return indent(l:mhead)
	endif

	let indnt = indent( prev1_line_num )

	let indnt = s:GetCodeIndent ( indnt, prev2_codes, prev1_codes, this_codes)

	if this_codes =~ s:BLOCK_COMMENT_STOP || b:block_comment_change != b:changedtick || b:block_comment_line != prev1_for_comment_line
		let b:in_block_comment = 0
	endif
	if this_codes =~ s:BLOCK_COMMENT_STOP
		return indent (a:line_num)
	endif
	if this_codes =~ s:BLOCK_COMMENT_START
		let b:in_block_comment = 1
		let b:block_comment_line = a:line_num
		let b:block_comment_change = b:changedtick
		return indnt
	endif
	if b:in_block_comment
		let b:block_comment_line = a:line_num
		return indent (a:line_num)
	endif

	if a:line_num == 1
		return 0
	endif
	if (this_codes =~ s:PREPROCESSOR)
		return s:GetPreprocIndent(a:line_num, indnt)
	endif
	if (this_codes =~ s:LINE_COMMENT)
		return indnt
	endif

	return indnt
endfunction
