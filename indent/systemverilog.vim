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

" A line opens a block comment when an 's' code survives anywhere in
" its codes: the s[^sp]*p cancel loop in s:ConvertToCodes removes complete
" pairs, so a leftover 's' is an unterminated '/*' even with
" code before it on the line ("y = 2; /* open" codes ';s').
" Anchoring at '^s' missed mid-line openers, so comment text below
" them (an 'end' inside the comment) was counted as code, and the
" slow-path skip loop walked past line 1 forever (demo100).
let s:BLOCK_COMMENT_START = 's'
let s:BLOCK_COMMENT_STOP = '^.*p$'
" a line closes a block comment when a leftover "p" has no
" later "s" on the line: code after "*/" ("*/ begin",
" "*/ x = 1;") still ends the comment (demo103). The strict
" STOP above stays for lines that ARE the close (their
" indent is kept); STOP_ANY only clears comment state.
let s:BLOCK_COMMENT_STOP_ANY = 'p[^s]*$'
" structural code letters in ConvertToCodes output (b/e/f/h/x/;).
" Codes also carry punctuation residue verbatim (a doc-comment
" opener codes as "s*", a close as "*p"), so "carries code" must
" test for these letters, never for any non-marker character.
let s:CODE_LETTER = '[befhx;]'
let s:LINE_COMMENT = '^l$'
let s:GROUP_INDENT_START = 'f'
let s:GROUP_INDENT_STOP = 'h'
let s:BLOCK_INDENT_START = 'b'
let s:BLOCK_INDENT_STOP = 'e'
let s:LINE_INDENT = '^.*x[sp]*$'
let s:EXEC_LINE = '^.*;[sp]*$'
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
" True if the line is a plain statement whose ConvertToCodes result is
" exactly ';' (see the ConvertToCodes fast path). Conservative: any
" doubt returns 0 and the caller falls through to the full path.
function! s:IsPlainStmt( line )
	" Fail fast: most lines have no trailing ';' at all. The big keyword
	" regex runs last, only for lines that passed every cheap check.
	if stridx(a:line, ';') < 0 || a:line !~# ';\s*$'
		return 0
	endif
	if a:line =~# '^\s*\(//\|/\*\)'
		return 0
	endif
	if stridx(a:line, '`') >= 0 || stridx(a:line, '"') >= 0
		return 0
	endif
	if stridx(a:line, '@') >= 0 || stridx(a:line, '{') >= 0 || stridx(a:line, '}') >= 0
		return 0
	endif
	if stridx(a:line, '/*') >= 0 || stridx(a:line, '*/') >= 0
		return 0
	endif
	if count(a:line, '(') != count(a:line, ')') || count(a:line, '[') != count(a:line, ']')
		return 0
	endif
	if a:line =~# '\<\(if\|for\|foreach\|do\|while\|forever\|repeat\|begin\|end\|function\|endfunction\|task\|endtask\|class\|endclass\|case\|casex\|casez\|endcase\|fork\|join\|join_any\|join_none\|generate\|endgenerate\|module\|endmodule\|always\|always_comb\|always_ff\|always_latch\|initial\|final\|typedef\|import\|export\|extern\|pure\|covergroup\|endgroup\|property\|endproperty\|sequence\|endsequence\|checker\|endchecker\|clocking\|endclocking\|specify\|endspecify\|config\|endconfig\|interface\|endinterface\|package\|endpackage\|primitive\|endprimitive\|table\|endtable\|randcase\|randsequence\|assert\|assume\|cover\|restrict\|disable\|wait\|wait_order\|return\|break\|continue\|else\|elsif\)\>'
		return 0
	endif
	return 1
endfunction

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
	" Fast path: plain statement -> codes ';'. A simple statement with
	" no control keyword, no unbalanced delimiter, no directive, no
	" string, no clocking event, not comment-only, and terminated by
	" ';' comes out of the full pipeline as just ';' (balanced parens
	" cancel, identifiers/operators are stripped, stray digits/symbols
	" do not match any code pattern). Detect it with C-level stridx /
	" count plus two small regexes instead of ~40 substitutes. Any
	" doubt falls through to the full path below.
	if stridx(a:codeline, '`') < 0 && stridx(a:codeline, '"') < 0
			\ && stridx(a:codeline, '@') < 0 && stridx(a:codeline, '{') < 0
			\ && stridx(a:codeline, '}') < 0
			\ && stridx(a:codeline, '/*') < 0 && stridx(a:codeline, '*/') < 0
			\ && count(a:codeline, '(') == count(a:codeline, ')')
			\ && count(a:codeline, '[') == count(a:codeline, ']')
			\ && a:codeline =~# ';\s*$' && a:codeline !~# '^\s*\(//\|/\*\)'
			\ && a:codeline !~# '\<\(if\|for\|foreach\|do\|while\|forever\|repeat\|begin\|end\|function\|endfunction\|task\|endtask\|class\|endclass\|case\|casex\|casez\|endcase\|fork\|join\|join_any\|join_none\|generate\|endgenerate\|module\|endmodule\|always\|always_comb\|always_ff\|always_latch\|initial\|final\|typedef\|import\|export\|extern\|pure\|covergroup\|endgroup\|property\|endproperty\|sequence\|endsequence\|checker\|endchecker\|clocking\|endclocking\|specify\|endspecify\|config\|endconfig\|interface\|endinterface\|package\|endpackage\|primitive\|endprimitive\|table\|endtable\|randcase\|randsequence\|assert\|assume\|cover\|restrict\|disable\|wait\|wait_order\|return\|break\|continue\|else\|elsif\)\>'
		let b:sv_conv_cache[l:key] = ';'
		return ';'
	endif
	let delims = a:codeline
	" '{'/'}' are blocks only as struct/union/enum/constraint bodies; in a
	" string-concatenation or literal context they must not indent. A
	" concatenation '{' sits after = ( , ? : ' (the last is the assignment
	" pattern '{) or at the start of a continuation line, and is followed by
	" a string, identifier or system task ($display in a randsequence
	" action, "first : { $display(...); };" — without the '$' the '{' is
	" kept while its '}' is dropped as a statement close, leaving an
	" unmatched 'b', demo12); its '}' is preceded by a string, identifier or
	" call close (spaces allowed) and followed by , ; ) : or an operator
	" (& | ^ + - * / % = < > ! ? — a concatenation used in an expression,
	" "({$random, $random} & ~mask)", its '}' is followed by '&', not by a
	" terminator; a real block-close '}' is never followed by an operator on
	" the same line, so widening the suffix cannot drop one). A ternary concat
	" "? {a}:{b};" has both brace pairs in one line). A '}' preceded by ';'
	" is also dropped: it closes a statement block whose '{' the rule above
	" dropped (a randsequence action, "first: {val++;} ;" — the '{' follows
	" ':' so it was dropped as a concatenation, but the '}' follows a
	" statement, not an expression; leaving it makes an unmatched 'e' that
	" dedents every following line, demo44). A real struct/enum/constraint
	" '}' preceded by ';' is never followed by , ; ) : on the same line, so
	" it is unaffected. The '{' follow class and the '}' prefix class both
	" include digits, so a concatenation whose first element is an
	" identifier and whose last is a based literal ("{sig, 2'b0, 4'b0}")
	" drops BOTH braces: dropping only the '{' leaves an unmatched 'e'
	" that dedents the line and everything after it (rlaphy_env.sv
	" else-begin call, 2026-11-09). Bins/range literals ({0}, {8'hF0},
	" {[0:15]}) likewise drop both braces (their '{' is followed by a
	" digit or '[' and their '}' is preceded by a digit or ']'), so they
	" stay balanced. A digit after '{' is NOT dropped when it is a
	" replication count ("{2{data}}"): the digit must not be followed by
	" more digits and then '{', or the outer '{' would be dropped while
	" its '}' (preceded by ']' or '}') is kept (demo67). This must run
	" BEFORE the string strip (the '"' operand boundary distinguishes a
	" concatenation from a bins value). NOTE: the classes must be spelled
	" [A-Za-z_"] etc - inside a [] collection \h means the two literal
	" characters '\' and 'h', not head-of-word.
	" 'dist {...}' and 'intersect {...}' sets: the '{' follows a keyword,
	" not = ( , : ? ', so the concatenation '{' rule below does not drop
	" it — but the '}' rule does drop a '}' preceded by a digit, leaving
	" an unmatched 'b' that over-indents everything after (demo3,
	" demo9, demo11, demo46). Drop the '{' here when followed by a digit
	" (not a replication count) or an identifier, same follow class as
	" below. 'inside'/'unique' sets are dropped whole by their own rules.
	" A '}' preceded by ']' is dropped too (a concatenation ending in a
	" bit-select, "{sig[1], sig[0]}", whose '{' was dropped as a
	" concatenation but whose '}' the digit-only prefix kept, leaving an
	" unmatched 'e' — rlaphy_env.sv 1496/1497, 2026-11-09); the matching
	" '{' for a range literal "{[0:15]}" is dropped as well (its follow
	" class gains '['), so the pair stays balanced either way.
	" 'return {' is the same shape: a concatenation returned as an
	" expression (demo102).
	let delims = substitute(delims, '\<\(dist\|intersect\|return\)\s*{\ze\s*\(\d\(\d*\s*{\)\@!\|\[\|[A-Za-z_"$''(~!+`-]\)', '\1', 'g')
	" Streaming operators ({<<{...}}, {>>{...}}) open a brace pair whose
	" inner '{' must survive as a block code: the outer '{' is kept
	" (followed by '<'/'>', outside the gate follow class) and
	" both '}'s are kept, so 'bbee' cancels to nothing. If the
	" gate below dropped the inner '{' (it follows '<'/'>'), one
	" 'e' would leak (demo52). Rewrite the inner '{' to '('
	" (the same 'b' code) to a fixpoint, so nested streaming is
	" protected level by level.
	let l:stream_pat = '[{(]\s*\(<<\|>>\)\s*\zs{'
	while delims =~ l:stream_pat
		let delims = substitute(delims, l:stream_pat, '(', '')
	endwhile
	" The '{' gate also covers operators: a '{' after + - * / %
	" & | ^ < > ~ ! is an expression operand (a concatenation), never
	" a block (demo102).
	let delims = substitute(delims, '\([=,(+*/%&|^<>~!-]\|[:?]\|''\)\s*{\ze\s*\(\d\(\d*\s*{\)\@!\|\[\|[A-Za-z_"$''(~!+`-]\)', '\1', 'g')
	let delims = substitute(delims, '^\s*{\ze\s*\(\d\(\d*\s*{\)\@!\|\[\|[A-Za-z_"$''(~!+`-]\)', '', 'g')
	" The '{' follow class also includes ' (an unsized based literal
	" first element, "{'h0, sig[0]}"): without it the '{' is kept
	" while the '}' is dropped, leaving an unmatched 'b' that
	" over-indents every following line (demo96).
	" The class also covers expression starters (, ~, !, +, backtick, -;
	" nested concat {{x}, y} still leaks (pairing gap, not widened).
	" based literals (8'hFF, 4'b10X1, 'd42) are number digits, not an
	" identifier that ends a concatenation: drop the radix+digits so the
	" closing '}' of a bins value set sees a plain digit and stays
	let delims = substitute(delims, '''[sSdDbBhHoO]\h\+', '', 'g')
	" 'inside {...}' and 'unique {...}' sets must be dropped BEFORE the
	" concatenation '}' drop below, or that drop eats the set's closing
	" '}' (preceded by an identifier, followed by ')') and leaves an
	" unmatched '{' -> 'b' in the codes, which breaks LINE_INDENT
	" matching for the 'if' line and makes a following 'end' dedent
	" only one level. The set may contain string literals: the group
	" matches either one non-brace non-quote char or one whole "..."
	" string, so a "}" inside a string does not end the set early.
	" 'unique' takes the same set form in a constraint
	" ("unique {val, mode};") and its '{' is not dropped by the
	" concatenation rule (it follows an identifier, not = ( , : ? '),
	" while its '}' IS dropped, leaving the same unmatched 'b'
	" (demo70).
	let delims = substitute(delims, '\<\(inside\|unique\)\s\+{\%([^}"]\|"[^"]*"\)*}', '', 'g')
	let delims = substitute(delims, '\([]A-Za-z_0-9");]\)\s*\zs}\ze\s*\([,;):&|^+\-*/%=<>!?.]\)', '', 'g')
	" A concatenation '}' before '[' or ']'
	" ("{a, b}[i]", "foo[{a, b}]") must drop exactly
	" when its '{' was dropped above: the '{' drops run
	" first, so a '{' still standing before the '}' (a
	" replication or a kept nested '{') means the '}' must
	" stay paired with it. The tempered gap walks back from the
	" '}' to the line start or a previous '}' without
	" crossing a '{'; one '}' per pass, to a fixpoint (demo98).
	if delims =~ '}\s*[\[\]]'
		let l:pair_pat = '\(^\|}\)\%(\({\)\@!.\)\{-}\([]A-Za-z_0-9");]\)\s*\zs}\ze\s*[\[\]]'
		while delims =~ l:pair_pat
			let delims = substitute(delims, l:pair_pat, '', '')
		endwhile
	endif
	" strip string literals early: keywords, comment markers and braces
	" inside strings ("class foo", "/*", "-> {") must not disturb the
	" classification below (the later strip becomes a no-op)
	let delims = substitute(delims, '"\(\\.\|[^"\\]\)*"', '', 'g')
	" set-membership 'inside {...}' and constraint 'unique {...}' are
	" expressions, not blocks: drop them whole (after the string strip,
	" so text inside a string cannot trigger it and eat a real brace
	" beyond the closing quote)
	let delims = substitute(delims, '\<\(inside\|unique\)\s\+{[^}]*}', '', 'g')
	" context strips that must run BEFORE the keyword filter (their leading
	" word - import/default - is not in the keep-list and is removed by the
	" filter): a DPI import's function/task is the imported symbol kind, not
	" a definition; a default clocking reference is not a block. There are
	" three 'default clocking' forms and the strip must tell them apart:
	" (1) reference "default clocking cb;" — no block, strip it;
	" (2a) definition "default clocking [@name] @(event); ... endclocking"
	" — a real block, do NOT strip (its body indents, endclocking closes);
	" (2b) declaration "default clocking @(event);" with no endclocking —
	" no block, strip it. The '@' rule below strips (2b) but also (2a)
	" without a name, whose endclocking then closes the enclosing group
	" (demo47's checker); the single-line rule first removes a whole
	" "default clocking ...; endclocking" line, and the identifier rule
	" strips (1). Multi-line (2a) without a name is still a known gap:
	" its endclocking closes the enclosing group (no 'default clocking'
	" appears in UVM/VIP, so it is untested in real code).
	let delims = substitute(delims, 'import[^\n]*function', '', 'g')
	let delims = substitute(delims, 'import[^\n]*task', '', 'g')
	" same for a DPI export ("export \"DPI-C\" function sv_callback;") and
	" a modport export ("export task run()"): the function/task is the
	" exported symbol kind, not a definition — without this the 'function'
	" opens a block and everything after it indents one level too deep
	" (demo48)
	let delims = substitute(delims, 'export[^\n]*function', '', 'g')
	let delims = substitute(delims, 'export[^\n]*task', '', 'g')
	let delims = substitute(delims, 'default\s\+clocking[^;]*;\s*endclocking', '', 'g')
	let delims = substitute(delims, 'default\s\+clocking\ze\s\+\h\w*\s*;', '', 'g')
	let delims = substitute(delims, 'default\s\+clocking\ze\s*[@;]', '', 'g')
	" A control line whose body is a complete block on the SAME line
	" ("if (a) begin b = 1; end") must not indent the next line: the
	" b/e cancel leaves a trailing 'x' (LINE_INDENT) and the following
	" statement sits one level too deep (demo97). Neutralize the span
	" here, after the string strip (so an "end" inside a string cannot
	" match) and before the keyword filter: replace the complete block
	" with ';' so the control classifies as a terminated statement.
	" The span must contain no structural keyword and no comment opener
	" (a nested control, a second block, or a commented-out 'end' all
	" defeat the match and keep current behavior); the gap between the
	" control and the block must not cross a block opener/closer (a
	" nested 'begin' would leave a dangling 'end' behind). Multi-line
	" blocks have no 'end' on the line and are untouched. Bare
	" 'begin...end' and case-label items already reduce to empty codes
	" and need no control prefix, so they are left alone.
	let delims = substitute(delims, '\%(\<\%(if\|for\|foreach\|do\|while\|forever\|repeat\|else\|always\|always_comb\|always_ff\|always_latch\|initial\|wait\|wait_order\)\>\|@\)\%(\%(\<\%(begin\|fork\|case\|casex\|casez\|generate\|table\|randcase\|end\|join_any\|join_none\|join\|endcase\|endgenerate\|endtable\)\>\)\@!.\)\{-}\<\%(begin\|fork\|case\|casex\|casez\|generate\|table\|randcase\)\>\%(\%(\<\%(begin\|end\|if\|else\|for\|foreach\|while\|forever\|repeat\|do\|case\|casex\|casez\|fork\|join\|join_any\|join_none\|function\|endfunction\|task\|endtask\|class\|endclass\|module\|endmodule\|generate\|endgenerate\|endcase\|table\|endtable\|randcase\|clocking\|endclocking\|covergroup\|endgroup\|property\|endproperty\|sequence\|endsequence\|checker\|endchecker\|specify\|endspecify\|config\|endconfig\|interface\|endinterface\|package\|endpackage\|primitive\|endprimitive\|cover\|assume\|restrict\|import\|export\|wait\|wait_order\|always\|always_comb\|always_ff\|always_latch\|initial\)\>\|/\*\|//\)\@!.\)\{-}\<\%(endcase\|endgenerate\|endtable\|end\|join_any\|join_none\|join\)\>', ';', 'g')
	" UVM field-automation macro pairs behave like block open/close so
	" `uvm_field_* entries indent one level and `..._utils_end dedents.
	" They are mapped to braces here on purpose: the keyword filter below
	" strips bare letters like 'b'/'e', while braces survive it and are
	" converted to b/e by the [({]/[)}] rules further down.
	let delims = substitute(delims, '`\h\w*_utils_begin\>', '{', 'g')
	let delims = substitute(delims, '`\h\w*_utils_end\>', '}', 'g')
	let delims = substitute(delims, '\<\(\%(initial\|always\|always_comb\|always_ff\|always_latch\|final\|begin\|generate\|disable\|if\|extern\|for\|foreach\|do\|while\|forever\|repeat\|randcase\|case\|casex\|casez\|wait\|wait_order\|fork\|ifdef\|ifndef\|else\|elsif\|end\|endgenerate\|endif\|begin_keywords\|celldefine\|default_nettype\|define\|end_keywords\|endcelldefine\|include\|nounconnected_drive\|pragma\|resetall\|timescale\|unconnected_drive\|undef\|undefineall\|endcase\|join\|join_any\|join_none\|class\|config\|clocking\|function\|task\|specify\|covergroup\|pure\|endclass\|endconfig\|endclocking\|endfunction\|endtask\|endspecify\|endgroup\|primitive\|table\|endprimitive\|endtable\|randsequence\|assume\|assert\|cover\|property\|typedef\|endproperty\|sequence\|checker\|endsequence\|endchecker\)\>\)\@!\k\+', '', 'g')
	let delims = substitute(delims, 'wait\s\+fork', '', 'g')
	let delims = substitute(delims, 'disable\s\+fork', '', 'g')
	let delims = substitute(delims, 'pure\s*\%(\/\*.\{-}\*\/\s*\)*function', '', 'g')
	let delims = substitute(delims, 'extern\s*\%(\/\*.\{-}\*\/\s*\)*function', '', 'g')
	let delims = substitute(delims, 'pure\s*\%(\/\*.\{-}\*\/\s*\)*task', '', 'g')
	let delims = substitute(delims, 'extern\s*\%(\/\*.\{-}\*\/\s*\)*task', '', 'g')
	" a DPI import's function/task is the imported symbol kind, not a
	" definition: neutralize it so "import "DPI-C" function f(...);" does
	" not open a group
	" keywords the filter keeps but that map to no code: strip the leftovers,
	" otherwise the bare word leaks into the codes and its letters accidentally
	" match the single-letter code patterns (e.g. "extern" contains 'e' and
	" 'x', acting as a spurious block-stop and mis-dedenting a following
	" "function ..." declaration that was split onto its own line)
	let delims = substitute(delims, '\<extern\>', '', 'g')
	let delims = substitute(delims, '\<pure\>', '', 'g')
	let delims = substitute(delims, '\<disable\>', '', 'g')
	let delims = substitute(delims, '\<wait\>', 'x', 'g')
	let delims = substitute(delims, '\<alias\>', '', 'g')
	let delims = substitute(delims, '\<final\>', '', 'g')
	let delims = substitute(delims, 'typedef\s\+class', '', 'g')
	let delims = substitute(delims, 'typedef', '', 'g')
	" 'property' in assert/assume/cover/restrict is a reference, not a
	" sequence/property definition (assert and property are both in the
	" keep-list, so this can run after the filter)
	let delims = substitute(delims, '\%(assert\|assume\|cover\|restrict\)\s\+\%(\[\s*\)\?property', '', 'g')
	let delims = substitute(delims, '`\s*\<\(begin_keywords\|celldefine\|default_nettype\|define\|else\|elsif\|end_keywords\|endcelldefine\|endif\|ifdef\|ifndef\|include\|nounconnected_drive\|pragma\|resetall\|timescale\|unconnected_drive\|undef\|undefineall\)\>', 'z', 'g')
	" a macro call in the MIDDLE of a line ("else `uvm_error(...)",
	" "if (x) `uvm_info(...)") is a complete statement to the indent
	" engine: its expansion ends with one. Inject a ';' where the macro
	" name sits, so the line classifies as exec instead of a bare control
	" keyword and the next statement does not indent one level too deep.
	" Line-LEADING macros keep the `^\s*`.*$ -> ';' rule further down
	" (which wipes the whole line, braces included).
	if delims !~ '^\s*`'
		let delims = substitute(delims, '`\h\w*\>', ';', 'g')
	endif
	let delims = substitute(delims, '\<\(begin\|generate\|randcase\|case\|casex\|casez\|fork\|table\)\>', 'b', 'g')
	let delims = substitute(delims, '\<\(end\|endgenerate\|endcase\|join\|join_any\|join_none\|endtable\)\>', 'e', 'g')
	let delims = substitute(delims, '\<\(class\|config\|clocking\|function\|task\|specify\|covergroup\|property\|sequence\|checker\|primitive\|randsequence\)\>', 'f', 'g')
	let delims = substitute(delims, '\<\(endclass\|endconfig\|endclocking\|endfunction\|endtask\|endspecify\|endgroup\|endproperty\|endsequence\|endchecker\|endprimitive\)\>', 'h', 'g')
	let delims = substitute(delims, '\<\(if\|for\|foreach\|do\|while\|forever\|repeat\|always\|always_comb\|always_ff\|always_latch\|initial\|wait_order\)\>', 'x', 'g')
	" 'wait_order' is a control statement like 'if': its body indents one
	" level and its 'else' clause dedents back (demo68). Without this the
	" body sits at the same level as 'wait_order' itself.
	" 'else' is a control statement ('x') so a statement on the next line
	" indents one level, and the dedent rule (prev2 x + prev1 exec) can also
	" fire for end/endfunction/endtask that follow an else-branch.
	" 'assert' stays a statement terminator (lower priority, per README).
	let delims = substitute(delims, '\<assert\>', ';', 'g')
	let delims = substitute(delims, '\<else\>', 'x', 'g')
	let delims = substitute(delims, '^\s*\/\/.*$', 'l', 'g')
	let delims = substitute(delims, '\/\/.*', '', 'g')
	let delims = substitute(delims, '"\(\\.\|[^"\\]\)*"', '', 'g')
	let delims = substitute(delims, '\/\*', 's', 'g')
	let delims = substitute(delims, '\*\/', 'p', 'g')
	let delims = substitute(delims, '\[[^:\[\]]*:[^:\[\]]*\]', '', 'g')
	let delims = substitute(delims, '\@', 'x', 'g')
	" a macro call whose argument is a multi-line constraint/block
	" ('`uvm_do_with(x, {' ... '})') keeps its open brace: map the whole
	" line to '{' so the body indents one level and the closing '})'
	" returns to the macro line instead of dedenting past it. The '{'
	" replaces the backtick, so the ^\s*`.*$ rule below leaves it alone;
	" in no-parens mode the brace is dropped with the other delimiters.
	let delims = substitute(delims, '^\s*`.*{\s*$', '{', '')
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
	" (no ternary-continuation rule here: a trailing '?' or ':' that
	" opens a multi-line ternary needs the next line indented, but
	" marking the line with 'x' dedents a ternary that is itself the
	" body of an 'if' to the 'if' level via the chained-control rule
	" (uvm_mem, uvm_reg), and a separate 'y' marker breaks 'else'
	" matching and cascades through whole files (uvm_mem +1142
	" lines). Multi-line ternary continuation is a known gap, not
	" fixed; demo67 uses a single-line ternary.)
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

" Segments of a block-comment boundary line that lie outside the
" comment markers: [before-first-/*, after-first-*/-up-to-reopen].
" Strings are stripped first (same uniform pattern as the code
" paths), so a "/*" inside a string cannot split the line.
function! s:CommentSegments( codeline )
	let l:stripped = substitute(a:codeline, '"\(\\.\|[^"\\]\)*"', '""', 'g')
	let l:before = matchstr(l:stripped, '^.\{-}\ze/\*')
	let l:after = matchstr(l:stripped, '\*/\zs.*$')
	let l:cut = stridx(l:after, '/*')
	if l:cut >= 0
		let l:after = strpart(l:after, 0, l:cut)
	endif
	return [l:before, l:after]
endfunction

" True when a boundary line carries real code outside the markers.
" Codes alone cannot tell: comment prose maps keywords to letters
" (an 'if' inside a /** doc comment codes as 'x'), so test the
" segments for a structural code letter instead (demo103/104).
function! s:BoundaryHasCode( codeline )
	let [l:before, l:after] = s:CommentSegments(a:codeline)
	return (l:before != '' && s:ConvertToCodes(l:before) =~ s:CODE_LETTER)
		\ || (l:after != '' && s:ConvertToCodes(l:after) =~ s:CODE_LETTER)
endfunction

" True when code follows the first */ (up to a re-opening /*).
function! s:CodeAfterClose( codeline )
	let l:after = s:CommentSegments(a:codeline)[1]
	return l:after != '' && s:ConvertToCodes(l:after) =~ s:CODE_LETTER
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
		let codeline = strpart( codeline , 0 , strlen( codeline ) - 1 ) . " " . getline (line_num)
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

	" NOTE: no floor at 0 here, and none at the callers either, on
	" purpose. A negative result makes Vim keep the line's current
	" indent, and several UVM golden files rely on exactly that (a stop
	" dedenting from a 0 base keeps the original file's indent, which is
	" the baked convention). Flooring the result — inside this function
	" or at the final returns — shifted 12, then 3, golden files. An
	" over-dedent caused by a stale prev2 is fixed at the source instead:
	" callers pass '' for a prev2 buried in a region that closed before
	" prev1 (s:IsStalePrev2), so the dedent rule never fires on it.
	return indnt
endfunction

" Return the line number of the `ifdef/`ifndef that a `else/`elsif/`endif at
" a:line_num matches, walking back through nested conditionals (comments and
" plain code are skipped), or 0 if none (an unbalanced/standalone directive).
" Return the `define line that starts the multi-line `define whose body
" contains a:line_num, or 0. A multi-line `define is a contiguous run of
" lines where every line but the last ends with a backslash; its body
" lines are macro text, not real conditional compilation, so the
" directive-counting walks must skip the whole body. The `define line
" itself is not "inside" the body (it is a real directive, transparent
" to the counting), so a:line_num equal to the `define line returns 0.
function! s:DefineBodyStart( line_num )
	let l:ln = a:line_num
	while l:ln > 1 && getline(l:ln - 1) =~ '\\$'
		let l:ln -= 1
	endwhile
	if l:ln < a:line_num && getline(l:ln) =~ '^\s*`define\>'
		return l:ln
	endif
	return 0
endfunction

" Previous effective code line for a [he] close that resolved through a
" closed `ifdef region (or a `define after one). Walk back from a:line_num
" (the matching `ifdef line) through any immediately preceding multi-line
" `define body and any immediately preceding closed `ifdef region, and
" return the line to use as prev_start so prev1 lands on the code before
" the whole preprocessor sequence (residual (b): task -> ifdef -> define
" -> ifdef -> endtask). Returns a:line_num unchanged when there is no
" such sequence. `ifdef openers are transparent here because a [he] close
" belongs to the outer level, not the region body.
function! s:PrevCodeLine( line_num )
	let l:ln = prevnonblank(a:line_num - 1)
	while l:ln > 0
		let l:line = getline(l:ln)
		if l:line =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/'
			let l:ln = prevnonblank(l:ln - 1)
			continue
		endif
		let l:ds = s:DefineBodyStart(l:ln)
		if l:ds > 0
			let l:ln = prevnonblank(l:ds - 1)
			continue
		endif
		if l:line =~ '^\s*`\s*\cendif\>'
			let l:m = s:FindIfdefMatch(l:ln)
			if l:m > 0
				let l:ln = prevnonblank(l:m - 1)
				continue
			endif
			break
		endif
		if l:line =~ '^\s*`'
			" any other directive (`ifdef/`ifndef/`else/`elsif/`define/
			" `include ...): transparent for a [he] close, skip it
			let l:ln = prevnonblank(l:ln - 1)
			continue
		endif
		" a code line: prev_start just after it, so prev1 resolves to it
		return l:ln + 1
	endwhile
	return a:line_num
endfunction

function! s:FindIfdefMatch( line_num )
	if !exists('b:sv_iffind_cache') || b:sv_iffind_tick != b:changedtick
		let b:sv_iffind_cache = {}
		let b:sv_iffind_tick = b:changedtick
	endif
	if has_key(b:sv_iffind_cache, a:line_num)
		return b:sv_iffind_cache[a:line_num]
	endif
	let l:depth = 0
	let l:ln = prevnonblank(a:line_num - 1)
	while l:ln > 0
		let l:ds = s:DefineBodyStart(l:ln)
		if l:ds > 0
			let l:ln = prevnonblank(l:ds - 1)
			continue
		endif
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
				let b:sv_iffind_cache[a:line_num] = l:ln
				return l:ln
			endif
			let l:depth -= 1
			let l:ln = prevnonblank(l:ln - 1)
			continue
		endif
		" plain code or other preprocessor directive: keep walking up
		let l:ln = prevnonblank(l:ln - 1)
	endwhile
	let b:sv_iffind_cache[a:line_num] = 0
	return 0
endfunction

" Indent for a preprocessor conditional line (`ifdef/`ifndef/`elsif/`else/
" `endif): align it with the enclosing code, matching the UVM library style
" where a nested `ifdef sits one level deeper than its enclosing code and
" `else/`elsif/`endif align with their matching `ifdef. The top-level file
" guard (`ifndef ..._SVH at column 0) falls through to the base indent (0).
" Correct indent for an `ifdef/`ifndef opener line, computed
" recursively via SlowIndent (which derives its own base from the
" opener's context) instead of read from the buffer, so a stale
" indent on the opener cannot leak into the next opener after a
" closed region. Each recursion moves to a strictly earlier line, so
" it terminates; the depth guard falls back to the buffer indent for
" very deep chains (the old behavior, still correct during gg=G).
" a:base_indnt is accepted for the call sites but not used: the
" opener's own base is recomputed by SlowIndent.
function! s:OpenerIndent( line_num, base_indnt )
	if !exists('b:sv_opener_depth')
		let b:sv_opener_depth = 0
	endif
	if b:sv_opener_depth > 50
		return indent(a:line_num)
	endif
	let b:sv_opener_depth += 1
	try
		let l:r = s:SlowIndent(a:line_num)
	finally
		let b:sv_opener_depth -= 1
	endtry
	return l:r
endfunction

function! s:IsFileGuard( ln )
	" a file guard is an `ifndef X immediately followed by `define X
	" AND it is the first `ifdef/`ifndef in the file (not nested
	" inside another conditional). A nested `ifndef X + `define X
	" (e.g. UVM_MAX_STREAMBITS default) is a conditional default,
	" not a guard, and its body IS indented +1.
	let l:line = getline(a:ln)
	if l:line !~ '^\s*`\s*\cifndef\>'
		return 0
	endif
	let l:gname = matchstr(l:line, '^\s*`\s*\cifndef\s\+\zs\w\+')
	if l:gname ==# ''
		return 0
	endif
	let l:nx = nextnonblank(a:ln + 1)
	if l:nx <= 0 || getline(l:nx) !~ '^\s*`\s*\cdefine\s\+' . l:gname . '\>'
		return 0
	endif
	let l:i = 1
	while l:i < a:ln
		if getline(l:i) =~ '^\s*`\s*\c\(ifdef\|ifndef\)\>'
			return 0
		endif
		let l:i += 1
	endwhile
	return 1
endfunction

function! s:GetPreprocIndent( line_num, base_indnt )
	let l:ln = prevnonblank(a:line_num - 1)
	if getline(a:line_num) =~ '^\s*`\s*\c\(ifdef\|ifndef\)\>'
		" opener: sit at the code level, one deeper per enclosing ifdef.
		" Two cases, distinguished by the nearest preceding directive:
		" (1) opener after a closed region: align with that closed
		" region opener, regardless of how deep its last body line
		" was, or every sequential region leaks +shiftwidth.
		" (2) otherwise: the old signed-nest rule (base + nest * sw),
		" which counts enclosing openers (including a top-level
		" guard, base -1 at file top) and nets off closed regions
		" encountered before the enclosing code line.
		let l:first = prevnonblank(a:line_num - 1)
		while l:first > 0
			if getline(l:first) =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/'
				let l:first = prevnonblank(l:first - 1)
				continue
			endif
			" a multi-line `define body is macro text, not a directive:
			" skip the whole body so case 1 can see the real `endif
			" before the `define (residual (b), slow path `ifdef B)
			let l:ds = s:DefineBodyStart(l:first)
			if l:ds > 0
				let l:first = prevnonblank(l:ds - 1)
				continue
			endif
			break
		endwhile
		if l:first > 0 && getline(l:first) =~ '^\s*`\s*\cendif\>' && s:DefineBodyStart(l:first) == 0
			let l:depth = 0
			let l:ln = l:first
			while l:ln > 0
				let l:ds = s:DefineBodyStart(l:ln)
				if l:ds > 0
					let l:ln = prevnonblank(l:ds - 1)
					continue
				endif
				let l:line = getline(l:ln)
				if l:line =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/'
					let l:ln = prevnonblank(l:ln - 1)
					continue
				endif
				if l:line =~ '^\s*`\s*\cendif\>'
					let l:depth += 1
				elseif l:line =~ '^\s*`\s*\c\(ifdef\|ifndef\)\>'
					if l:depth > 0
						let l:depth -= 1
						if l:depth == 0
							return s:OpenerIndent(l:ln, a:base_indnt)
						endif
					else
						return s:OpenerIndent(l:ln, a:base_indnt) + &shiftwidth
					endif
				elseif l:line =~ '^\s*`'
					" other preprocessor directive - transparent
				elseif l:depth > 0
					" code inside a closed region: skip it
				else
					break
				endif
				let l:ln = prevnonblank(l:ln - 1)
			endwhile
			return a:base_indnt
		endif
		" nested `ifdef after a multi-line `define (demo22): the opener
		" sits one level deeper than its enclosing `ifdef, but case 2
		" below breaks on the define body and never counts the enclosing
		" region. If the nearest preceding directive (skipping define
		" bodies, `define/`include/`undef lines and comments) is a
		" non-guard `ifdef/`ifndef opener, align one level deeper
		" than it. Only when something was actually skipped: a nested
		" `ifdef directly after its enclosing opener (no `define in
		" between, e.g. uvm_object_defines.svh `ifndef
		" uvm_record_attribute / `ifdef QUESTA) stays at the same
		" level, as the golden files expect. A file guard is excluded:
		" its body sits at the same level (demo16).
		let l:enc = prevnonblank(a:line_num - 1)
		let l:skipped = 0
		while l:enc > 0
			let l:el = getline(l:enc)
			if l:el =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/'
				let l:enc = prevnonblank(l:enc - 1)
				continue
			endif
			let l:ds = s:DefineBodyStart(l:enc)
			if l:ds > 0
				let l:skipped = 1
				let l:enc = prevnonblank(l:ds - 1)
				continue
			endif
			if l:el =~ '^\s*`\s*\c\(define\|include\|undef\)\>'
				let l:skipped = 1
				let l:enc = prevnonblank(l:enc - 1)
				continue
			endif
			break
		endwhile
		if l:skipped && l:enc > 0 && getline(l:enc) =~ '^\s*`\s*\c\(ifdef\|ifndef\)\>' && !s:IsFileGuard(l:enc)
			return indent(l:enc) + &shiftwidth
		endif
		let l:nest = 0
		while l:ln > 0
			if s:DefineBodyStart(l:ln) > 0
				" a line inside a define body is macro text: it breaks the
				" directive run exactly like a code line does, so stop here
				" instead of counting the define's internal directives.
				break
			endif
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
		return a:base_indnt + l:nest * &shiftwidth
	endif
	" `include inside an `ifdef body (reached when the previous line is code,
	" so SlowIndent's include block did not return early): an `include is a
	" body line like any statement, so sit at the code level (base_indnt),
	" not at the opener level like a closer (`else/`elsif/`endif) or a
	" `define (which aligns with its opener by convention). But a file
	" guard's body stays at the guard level (demo16), so a guard
	" `include falls through to the closer branch below.
	if getline(a:line_num) =~ '^\s*`\s*\cinclude\>'
		let l:m = s:FindIfdefMatch(a:line_num)
		if l:m > 0 && !s:IsFileGuard(l:m)
			return a:base_indnt
		endif
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

" --- rolling single-pass state (gg=G fast path) ---
" Valid only while indentexpr is called for consecutive non-blank lines
" starting at line 1 with an unchanged changedtick (exactly what gg=G
" does). Any other call pattern falls back to the slow path and
" invalidates the chain. State is updated for every line in the chain,
" whichever path computed its indent, so a slow-path line never breaks it.
let b:sv_roll_tick = -1
let b:sv_roll_last = -1
let b:sv_roll_top = 0
let b:sv_roll_ifdefs = []
let b:sv_roll_match = {}
let b:sv_roll_nets = {}
let b:sv_roll_sig = 0
let b:sv_roll_first = 0
let b:sv_roll_run = 0
let b:sv_roll_codelines = []
let b:sv_roll_ucodes = {}
let b:sv_roll_uindent = {}
let b:sv_roll_incomment = 0
let b:sv_roll_pend = -1
let b:sv_roll_pend_ic = 0
let b:sv_roll_prevnb = 0

" Paren net of one physical line, after the same strips the tail-head walks
" use (string literals, then //-comment). Lazily computed and memoized per
" line, so a walk that re-visits lines pays the strips once per pass.

" A function/task whose signature sits on a line after a bare qualifier line
" (extern / pure / virtual / protected ... with no ';') is a split prototype:
" its group opener 'f' must not stay open past the signature's closing ');',
" or every following declaration cascades one level deeper. Strip the 'f'.
function! s:StripPrototypeF( line_num, codeline, codes )
	if stridx(a:codeline, 'function') == -1 && stridx(a:codeline, 'task') == -1
		return a:codes
	endif
	if a:codeline =~ '^\s*\%(\%(virtual\|pure\|static\|automatic\|local\)\s\+\)*\%(function\|task\)\>'
		let l:prev = getline(prevnonblank(a:line_num - 1))
		if l:prev =~ '^\s*\%(extern\|virtual\|protected\|pure\|static\|local\)\%(\s\+\%(extern\|virtual\|protected\|pure\|static\|local\)\)*\s*$'
			return substitute(a:codes, 'f', '', 'g')
		endif
	endif
	return a:codes
endfunction

" If the line at a:line_num ends a multi-line statement - a macro call
" ('`uvm_info(a, ...') or an ordinary method/function call whose arguments
" span lines (top.uvm_report_error("m", $sformatf(...), ...)) - return the
" statement head's line number; otherwise 0. The head is the line that
" opened the statement: walk back from the tail, balancing round
" parentheses (strings and //-comments ignored); the first line that brings
" the running balance back to >= 0 is the head (the tail itself closes more
" parens than it opens, so the balance starts negative). A ');'-ending line
" whose preceding line is not a ', ( [ {'-continuation is a self-contained
" statement, not a tail.
function! s:StatementTailHead( line_num )
	let l:line = getline(a:line_num)
	if l:line !~ ')\s*;\?\s*$'
		return 0
	endif
	if l:line =~ '^\s*[;)}]'
	  \ || l:line =~ '^\s*\%(end\|endcase\|endgenerate\|endmodule\|endinterface\|endpackage\|endclass\|endfunction\|endtask\|endgroup\|endproperty\|endsequence\|endchecker\|endconfig\|endclocking\|endspecify\|join\|join_any\|join_none\)\>'
		return 0
	endif
	if prevnonblank(a:line_num - 1) == 0 || getline(prevnonblank(a:line_num - 1)) !~ '[,([{]\s*$'
		return 0
	endif
	let l:bal = 0
	" the tail must close more parens than it opens (it closes the head's
	" open paren); a balanced or opening line is not a closing tail
	let l:l = substitute(l:line, '\".\{-}\"', '', 'g')
	let l:l = substitute(l:l, '\/\/.*', '', '')
	let l:bal = len(substitute(l:l, '[^(]', '', 'g')) - len(substitute(l:l, '[^)]', '', 'g'))
	if l:bal >= 0
		return 0
	endif
	let l:ln = prevnonblank(a:line_num - 1)
	let l:limit = 200
	while l:ln > 0 && l:limit > 0
		let l:l = getline(l:ln)
		let l:l = substitute(l:l, '\".\{-}\"', '', 'g')
		let l:l = substitute(l:l, '\/\/.*', '', '')
		let l:bal = l:bal + len(substitute(l:l, '[^(]', '', 'g')) - len(substitute(l:l, '[^)]', '', 'g'))
		if l:bal >= 0
			return l:ln
		endif
		let l:ln = prevnonblank(l:ln - 1)
		let l:limit -= 1
	endwhile
	return 0
endfunction

" If a:line_num is the closing line of a multi-line CONTROL statement
" (if/for/foreach/while/do/repeat/forever/wait_order whose condition
" spans lines AND contains a preprocessor directive (`ifdef/`ifndef/
" `elsif/`else/`endif) inside the parens), return the line number of the
" control opener; otherwise 0. The directive requirement narrows the
" fix to the ifdef-chosen-condition case (demo83): a plain multi-line
" condition (no directive) keeps the established flat body (UVM golden),
" so only ifdef-split conditions indent their body. Walks back counting
" paren balance (strings and // comments stripped); `;` does NOT stop
" the walk (a for-loop init/cond/incr has ';' inside the parens). The
" opener must classify as a control line (its codes contain 'x'), so a
" function/method call tail returns 0 (its head has no 'x'). A bare ')'
" on its own line is a valid tail.
function! s:ControlTailHead( line_num, ... )
	let l:line = getline(a:line_num)
	if l:line !~ ')\s*$' || l:line =~ ');\s*$'
		return 0
	endif
	if l:line =~ '^\s*[;}]'
		return 0
	endif
	if l:line =~ '^\s*\%(end\|endcase\|endgenerate\|endmodule\|endinterface\|endpackage\|endclass\|endfunction\|endtask\|endgroup\|endproperty\|endsequence\|endchecker\|endconfig\|endclocking\|endspecify\|join\|join_any\|join_none\)\>'
		return 0
	endif
	" by default the walk must cross a preprocessor directive: ungated,
	" ordinary multi-line if bodies (flat by golden convention) regress.
	" Callers that already know the tail sits inside an `ifdef region
	" (s:AfterEndifBodyIndent, s:RegionEndsWithControl) pass 0, so a
	" multi-line control wholly inside one branch still resolves.
	let l:require_preproc = a:0 >= 1 ? a:1 : 1
	let l:l = substitute(l:line, '"\(\\.\|[^"\\]\)*"', '', 'g')
	let l:l = substitute(l:l, '/\*.\{-}\*/', '', 'g')
	let l:l = substitute(l:l, '\/\/.*', '', '')
	let l:bal = len(substitute(l:l, '[^(]', '', 'g')) - len(substitute(l:l, '[^)]', '', 'g'))
	if l:bal >= 0
		return 0
	endif
	let l:saw_preproc = 0
	let l:ln = prevnonblank(a:line_num - 1)
	let l:limit = 200
	while l:ln > 0 && l:limit > 0
		let l:limit -= 1
		let l:l = getline(l:ln)
		if l:l =~ '^\s*`\s*\c\(else\|elsif\)\>'
			" the sibling branch is mutually exclusive with the branch
			" the tail came from: skip it entirely (jump to before
			" the matching `ifdef) instead of counting its parens
			" into l:bal a second time
			let l:saw_preproc = 1
			let l:m = s:FindIfdefMatch(l:ln)
			if l:m > 0
				let l:ln = prevnonblank(l:m - 1)
				continue
			endif
		elseif l:l =~ '^\s*`\s*\c\(ifdef\|ifndef\|endif\)\>'
			let l:saw_preproc = 1
		endif
		let l:l = substitute(l:l, '"\(\\.\|[^"\\]\)*"', '', 'g')
		let l:l = substitute(l:l, '/\*.\{-}\*/', '', 'g')
		let l:l = substitute(l:l, '\/\/.*', '', '')
		let l:bal = l:bal + len(substitute(l:l, '[^(]', '', 'g')) - len(substitute(l:l, '[^)]', '', 'g'))
		if l:bal >= 0
			if (!l:require_preproc || l:saw_preproc) && s:ConvertToCodes(getline(l:ln)) =~ 'x'
				return l:ln
			endif
			return 0
		endif
		let l:ln = prevnonblank(l:ln - 1)
	endwhile
	return 0
endfunction

" Return the last code line inside the `ifdef region ending at a:endif_ln
" (whose matching `ifdef is a:ifdef_ln), skipping comments, directives
" and whole nested `ifdef...`endif blocks, or 0 if the region holds no
" code line of its own.
function! s:RegionLastCodeLine( endif_ln, ifdef_ln )
	let l:last = prevnonblank(a:endif_ln - 1)
	while l:last > a:ifdef_ln
		let l:ll = getline(l:last)
		if l:ll =~ '^\s*`\s*\cendif\>'
			" a nested `ifdef...`endif block: skip the whole block so
			" a control buried inside it is not mistaken for this
			" region's own last code line
			let l:m = s:FindIfdefMatch(l:last)
			if l:m > 0 && l:m > a:ifdef_ln
				let l:last = prevnonblank(l:m - 1)
				continue
			endif
		endif
		if l:ll =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/\|^\s*`\s*\c\(ifdef\|ifndef\|elsif\|else\|endif\|define\|undef\|include\)\>'
			let l:last = prevnonblank(l:last - 1)
			continue
		endif
		break
	endwhile
	return l:last > a:ifdef_ln ? l:last : 0
endfunction

" If the last code line inside the 'ifdef region ending at a:endif_ln
" (whose matching 'ifdef is a:ifdef_ln) opens a block whose close sits
" outside the region, return that line; otherwise 0. A control+begin
" line codes 'xb' (possibly with a trailing statement, 'xb;'), with no
" 'e' before it: an 'end else begin' line ('exb') closes a block
" first, and its indent is governed by the close-after-directive
" handling, not by this helper (the else-split shape keeps its
" pristine behavior). A bare opener codes 'b' -- but so does a
" multi-line call head ('foo('), so the bare form additionally
" requires an opener keyword at the start of the line. The flat-tail
" golden convention forbids treating a bare 'b' as an opener
" without that text check (demo101).
function! s:RegionEndsWithBlockOpener( endif_ln, ifdef_ln )
	let l:last = s:RegionLastCodeLine(a:endif_ln, a:ifdef_ln)
	if l:last <= 0
		return 0
	endif
	let l:codes = s:ConvertToCodes(getline(l:last))
	if l:codes =~ '^[^e]*xb;*$'
		return l:last
	endif
	if l:codes =~ '^b;*$' && getline(l:last) =~ '^\s*\%(begin\|fork\|case\|casex\|casez\|generate\|table\|randcase\)\>'
		return l:last
	endif
	return 0
endfunction

" If the last code line inside the `ifdef region ending at a:endif_ln
" (whose matching `ifdef is a:ifdef_ln) is a control statement, return the
" indent its body should take (control indent + shiftwidth); otherwise -1.
" Used for a statement after an `endif that is the body of an if/for/...
" whose opener is the last code line inside the region (demo84 Form 2:
" `ifdef X / if (b) / `else / if (c) / `endif / `MACRO; — the macro is
" the body of the if). A control tail (multi-line condition) resolves
" through s:ControlTailHead to its opener, whether the opener sits
" inside the region or above it (Form 1).
function! s:AfterEndifBodyIndent( endif_ln, ifdef_ln )
	let l:last = s:RegionLastCodeLine(a:endif_ln, a:ifdef_ln)
	if l:last <= 0
		return -1
	endif
	if s:ConvertToCodes(getline(l:last)) =~ s:LINE_INDENT
		return indent(l:last) + &shiftwidth
	endif
	" a block opener (if/for/... begin, or a bare begin/fork/case) as
	" the region's last code line opens a block whose body sits after
	" the 'endif (demo101): the body indents one level past the opener
	let l:op = s:RegionEndsWithBlockOpener(a:endif_ln, a:ifdef_ln)
	if l:op > 0
		return indent(l:op) + &shiftwidth
	endif
	" l:last is confirmed inside the region, so the tail walk needs no
	" directive crossing: a multi-line control wholly inside one branch
	" (no directive between its head and tail) must still resolve
	let l:chead = s:ControlTailHead(l:last, 0)
	if l:chead > 0
		return indent(l:chead) + &shiftwidth
	endif
	return -1
endfunction

" If the region ending at a:endif_ln (whose matching `ifdef is
" a:ifdef_ln) ends with a control statement, return the line the code
" after the region's body resolves through: the `ifdef line when the
" control lives inside the region (Form 2), or the control head above
" the region when the region's last line is a tail resolving there
" (Form 1: the following line aligns with that head, not with the
" region, whose level is the head's body level). Otherwise 0.
function! s:RegionExitLine( endif_ln, ifdef_ln )
	let l:last = s:RegionLastCodeLine(a:endif_ln, a:ifdef_ln)
	if l:last <= 0
		return 0
	endif
	if s:ConvertToCodes(getline(l:last)) =~ s:LINE_INDENT
		return a:ifdef_ln
	endif
	" see s:AfterEndifBodyIndent: no directive crossing required here.
	" Entry and exit must agree: either the head is inside the region,
	" or the tail walk crosses a directive to reach a head above it
	" (Form 1) -- both govern the lines after the `endif.
	let l:chead = s:ControlTailHead(l:last, 0)
	if l:chead > 0
		return l:chead <= a:ifdef_ln ? l:chead : a:ifdef_ln
	endif
	return 0
endfunction

" True if the region ending at a:endif_ln ends with a control statement:
" a direct control line, a control tail whose opener is inside the
" region, or a control tail whose opener sits above the `ifdef (Form 1)
" and is reached by crossing a directive.
function! s:RegionEndsWithControl( endif_ln, ifdef_ln )
	return s:RegionExitLine(a:endif_ln, a:ifdef_ln) > 0
endfunction

" True when the code line at a:prev2_ln sits inside a conditional region
" that closed (or switched branch) before a:prev1_ln: an `endif/`else/`elsif
" strictly between the two lines whose matching `ifdef is at or above
" a:prev2_ln. Such a prev2 is stale: it governs nothing below the region,
" so the "prev2 control + prev1 statement" dedent rule must not see it as
" a control (repro_p2b: a bare `if` buried in a nested region otherwise
" double-dedents the `end` below the outer `endif below 0, and Vim then
" keeps the line's stale indent). Exception: a prev2 that is the tail of
" a control opening above the region (Form 1: the control spans the
" region and does govern the lines below it) is not stale.
function! s:IsStalePrev2( prev2_ln, prev1_ln )
	let l:ln = prevnonblank(a:prev1_ln - 1)
	while l:ln > a:prev2_ln
		if getline(l:ln) =~ '^\s*`\s*\c\%(endif\|else\|elsif\)\>'
			let l:m = s:FindIfdefMatch(l:ln)
			if l:m > 0 && l:m <= a:prev2_ln
				let l:chead = s:ControlTailHead(a:prev2_ln)
				if l:chead > 0 && l:chead <= l:m
					return 0
				endif
				return 1
			endif
		endif
		let l:ln = prevnonblank(l:ln - 1)
	endwhile
	return 0
endfunction

" If a:prev1_ln sits inside a branch that is mutually exclusive with
" the branch holding a:line_num (an `else/`elsif strictly between the
" two whose matching `ifdef is at or above a:prev1_ln), return the code
" line before that `ifdef; otherwise return a:prev1_ln unchanged. The
" redirect applies only when the line closes the shared condition (a
" `)`-tail line) or continues it past a sibling line that already
" closed the paren (the code before the `ifdef has an unclosed
" paren/begin): a fresh statement after the sibling branch keeps its
" natural prev1 (demo86, demo91).
function! s:PrevBeforeBranch( prev1_ln, line_num )
	let l:ln = prevnonblank(a:line_num - 1)
	while l:ln > a:prev1_ln
		if getline(l:ln) =~ '^\s*`\s*\c\%(else\|elsif\)\>'
			let l:m = s:FindIfdefMatch(l:ln)
			if l:m > 0 && l:m <= a:prev1_ln
				let l:pl = s:GetPrevWholeLineNum(l:m)
				if l:pl <= 0
					return 0
				endif
				let l:pl_codes = s:ConvertToCodes(s:GetWholeLine(l:pl))
				let l:in_comment = 0
				while l:pl > 0 && (l:pl_codes =~ s:LINE_COMMENT || l:in_comment || l:pl_codes =~ s:BLOCK_COMMENT_STOP || l:pl_codes =~ s:BLOCK_COMMENT_START || l:pl_codes =~ s:PREPROCESSOR)
					if l:pl_codes =~ s:BLOCK_COMMENT_STOP_ANY
						let l:in_comment = 1
					endif
					if l:pl_codes =~ s:BLOCK_COMMENT_START
						let l:in_comment = 0
					endif
					" boundary line carrying code ("begin /*", "*/ end"):
					" use it as the previous code line instead of skipping
					" past it; comment-interior lines keep skipping even
					" when their text contains keywords (demo103).
					if (l:pl_codes =~ s:BLOCK_COMMENT_STOP_ANY || l:pl_codes =~ s:BLOCK_COMMENT_START) && s:BoundaryHasCode(s:GetWholeLine(l:pl)) && l:pl_codes !~ s:LINE_COMMENT && l:pl_codes !~ s:PREPROCESSOR
						break
					endif
					let l:pl = s:GetPrevWholeLineNum(l:pl)
					if l:pl <= 0
						break
					endif
					let l:pl_codes = s:ConvertToCodes(s:GetWholeLine(l:pl))
				endwhile
				" redirect only for a `)`-tail line (more closes than
				" opens: a complete `if (c)` head is not a tail), or
				" for a continuation line: an unterminated line that
				" is not itself a complete balanced head, whose
				" sibling line closed the shared paren (so it cannot
				" govern this line), inside a construct whose head
				" above the `ifdef is itself unclosed (a fresh
				" statement, or a continuation after a plain sibling
				" line, keeps its natural prev1)
				let l:cur = substitute(getline(a:line_num), '"\(\\.\|[^"\\]\)*"', '', 'g')
				let l:cur = substitute(l:cur, '/\*.\{-}\*/', '', 'g')
				let l:cur = substitute(l:cur, '\/\/.*', '', '')
				let l:opens = len(substitute(l:cur, '[^(]', '', 'g'))
				let l:closes = len(substitute(l:cur, '[^)]', '', 'g'))
				if l:cur =~ ')\s*$' && l:cur !~ ');\s*$' && l:closes > l:opens
					return l:pl
				endif
				if l:cur !~ ';\s*$' && !(l:cur =~ ')\s*$' && l:opens == l:closes) && l:pl > 0 && s:ConvertToCodes(s:GetWholeLine(l:pl)) =~ 'b'
					let l:sib = substitute(getline(a:prev1_ln), '"\(\\.\|[^"\\]\)*"', '', 'g')
					let l:sib = substitute(l:sib, '/\*.\{-}\*/', '', 'g')
					let l:sib = substitute(l:sib, '\/\/.*', '', '')
					if len(substitute(l:sib, '[^)]', '', 'g')) > len(substitute(l:sib, '[^(]', '', 'g'))
						return l:pl
					endif
				endif
				return a:prev1_ln
			endif
		endif
		let l:ln = prevnonblank(l:ln - 1)
	endwhile
	return a:prev1_ln
endfunction

" Walk up from a:ln over bare single-line control heads (codes ending
" in 'x': if/for/while with no body of their own) to the `endif the
" chain hangs off, returning that `endif line, or 0. a:ln itself may be
" the `endif. At most 4 heads are stepped over; a deeper chain falls
" back to the normal rules instead of resolving through the region.
function! s:ChainToEndif( ln )
	let l:ln = a:ln
	let l:limit = 4
	while l:ln > 0
		if getline(l:ln) =~ '^\s*`\s*\cendif\>'
			return l:ln
		endif
		if getline(l:ln) =~ '^\s*\%(end\s\+\)\?else\>' && s:ConvertToCodes(getline(l:ln)) !~ 'b'
			" a bare `else` between the walked heads and the region:
			" jump over the whole if/else-if chain and continue
			" above its first `if`. The step above the head is
			" essential: the head may carry its body on the same
			" line (`if (c) x = 1;`), so re-checking the head
			" itself against LINE_INDENT would fail and break
			" the chain. An `else` that opens a block (`else
			" begin`) is not stepped over: the line above it
			" sits inside that block.
			if l:limit <= 0
				return 0
			endif
			let l:limit -= 1
			let l:ln = prevnonblank(s:ElseChainHead(l:ln) - 1)
			continue
		endif
		if l:limit <= 0 || s:ConvertToCodes(getline(l:ln)) !~ s:LINE_INDENT
			return 0
		endif
		let l:limit -= 1
		let l:ln = prevnonblank(l:ln - 1)
	endwhile
	return 0
endfunction

" If a:p1_ln is an `else`/`else if` continuation line, walk up the
" if/else-if chain to the first `if` line and return it; otherwise
" return a:p1_ln unchanged. A branch may be a single statement, a
" multi-line condition (resolved via s:ControlTailHead), or a
" begin...end block (stepped over via s:MatchBlockOpener, whether the
" `end` sits on its own line or shares the line with the `else`).
" At most 8 steps.
function! s:ElseChainHead( p1_ln )
	let l:ln = a:p1_ln
	let l:limit = 8
	while l:limit > 0 && getline(l:ln) =~ '^\s*\%(end\s\+\)\?else\>'
		let l:limit -= 1
		if getline(l:ln) =~ '^\s*end\s\+else\>'
			let l:op = s:MatchBlockOpener(l:ln)
			if l:op <= 0
				break
			endif
			let l:cand = getline(l:op) =~ '^\s*begin\>' ? prevnonblank(l:op - 1) : l:op
		else
			let l:body = prevnonblank(l:ln - 1)
			if l:body <= 0
				break
			endif
			if s:ConvertToCodes(getline(l:body)) =~ '^[he]$'
				let l:op = s:MatchBlockOpener(l:body)
				if l:op <= 0
					break
				endif
				let l:cand = getline(l:op) =~ '^\s*begin\>' ? prevnonblank(l:op - 1) : l:op
			elseif getline(l:body) =~ '^\s*\%(else\s\+\)\?if\>'
				" the previous branch's body sits on its `if` line
				" (`if (c) y = 1;`): the body line IS the chain link
				let l:cand = l:body
			else
				let l:cand = prevnonblank(l:body - 1)
			endif
		endif
		if l:cand <= 0
			break
		endif
		if getline(l:cand) =~ '^\s*\%(else\s\+\)\?if\>'
			let l:ln = l:cand
			continue
		endif
		let l:ch = s:ControlTailHead(l:cand, 0)
		if l:ch > 0
			let l:ln = l:ch
			continue
		endif
		break
	endwhile
	return l:ln
endfunction

" The line before the chain head above a:ln, for region resolution:
" resolve a:ln through its else-chain, and if the line before the head
" is itself a bare `else` (the head's body sits between the `else` and
" a:ln), resolve that `else` through its chain too. An `else` that
" opens a block (`else begin`, `end else begin`) is not stepped over:
" the line above it sits inside that block. A multi-line control head
" above the chain head is jumped to its first line: an `else if` head
" then takes the second chain resolution, and a plain `if` head is
" itself the chain head, so the line above it is returned. The
" block-open test exempts a jumped-to head: its codes contain 'b'
" from the unclosed paren, not from a `begin`.
function! s:ChainHeadPrev( ln )
	let l:hd = s:ElseChainHead(a:ln)
	let l:pe = prevnonblank(l:hd - 1)
	" a multi-line control head: the line above the head is the
	" head's `)`-tail line, not the head's first line; jump to the
	" head so the tests below can see it
	let l:ch = l:pe > 0 ? s:ControlTailHead(l:pe, 0) : 0
	if l:ch > 0
		let l:pe = l:ch
	endif
	if l:pe > 0 && getline(l:pe) =~ '^\s*\%(end\s\+\)\?else\>' && (l:ch > 0 || s:ConvertToCodes(getline(l:pe)) !~ 'b')
		let l:hd = s:ElseChainHead(l:pe)
		let l:pe = prevnonblank(l:hd - 1)
	elseif l:ch > 0
		let l:pe = prevnonblank(l:pe - 1)
	endif
	return l:pe
endfunction

" Return the line number of the block/group opener matching the close at
" a:close_ln (whose codes are exactly 'e' or 'h'), counting b/f opens
" against e/h closes while walking up, or 0 if none is found.
function! s:MatchBlockOpener( close_ln )
	let l:depth = 1
	let l:ln = prevnonblank(a:close_ln - 1)
	let l:limit = 500
	while l:ln > 0 && l:limit > 0
		let l:limit -= 1
		let l:c = s:ConvertToCodes(getline(l:ln))
		let l:depth += len(substitute(l:c, '[^eh]', '', 'g')) - len(substitute(l:c, '[^bf]', '', 'g'))
		if l:depth <= 0
			return l:ln
		endif
		let l:ln = prevnonblank(l:ln - 1)
	endwhile
	return 0
endfunction

" If a block opener at a:opener_ln is the last code line inside an 'ifdef
" region that closed between it and a:close_ln, return the matching
" 'ifdef line; otherwise 0. The block is split across the 'endif: its
" opener sits inside the region, its close outside, so a line after the
" close resolves to the region's outer level (demo101).
function! s:SplitBlockIfdef( opener_ln, close_ln )
	let l:ln = prevnonblank(a:close_ln - 1)
	while l:ln > a:opener_ln
		if getline(l:ln) =~ '^\s*`\s*\cendif\>'
			let l:m = s:FindIfdefMatch(l:ln)
			if l:m > 0 && l:m <= a:opener_ln && s:RegionEndsWithBlockOpener(l:ln, l:m) == a:opener_ln
				return l:m
			endif
		endif
		let l:ln = prevnonblank(l:ln - 1)
	endwhile
	return 0
endfunction

" If a:line_num's prev1 is a statement that is itself the body of a control
" statement inside an `ifdef region (the line before prev1 is an `endif and
" AfterEndifBodyIndent says prev1 is that control's body), return the line
" the current line resolves through: the matching `ifdef for an in-region
" control, or the enclosing control head for a Form-1 tail; otherwise 0.
" Likewise if prev1 closes a begin/end (or {...}) block whose opener is
" itself such a body: the current line follows the whole if statement and
" resolves through the region. Used to resolve a line that follows such
" a body (a close or a new statement) through the region.
function! s:BodyAfterEndifIfdef( line_num )
	" an `else` continuation belongs to the if statement above it, not to
	" the line after the body: it aligns with its `if` via the normal
	" rules and must never be yanked to the region's outer level
	if getline(a:line_num) =~ '^\s*else\>'
		return 0
	endif
	let l:p1 = prevnonblank(a:line_num - 1)
	if l:p1 <= 0
		return 0
	endif
	" a directive line is not a body (but a macro call is: only the known
	" directive keywords are excluded, not every backtick-led line)
	let l:p1_line = getline(l:p1)
	if l:p1_line =~ '^\s*`\s*\c\(ifdef\|ifndef\|elsif\|else\|endif\|define\|undef\|include\)\>'
		return 0
	endif
	let l:p1_codes = s:ConvertToCodes(l:p1_line)
	" p1 opens a block, is itself a bare control head, or is a control
	" tail: the current line belongs to p1's construct, not to the
	" region outside the `endif. A complete single-line if (`if (c)
	" y;', codes ending in ';') is still a body: only a bare head
	" (codes ending in 'x') is excluded. The tail test is ungated
	" (require_preproc 0): a multi-line head directly above the
	" region crosses no directive, and without the gate its `)`-tail
	" line (codes 'e') would fall into the block-close path below,
	" match the head as if it were a `begin`, and yank the head's
	" own body out to the region's outer level.
	if l:p1_codes =~ '[b]' || l:p1_codes =~ s:LINE_INDENT || s:ControlTailHead(l:p1, 0) > 0
		return 0
	endif
	if l:p1_codes =~ '^[he]$'
		" p1 closes a block: resolve through the region only if the
		" matching opener is itself the body-after-endif, directly
		" or as the body of a bare control head that is
		let l:op = s:MatchBlockOpener(l:p1)
		if l:op <= 0
			return 0
		endif
		" the opener may itself be an `else` continuation (else begin):
		" resolve from the first `if` of its chain
		let l:ope = s:ChainHeadPrev(l:op)
		let l:ope_endif = l:ope > 0 ? s:ChainToEndif(l:ope) : 0
		if l:ope_endif > 0
			let l:m = s:FindIfdefMatch(l:ope_endif)
			let l:res = l:m > 0 ? s:RegionExitLine(l:ope_endif, l:m) : 0
			if l:res > 0
				return l:res
			endif
		endif
		" the opener may be the last code line inside an 'ifdef region
		" that closed between it and the close (demo101): the block is
		" split across the 'endif, so the line after the close sits at
		" the region's outer level, not at the close's indent
		let l:sp = s:SplitBlockIfdef(l:op, a:line_num)
		if l:sp > 0
			return l:sp
		endif
		return 0
	endif
	if l:p1_codes =~ '[he]'
		return 0
	endif
	" p1 is a completed statement directly after an `endif, or the body
	" of a chain of bare control heads hanging off an `endif, or the
	" tail of an if/else-if chain whose first `if` is such a body
	" (transitive: the current line follows the whole if statement)
	let l:pe = s:ChainHeadPrev(l:p1)
	let l:pe_endif = l:pe > 0 ? s:ChainToEndif(l:pe) : 0
	if l:pe_endif > 0
		let l:m = s:FindIfdefMatch(l:pe_endif)
		let l:res = l:m > 0 ? s:RegionExitLine(l:pe_endif, l:m) : 0
		if l:res > 0
			return l:res
		endif
	endif
	return 0
endfunction

" If a:line_num belongs to a split function/task PROTOTYPE declaration
" (e.g. 'extern function ...' on one line, and '(' or continuation on the
" next), return the line number of the prototype's opening line; otherwise 0.
" Stops if a statement boundary (';', '{', '}', group openers/closers) is hit.
" If a:line_num belongs to a split function/task PROTOTYPE declaration
" (e.g. 'extern function ...' on one line, and '(' or continuation on the
" next), return the line number of the prototype's opening line; otherwise 0.
" Stops if a statement boundary (';', '{', '}', group openers/closers) is hit.
function! s:PrototypeSigHead( line_num )
	let l:ln = prevnonblank(a:line_num - 1)
	let l:limit = 6
	while l:ln > 0 && l:limit > 0
		let l:l = getline(l:ln)
		let l:clean = substitute(l:l, '\".\{-}\"', '', 'g')
		let l:clean = substitute(l:clean, '\/\/.*', '', '')
		if l:clean =~ '[;{}]' || l:clean =~ '^\s*`'
			return 0
		endif
		if l:clean =~ '\<\%(end\|endclass\|endfunction\|endtask\|endgroup\|endmodule\|endinterface\|endpackage\)\>'
			return 0
		endif
		if l:clean =~ '\<\%(function\|task\)\>'
			return l:ln
		endif
		let l:ln = prevnonblank(l:ln - 1)
		let l:limit -= 1
	endwhile
	return 0
endfunction

" If a:line_num is a continuation of a multi-line function/task PROTOTYPE's
" argument list, return the column (0-based) to align it to - the character
" right after the signature's opening '(' - so every argument line, and the
" closing ');', aligns its type keyword under the first argument. Returns 0
" otherwise. A definition (whose 'function'/'task' still carries an 'f')
" stops the walk, as does a line that opens a '(' itself or sits past the
" list's closing ')'.
function! s:SigArgColumn( line_num )
	let l:l0 = substitute(getline(a:line_num), '\".\{-}\"', '', 'g')
	let l:l0 = substitute(l:l0, '\/\/.*', '', '')
	let l:net0 = len(substitute(l:l0, '[^(]', '', 'g')) - len(substitute(l:l0, '[^)]', '', 'g'))
	if l:net0 > 0
		return 0
	endif
	" the line above must end with a continuation character (',' '(' '[' '{'):
	" signature argument lines follow a ','-ending head. Without this guard
	" every ordinary body line would walk to the top of the file, making a
	" whole-buffer re-indent O(n^2).
	if prevnonblank(a:line_num - 1) == 0 || getline(prevnonblank(a:line_num - 1)) !~ '[,([{]\s*$'
		return 0
	endif
	let l:bal = 0
	let l:ln = prevnonblank(a:line_num - 1)
	let l:limit = 40
	while l:ln > 0 && l:limit > 0
		let l:l = substitute(getline(l:ln), '\".\{-}\"', '', 'g')
		let l:l = substitute(l:l, '\/\/.*', '', '')
		let l:net = len(substitute(l:l, '[^(]', '', 'g')) - len(substitute(l:l, '[^)]', '', 'g'))
		let l:bal = l:bal + l:net
		if l:bal < 0
			return 0
		endif
		if l:net > 0
			" the line that opened the enclosing '('
			if l:l =~ '\<\%(function\|task\)\>'
				return stridx(l:l, '(') + 1
			endif
			" the '(' may be split onto its own line below the signature
			" ('extern ... function ... name' / '(')
			if l:l =~ '^\s*('
				let l:head = s:PrototypeSigHead(l:ln)
				if l:head > 0
					return stridx(l:l, '(') + 1
				endif
			endif
			return 0
		endif
		let l:ln = prevnonblank(l:ln - 1)
		let l:limit -= 1
	endwhile
	return 0
endfunction

" Enclosing code level for code after a closed `ifdef region: walk back
" from the matching `ifdef to the first code line before the region, and
" return the level a plain statement after that line would take. If that
" level is below the `ifdef line's own indent, the region's ifdef level
" is inflated (e.g. nested ifdefs at column 0 inside a function) and
" code after the region must return to the enclosing level, or every
" sequential region leaks +shiftwidth.
function! s:EnclosingCodeIndent( ifdef_line )
	if !exists('b:sv_enc_cache') || b:sv_enc_tick != b:changedtick
		let b:sv_enc_cache = {}
		let b:sv_enc_tick = b:changedtick
	endif
	if has_key(b:sv_enc_cache, a:ifdef_line)
		return b:sv_enc_cache[a:ifdef_line]
	endif
	let l:depth = 0
	let l:ln = prevnonblank(a:ifdef_line - 1)
	while l:ln > 0
		let l:l = getline(l:ln)
		if l:l =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/'
			let l:ln = prevnonblank(l:ln - 1)
			continue
		endif
		if l:l =~ '^\s*`\s*\cendif\>'
			let l:depth += 1
			let l:ln = prevnonblank(l:ln - 1)
			continue
		endif
		if l:l =~ '^\s*`\s*\c\(ifdef\|ifndef\)\>'
			if l:depth > 0
				let l:depth -= 1
				let l:ln = prevnonblank(l:ln - 1)
				continue
			endif
			let b:sv_enc_cache[a:ifdef_line] = indent(l:ln) + &shiftwidth
			return indent(l:ln) + &shiftwidth
		endif
		if l:l =~ '^\s*`'
			let l:ln = prevnonblank(l:ln - 1)
			continue
		endif
		if l:depth > 0
			let l:ln = prevnonblank(l:ln - 1)
			continue
		endif
		let l:prev2 = s:GetPrevWholeLineNum(l:ln)
		let b:sv_enc_cache[a:ifdef_line] = s:GetCodeIndent(indent(l:ln), s:ConvertToCodes(s:GetWholeLine(l:prev2)), s:ConvertToCodes(s:GetWholeLine(l:ln)), '')
		return b:sv_enc_cache[a:ifdef_line]
	endwhile
	let b:sv_enc_cache[a:ifdef_line] = 0
	return 0
endfunction

" If a:line_num is a bare ');' line closing a multi-line signature or
" call, return the head line that opened the paren (paren-balance walk,
" strings and //-comments stripped); otherwise 0.
function! s:SigTailHead( line_num )
	if getline(a:line_num) !~ '^\s*);\s*$'
		return 0
	endif
	let l:bal = -1
	let l:ln = prevnonblank(a:line_num - 1)
	let l:limit = 200
	while l:ln > 0 && l:limit > 0
		let l:l = substitute(getline(l:ln), '".\{-}"', '', 'g')
		let l:l = substitute(l:l, '//.*', '', '')
		let l:bal = l:bal + len(substitute(l:l, '[^(]', '', 'g')) - len(substitute(l:l, '[^)]', '', 'g'))
		if l:bal >= 0
			return l:ln
		endif
		let l:ln = prevnonblank(l:ln - 1)
		let l:limit -= 1
	endwhile
	return 0
endfunction

function! s:RollNet( line_num )
	if has_key(b:sv_roll_nets, a:line_num)
		return b:sv_roll_nets[a:line_num]
	endif
	let l:l = substitute(getline(a:line_num), '".\{-}"', '', 'g')
	let l:l = substitute(l:l, '//.*', '', '')
	let l:net = len(substitute(l:l, '[^(]', '', 'g')) - len(substitute(l:l, '[^)]', '', 'g'))
	let b:sv_roll_nets[a:line_num] = l:net
	return l:net
endfunction

function! s:RollReset()
	let b:sv_roll_tick = b:changedtick
	let b:sv_roll_last = -1
	let b:sv_roll_top = 1
	let b:sv_roll_ifdefs = []
	let b:sv_roll_match = {}
	let b:sv_roll_nets = {}
	let b:sv_roll_sig = 0
	let b:sv_roll_first = 0
	let b:sv_roll_run = 0
	let b:sv_roll_codelines = []
	let b:sv_roll_ucodes = {}
	let b:sv_roll_uindent = {}
	let b:sv_roll_incomment = 0
	let b:sv_roll_pend = -1
	let b:sv_roll_pend_ic = 0
	let b:sv_roll_prevnb = 0
endfunction

function! s:RollEndsBs( line_num )
	let l:l = getline(a:line_num)
	return strlen(l:l) > 0 && strpart(l:l, strlen(l:l) - 1, 1) == '\'
endfunction

" 1 while the chain is intact: called for consecutive non-blank lines from
" line 1 with an unchanged changedtick (blank lines are skipped by Vim's
" = operator, so a gap of blank lines is fine).
function! s:RollChainOk( line_num )
	if a:line_num <= 1
		return 0
	endif
	if b:sv_roll_tick != b:changedtick || b:sv_roll_last < 0 || !b:sv_roll_top
		return 0
	endif
	if a:line_num == b:sv_roll_last + 1
		return 1
	endif
	if a:line_num > b:sv_roll_last
		let l:ln = b:sv_roll_last + 1
		while l:ln < a:line_num
			if getline(l:ln) !~ '^\s*$'
				return 0
			endif
			let l:ln += 1
		endwhile
		return 1
	endif
	return 0
endfunction

" Maintain rolling state for line a:line_num (indent a:indnt, computed by
" either path). Seeds a new chain at line 1; continues a valid chain;
" anything else invalidates the chain and leaves state alone.
function! s:RollUpdate( line_num, indnt )
	if a:line_num == 1
		call s:RollReset()
	elseif b:sv_roll_tick != b:changedtick || b:sv_roll_last < 0 || !b:sv_roll_top
		return
	elseif a:line_num <= b:sv_roll_last
		let b:sv_roll_last = -1
		let b:sv_roll_top = 0
		return
	else
		let l:ln = b:sv_roll_last + 1
		while l:ln < a:line_num
			if getline(l:ln) !~ '^\s*$'
				let b:sv_roll_last = -1
				let b:sv_roll_top = 0
				return
			endif
			let l:ln += 1
		endwhile
	endif
	" a -1 result means 'keep the current indent' (Vim keeps the line as-is,
	" e.g. indent(0) is -1 when there is no code above); the line's real
	" indent is its current buffer indent, so normalize before recording it.
	let l:eff = a:indnt < 0 ? indent(a:line_num) : a:indnt
	let l:line = getline(a:line_num)
	let l:blank = (l:line =~ '^\s*$')
	let l:ends_bs = s:RollEndsBs(a:line_num)
	let l:prev_bs = (a:line_num > 1 && s:RollEndsBs(a:line_num - 1))
	if !l:blank
		let b:sv_roll_prevnb = a:line_num
	endif
	" backslash unit bookkeeping: a unit closes on the first line that does
	" not end with '\' (a blank line closes a pending unit as its last line)
	if l:ends_bs
		if b:sv_roll_pend < 0
			let b:sv_roll_pend = a:line_num
			let b:sv_roll_pend_ic = b:sv_roll_incomment
		endif
	elseif !l:blank || b:sv_roll_pend >= 0
		let l:ustart = b:sv_roll_pend >= 0 ? b:sv_roll_pend : a:line_num
		let l:uic = b:sv_roll_pend >= 0 ? b:sv_roll_pend_ic : b:sv_roll_incomment
		let l:utext = s:GetWholeLine(l:ustart)
		let l:ucodes = s:ConvertToCodes(l:utext)
		" a unit is comment-only when it carries no code outside
		" the comment markers: a unit starting inside a comment
		" counts only with code AFTER the closing "*/" (demo103);
		" a unit starting outside counts when any code letter
		" survives the markers (a "begin /*" opener included).
		let l:ucode = s:BoundaryHasCode(l:utext)
		let l:uafter = s:CodeAfterClose(l:utext)
		if !(l:ucodes =~ s:LINE_COMMENT || l:ucodes =~ s:PREPROCESSOR || (l:uic && !l:uafter) || (!l:uic && !l:ucode && (l:ucodes =~ s:BLOCK_COMMENT_START || l:ucodes =~ s:BLOCK_COMMENT_STOP)))
			call add(b:sv_roll_codelines, l:ustart)
			let b:sv_roll_ucodes[l:ustart] = l:ucodes
			let b:sv_roll_uindent[l:ustart] = (l:ustart == a:line_num ? l:eff : indent(l:ustart))
		endif
		let b:sv_roll_pend = -1
	endif
	" classification from raw text (mirrors the slow path's walks, which
	" read physical lines, including continuation lines of `define bodies)
	" Directives inside a multi-line `define body are macro text, not
	" real conditional compilation: they must not touch the ifdef stack,
	" the match dict, the run count, or sig/first.
	" Likewise a line whose unit started inside a /* */ block comment
	" is comment text, not a directive (a `define in the middle of a
	" /* */ block starts with a backtick, so the comment-text check
	" below does not catch it). l:uic is that block-comment state; it
	" is only set in the elseif branch, so define it here when the
	" line ends with a backslash and the if branch ran instead.
	if !exists('l:uic')
		let l:uic = b:sv_roll_pend >= 0 ? get(b:, 'sv_roll_pend_ic', 0) : get(b:, 'sv_roll_incomment', 0)
	endif
	if !l:blank && s:DefineBodyStart(a:line_num) == 0 && !l:uic
		if l:line =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/'
			" comment line: sig/first/run/stack untouched
		elseif l:line =~ '^\s*`\s*\cinclude\>'
			let b:sv_roll_first = a:line_num
		elseif l:line =~ '^\s*`\s*\c\(ifdef\|ifndef\)\>'
			let b:sv_roll_sig = a:line_num
			let b:sv_roll_first = a:line_num
			let b:sv_roll_run += 1
			call add(b:sv_roll_ifdefs, [a:line_num, l:eff])
		elseif l:line =~ '^\s*`\s*\cendif\>'
			let b:sv_roll_sig = a:line_num
			let b:sv_roll_first = a:line_num
			let b:sv_roll_run -= 1
			if !empty(b:sv_roll_ifdefs)
				let l:op = remove(b:sv_roll_ifdefs, -1)
				let b:sv_roll_match[a:line_num] = l:op[0]
			endif
		elseif l:line =~ '^\s*`\s*\c\(ifdef\|ifndef\|elsif\|else\)\>'
			let b:sv_roll_sig = a:line_num
			let b:sv_roll_first = a:line_num
		elseif l:line =~ '^\s*`'
			let b:sv_roll_sig = a:line_num
			let b:sv_roll_first = a:line_num
		else
			let b:sv_roll_sig = a:line_num
			let b:sv_roll_first = a:line_num
			let b:sv_roll_run = 0
		endif
	endif
	" forward block-comment state from physical-line codes, like the slow
	" path's block-comment block; continuation lines never reach it there
	if !l:prev_bs
		let l:pcodes = s:ConvertToCodes(l:line)
		if l:pcodes =~ s:BLOCK_COMMENT_STOP_ANY
			let b:sv_roll_incomment = 0
		elseif l:pcodes =~ s:BLOCK_COMMENT_START
			let b:sv_roll_incomment = 1
		endif
	endif
	let b:sv_roll_last = a:line_num
endfunction

function! s:RollTailHead( line_num )
	let l:line = getline(a:line_num)
	if l:line !~ ')\s*;\?\s*$'
		return 0
	endif
	if l:line =~ '^\s*[;)}]'
	  \ || l:line =~ '^\s*\%(end\|endcase\|endgenerate\|endmodule\|endinterface\|endpackage\|endclass\|endfunction\|endtask\|endgroup\|endproperty\|endsequence\|endchecker\|endconfig\|endclocking\|endspecify\|join\|join_any\|join_none\)\>'
		return 0
	endif
	if prevnonblank(a:line_num - 1) == 0 || getline(prevnonblank(a:line_num - 1)) !~ '[,([{]\s*$'
		return 0
	endif
	let l:bal = 0
	" the tail must close more parens than it opens (it closes the head's
	" open paren); a balanced or opening line is not a closing tail
		let l:bal = s:RollNet(a:line_num)
	if l:bal >= 0
		return 0
	endif
	let l:ln = prevnonblank(a:line_num - 1)
	let l:limit = 200
	while l:ln > 0 && l:limit > 0
			let l:bal = l:bal + s:RollNet(l:ln)
		if l:bal >= 0
			return l:ln
		endif
		let l:ln = prevnonblank(l:ln - 1)
		let l:limit -= 1
	endwhile
	return 0
endfunction

function! s:RollSigTailHead( line_num )
	if getline(a:line_num) !~ '^\s*);\s*$'
		return 0
	endif
	let l:bal = -1
	let l:ln = prevnonblank(a:line_num - 1)
	let l:limit = 200
	while l:ln > 0 && l:limit > 0
		let l:bal = l:bal + s:RollNet(l:ln)
		if l:bal >= 0
			return l:ln
		endif
		let l:ln = prevnonblank(l:ln - 1)
		let l:limit -= 1
	endwhile
	return 0
endfunction

function! s:RollSigArgColumn( line_num )
		let l:net0 = s:RollNet(a:line_num)
	if l:net0 > 0
		return 0
	endif
	" the line above must end with a continuation character (',' '(' '[' '{'):
	" signature argument lines follow a ','-ending head. Without this guard
	" every ordinary body line would walk to the top of the file, making a
	" whole-buffer re-indent O(n^2).
	if prevnonblank(a:line_num - 1) == 0 || getline(prevnonblank(a:line_num - 1)) !~ '[,([{]\s*$'
		return 0
	endif
	let l:bal = 0
	let l:ln = prevnonblank(a:line_num - 1)
	let l:limit = 40
	while l:ln > 0 && l:limit > 0
		let l:l = substitute(getline(l:ln), '\".\{-}\"', '', 'g')
		let l:l = substitute(l:l, '\/\/.*', '', '')
		let l:net = s:RollNet(l:ln)
		let l:bal = l:bal + l:net
		if l:bal < 0
			return 0
		endif
		if l:net > 0
			" the line that opened the enclosing '('
			if l:l =~ '\<\%(function\|task\)\>'
				return stridx(l:l, '(') + 1
			endif
			" the '(' may be split onto its own line below the signature
			" ('extern ... function ... name' / '(')
			if l:l =~ '^\s*('
				let l:head = s:PrototypeSigHead(l:ln)
				if l:head > 0
					return stridx(l:l, '(') + 1
				endif
			endif
			return 0
		endif
		let l:ln = prevnonblank(l:ln - 1)
		let l:limit -= 1
	endwhile
	return 0
endfunction

" Preprocessor indent from rolling state. Mirrors s:GetPreprocIndent:
" opener after a closed region aligns with that region's opener
" (sv_roll_match), otherwise base + trailing-directive-run * sw;
" any other directive aligns with the innermost open `ifdef (stack top).
function! s:RollPreprocIndent( line_num, base_indnt )
	let l:line = getline(a:line_num)
	if l:line =~ '^\s*`\s*\c\(ifdef\|ifndef\)\>'
		let l:first = b:sv_roll_first
		if l:first > 0 && getline(l:first) =~ '^\s*`\s*\cendif\>'
			if has_key(b:sv_roll_match, l:first)
				return indent(b:sv_roll_match[l:first])
			endif
			return a:base_indnt
		endif
		return a:base_indnt + b:sv_roll_run * &shiftwidth
	endif
	" `include inside an `ifdef body: a body line like any statement, so
	" sit at the code level (base_indnt), not at the opener level like a
	" closer. Reached when the previous line is code (RollFastIndent's
	" include branch only returns early after a directive sig). But a
	" file guard's body stays at the guard level (demo16), so a guard
	" `include keeps the stack-top level below.
	if l:line =~ '^\s*`\s*\cinclude\>'
		if !empty(b:sv_roll_ifdefs) && s:IsFileGuard(b:sv_roll_ifdefs[-1][0])
			return b:sv_roll_ifdefs[-1][1]
		endif
		return a:base_indnt
	endif
	if !empty(b:sv_roll_ifdefs)
		return b:sv_roll_ifdefs[-1][1]
	endif
	return a:base_indnt
endfunction

" Plain-line fast lane: a plain statement following a plain statement.
" Returns its indent, or -1 to fall through to the normal path. For
" such a line GetCodeIndent returns the base unchanged, so the indent
" is the previous plain line's (already correct) indent, and the
" rolling-state update is minimal: append to the code-unit list with
" codes ';', set sig/first to this line and the directive-run count to
" 0, leave the ifdef stack and block-comment state untouched. Skips
" RollFastIndent, RollUpdate and every ConvertToCodes call for the line.
function! s:RollPlainLine( line_num )
	if b:sv_roll_tick != b:changedtick || b:sv_roll_last < 0 || !b:sv_roll_top
		return -1
	endif
	if b:sv_roll_incomment
		return -1
	endif
	let l:line = getline(a:line_num)
	if l:line =~ '^\s*$'
		return -1
	endif
	if !s:IsPlainStmt(l:line)
		return -1
	endif
	let l:prev = prevnonblank(a:line_num - 1)
	" previous line must be a plain exec unit: its memoized unit codes
	" are ';' (directives/comments never enter that dict). Cheaper and
	" more accurate than re-running the text check on it.
	if l:prev <= 0 || get(b:sv_roll_ucodes, l:prev, '') !=# ';'
		return -1
	endif
	if s:RollEndsBs(a:line_num) || s:RollEndsBs(l:prev)
		return -1
	endif
	if s:DefineBodyStart(a:line_num) != 0
		return -1
	endif
	" a plain statement after a body-after-endif (Form 2) resolves
	" through the region in the full path; this shortcut's one-level
	" dedent from the body indent lands one level too deep. The chain
	" pre-check keeps the common case cheap: from the line before prev
	" (or before the first `if` of prev's else-chain, stepping over a
	" bare `else` when prev is that branch's body), walk up over bare
	" control heads to an `endif; only then run the full check.
	let l:pe = s:ChainHeadPrev(l:prev)
	if l:pe > 0 && s:ChainToEndif(l:pe) > 0 && s:BodyAfterEndifIfdef(a:line_num) > 0
		return -1
	endif
	" gap check (only blank lines may intervene; the chain is in order)
	if a:line_num != b:sv_roll_last + 1
		let l:ln = b:sv_roll_last + 1
		while l:ln < a:line_num
			if getline(l:ln) !~ '^\s*$'
				return -1
			endif
			let l:ln += 1
		endwhile
	endif
	" GetCodeIndent's dedent rule: prev2 ends with 'x' (a control line)
	" and prev1 is an exec line (';') -> one level back. prev is the
	" last code unit, so the unit before it is prev2's unit. A control
	" tail (multi-line condition ending in ')') counts as the control
	" line, mirroring the override in the full paths.
	let l:ind = indent(l:prev)
	if len(b:sv_roll_codelines) >= 2 && b:sv_roll_codelines[-1] == l:prev
		let l:p2codes = get(b:sv_roll_ucodes, b:sv_roll_codelines[-2], '')
		if l:p2codes =~ s:LINE_INDENT || s:ControlTailHead(b:sv_roll_codelines[-2]) > 0
			let l:ind = l:ind - &shiftwidth
		endif
	elseif len(b:sv_roll_codelines) < 2
		" no prev2 unit: no dedent possible, keep indent(prev)
	else
		" prev is not the last unit: state assumption broken, bail out
		return -1
	endif
	let b:sv_roll_prevnb = a:line_num
	call add(b:sv_roll_codelines, a:line_num)
	let b:sv_roll_ucodes[a:line_num] = ';'
	let b:sv_roll_uindent[a:line_num] = l:ind
	let b:sv_roll_sig = a:line_num
	let b:sv_roll_first = a:line_num
	let b:sv_roll_run = 0
	let b:sv_roll_last = a:line_num
	return l:ind
endfunction

" Rolling single-pass fast path for gg=G. Mirrors s:SlowIndent step by step,
" reading rolling state instead of walking back; returns -1 to fall back to
" the slow path whenever the state cannot answer exactly.
function! s:RollFastIndent( line_num )
	let l:N = a:line_num
	let l:line = getline(l:N)
	if l:line =~ '^\s*$'
		return -1
	endif
	if s:RollEndsBs(l:N - 1)
		return -1
	endif
	if b:sv_roll_incomment
		return -1
	endif
	" macro call containing `inside {...}` sets: the rolling code-unit
	" bookkeeping miscounts these (phy_common 14290: fast [28] vs slow
	" [4]); fall back to the slow path, which handles inside sets
	" correctly (v9 pre-drop in ConvertToCodes)
	if l:line =~ '^\s*`' && l:line =~ '\<inside\>'
		return -1
	endif
	if empty(b:sv_roll_codelines)
		return -1
	endif
	let l:this_codes = s:ConvertToCodes(l:line)
	let l:sw = &shiftwidth
	" --- preprocessor-continuation loops (sig = first non-skip line above) ---
	let l:prev_start = l:N
	let l:sig = b:sv_roll_sig
	let l:sig_is_endif = (l:sig > 0 && getline(l:sig) =~ '^\s*`\s*\cendif\>')
	let l:sig_is_ifdef = (l:sig > 0 && getline(l:sig) =~ '^\s*`\s*\c\(ifdef\|ifndef\|elsif\|else\)\>')
	let l:sig_is_define = (l:sig > 0 && getline(l:sig) =~ '^\s*`\s*\c\(define\|undef\)\>')
	let l:is_include = (l:line =~ '^\s*`\s*\cinclude\>')
	let l:is_bigdir = (l:line =~ '^\s*`\s*\c\(begin_keywords\|celldefine\|default_nettype\|else\|elsif\|end_keywords\|endcelldefine\|endif\|ifdef\|ifndef\|include\|nounconnected_drive\|pragma\|resetall\|timescale\|unconnected_drive\|undefineall\)\>')
	if l:is_include
		if l:sig_is_endif
			let l:m = get(b:sv_roll_match, l:sig, 0)
			if l:m > 0
				let l:enc = s:EnclosingCodeIndent(l:m)
				return l:enc < indent(l:m) ? l:enc : indent(l:m)
			endif
		elseif l:sig_is_ifdef
			return indent(l:sig) + l:sw
		endif
	elseif !l:is_bigdir
		" a line after a body-after-endif: prev1 is itself the body of a
		" control statement that is the last code line inside an `ifdef
		" region (demo84 Form 2). A bare close resolves through the
		" region like a close directly after the `endif; a regular
		" statement sits at the region's outer level.
		let l:baef = s:BodyAfterEndifIfdef(l:N)
		if l:baef > 0
			if l:this_codes =~ '^[he]$'
				let l:prev_start = l:baef
				let l:prev_start = s:PrevCodeLine(l:prev_start)
			else
				let l:enc = s:EnclosingCodeIndent(l:baef)
				return l:enc < indent(l:baef) ? l:enc : indent(l:baef)
			endif
		endif
		if l:sig_is_endif
			let l:m = get(b:sv_roll_match, l:sig, 0)
			if l:m > 0
				" a bare block close (end, not a group close) after an
				" 'endif whose region ends with a block opener closes
				" that opener: align with it instead of resolving
				" through the region (demo101)
				if l:this_codes ==# 'e'
					let l:op = s:RegionEndsWithBlockOpener(l:sig, l:m)
					if l:op > 0
						return indent(l:op)
					endif
				endif
				if l:this_codes =~ '^[he]$'
					let l:prev_start = l:m
					let l:prev_start = s:PrevCodeLine(l:prev_start)
				else
					" a statement after an `endif may be the body of a
					" control statement that is the last code line
					" inside the region (demo84 Form 2)
					let l:bind = s:AfterEndifBodyIndent(l:sig, l:m)
					if l:bind >= 0
						return l:bind
					endif
					let l:enc = s:EnclosingCodeIndent(l:m)
					return l:enc < indent(l:m) ? l:enc : indent(l:m)
				endif
			endif
		elseif l:sig_is_ifdef
			if l:this_codes =~ '^[he]$'
				let l:prev_start = l:sig
			elseif l:line =~ '^\s*`\s*\cdefine\>'
				" a `define after an `ifdef/`ifndef (the file-guard idiom)
				" aligns with the `ifdef, not one level deeper
				return indent(l:sig)
			else
				" a condition continuation split across branches must see
				" the code before the `ifdef, not indent+sw off the
				" directive: fall through to the prev1/prev2 resolution
				" below when PrevBeforeBranch would redirect this line
				let l:pp = prevnonblank(l:sig - 1)
				if !(l:pp > 0 && s:PrevBeforeBranch(l:pp, l:N) != l:pp)
					return indent(l:sig) + l:sw
				endif
			endif
		elseif l:sig_is_define
			" the sig is a `define: resolve through it to the directive
			" before it. A `define after an `endif means the next line
			" sits at the closed region's outer level; a `define after
			" an `ifdef (guard idiom) or after code means the next line
			" aligns with the `define itself.
			" Only when the sig is fresh: lines inside a /* */ comment
			" or a `define body do not update sig, so it can go stale
			" (e.g. a file-guard `define far above a line inside a
			" commented-out macro body). If any line between the sig
			" and here is not blank and not a comment line, fall
			" through to the normal prev1/prev2 resolution instead.
			let l:fresh = 1
			let l:j = l:sig + 1
			while l:j < l:N
				let l:jl = getline(l:j)
				if l:jl !~ '^\s*$' && l:jl !~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/'
					let l:fresh = 0
					break
				endif
				let l:j += 1
			endwhile
			if l:fresh
			" walk back through a run of `define/`undef lines to the
			" directive before the whole run (a `define after an `undef
			" after an `endif, demo33, resolves through the run to the
			" closed region, not just to the `undef)
			let l:prev_sig = prevnonblank(l:sig - 1)
			while l:prev_sig > 0 && getline(l:prev_sig) =~ '^\s*`\s*\c\(define\|undef\)\>'
				let l:prev_sig = prevnonblank(l:prev_sig - 1)
			endwhile
				if l:prev_sig > 0 && getline(l:prev_sig) =~ '^\s*`\s*\cendif\>'
					let l:m = get(b:sv_roll_match, l:prev_sig, 0)
					if l:m > 0
						if l:this_codes =~ '^[he]$'
							let l:prev_start = l:m
							let l:prev_start = s:PrevCodeLine(l:prev_start)
						else
							let l:enc = s:EnclosingCodeIndent(l:m)
							return l:enc < indent(l:m) ? l:enc : indent(l:m)
						endif
					endif
				else
					" `define after an `ifdef (guard idiom) or after code:
					" fall through to the normal prev1/prev2 +
					" GetCodeIndent path, which distinguishes a flat
					" top-level unit (package/module, [0]) from an
					" indented declaration (typedef, [2]). Returning
					" indent(sig) here would flatten the latter.
					if l:this_codes =~ '^[he]$'
						let l:prev_start = l:sig
					endif
				endif
			endif
		endif
	endif
	" --- prev1 / prev2 from the rolling code-unit list ---
	let l:p1 = -1
	let l:p2 = -1
	let l:i = len(b:sv_roll_codelines) - 1
	while l:i >= 0
		if b:sv_roll_codelines[l:i] < l:prev_start
			let l:p1 = b:sv_roll_codelines[l:i]
			if l:i > 0
				let l:p2 = b:sv_roll_codelines[l:i - 1]
			endif
			break
		endif
		let l:i -= 1
	endwhile
	if l:p1 < 0
		return -1
	endif
	" a line in a branch after `else/`elsif must see the code before
	" the `ifdef, not the sibling branch's lines, when it closes the
	" shared condition or continues it (s:PrevBeforeBranch decides);
	" prev2 follows from the new prev1's position in the rolling list
	if l:p1 > 0
		let l:np1 = s:PrevBeforeBranch(l:p1, l:N)
		if l:np1 > 0 && l:np1 != l:p1 && has_key(b:sv_roll_ucodes, l:np1)
			let l:p1 = l:np1
			let l:p2 = -1
			let l:j = len(b:sv_roll_codelines) - 1
			while l:j >= 0
				if b:sv_roll_codelines[l:j] == l:p1
					if l:j > 0
						let l:p2 = b:sv_roll_codelines[l:j - 1]
					endif
					break
				endif
				let l:j -= 1
			endwhile
		endif
	endif
	let l:p1line = getline(l:p1)
	if l:p1line =~ '\<endfunction\>' && stridx(l:p1line, ');') >= 0
		return -1
	endif
	let l:p1_codes = s:StripPrototypeF(l:p1, s:GetWholeLine(l:p1), b:sv_roll_ucodes[l:p1])
	let l:p2_codes = (l:p2 > 0) ? s:StripPrototypeF(l:p2, s:GetWholeLine(l:p2), b:sv_roll_ucodes[l:p2]) : ''
	let l:this_codes = s:StripPrototypeF(l:N, l:line, l:this_codes)
	" --- macro-tail case (prev1 is a macro-call tail) ---
	let l:mhead = s:RollTailHead(l:p1)
	if l:mhead > 0 && getline(l:mhead) =~ '^\s*`'
		let l:p1_codes = ';'
		let l:p2 = s:GetPrevWholeLineNum(l:mhead)
		let l:p2_codes = s:ConvertToCodes(s:GetWholeLine(l:p2))
	endif
	" if p1 is the tail of a multi-line CONTROL statement, treat it as the
	" control line ('x') so the next line (the body) indents one level.
	" Likewise p2: after a control body, the "prev2 x + prev1 exec" rule
	" must see the control line to dedent the following statement.
	let l:chead1 = s:ControlTailHead(l:p1)
	if l:chead1 > 0
		let l:p1_codes = 'x'
	endif
	if l:p2 > 0 && s:ControlTailHead(l:p2) > 0
		let l:p2_codes = 'x'
	endif
	" --- signature argument column ---
	let l:argcol = s:RollSigArgColumn(l:N)
	if l:argcol > 0
		return l:argcol
	endif
	" --- '(' on its own line below a prototype signature ---
	if l:line =~ '^\s*('
		let l:head = s:PrototypeSigHead(l:N)
		if l:head > 0
			return indent(l:head) + l:sw
		endif
	endif
	" --- line after a signature's closing ');' ---
	let l:mhead = s:RollTailHead(l:p1)
	if l:mhead <= 0
		let l:mhead = s:RollSigTailHead(l:p1)
	endif
	if l:mhead > 0
		let l:sigline = (getline(l:mhead) =~ '\<\%(function\|task\)\>') ? l:mhead : (getline(l:mhead) =~ '^\s*(' ? s:PrototypeSigHead(l:mhead) : 0)
		if l:sigline > 0 && getline(l:sigline) =~ '\<\%(function\|task\)\>'
			let l:is_proto = (getline(l:sigline) =~ '\<\%(extern\|pure\)\>' || s:ConvertToCodes(getline(l:sigline)) !~# 'f')
			if l:is_proto
				return indent(l:sigline) - (l:this_codes =~# 'h' ? l:sw : 0)
			else
				return indent(l:sigline) + (l:this_codes =~# 'h' ? 0 : l:sw)
			endif
		endif
	endif
	" --- tail of a multi-line statement ---
	let l:mhead = s:RollTailHead(l:N)
	if l:mhead <= 0
		let l:mhead = s:RollSigTailHead(l:N)
	endif
	if l:mhead > 0
		return indent(l:mhead)
	endif
	" --- main code indent ---
	" the control head, not the (possibly deeper) condition tail, is the
	" indent base for the body
	let l:base = l:chead1 > 0 ? get(b:sv_roll_uindent, l:chead1, indent(l:chead1)) : b:sv_roll_uindent[l:p1]
	" a prev2 buried in a region that closed before prev1 must not feed
	" the "prev2 control + prev1 statement" dedent rule (s:IsStalePrev2)
	let l:p2_gci = l:p2_codes
	if l:p2 > 0 && l:p2_codes =~ s:LINE_INDENT && s:IsStalePrev2(l:p2, l:p1)
		let l:p2_gci = ''
	endif
	let l:indnt = s:GetCodeIndent(l:base, l:p2_gci, l:p1_codes, l:this_codes)
	" --- block-comment block (body/STOP lines never reach here) ---
	if l:this_codes =~ s:BLOCK_COMMENT_STOP
		let b:in_block_comment = 0
		return indent(l:N)
	endif
	if l:this_codes =~ s:BLOCK_COMMENT_START
		let b:in_block_comment = 1
		let b:block_comment_line = l:N
		let b:block_comment_change = b:changedtick
		return l:indnt
	endif
	" --- preprocessor / plain ---
	if l:this_codes =~ s:PREPROCESSOR
		return s:RollPreprocIndent(l:N, l:indnt)
	endif
	return l:indnt
endfunction

if !exists('g:sv_roll_fast')
	let g:sv_roll_fast = 1
endif

function! GetSystemVerilogIndent( line_num )
	if g:sv_roll_fast && s:RollChainOk(a:line_num)
		let l:r = s:RollPlainLine(a:line_num)
		if l:r >= 0
			return l:r
		endif
		let l:r = s:RollFastIndent(a:line_num)
		if l:r >= 0
			call s:RollUpdate(a:line_num, l:r)
			return l:r
		endif
	endif
	let l:r = s:SlowIndent(a:line_num)
	call s:RollUpdate(a:line_num, l:r)
	return l:r
endfunction

function! s:SlowIndent( line_num )
	let this_codeline = getline( a:line_num )
	let prev1_line_num = prevnonblank( a:line_num - 1)
	let prev1_codeline = getline( prev1_line_num )
	let prev2_line_num = prev1_line_num - 1
	let prev2_codeline = getline( prev2_line_num )

	let indnt = indent( prev1_line_num )

	" codes for this line, computed early: the preprocessor-continuation
	" rules below must know whether this line CLOSES a group/block.
	" end/endcase/endfunction... right after an `endif close something that
	" opened OUTSIDE the conditional region - they must resolve through the
	" region instead of aligning with it, or endfunction after a trailing
	" `ifndef...`endif block lands one level too deep. Memoized, so the
	" later s:ConvertToCodes call for the same text is free.
	let l:this_codes_early = s:ConvertToCodes( this_codeline )
	" where previous-line resolution starts: normally this line; when a
	" group/block close follows a conditional region, the matching `ifdef
	" line, so prev1 resolves to the code before the whole region
	let l:prev_start = a:line_num

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
					let l:enc = s:EnclosingCodeIndent(l:m)
					return l:enc < indent(l:m) ? l:enc : indent(l:m)
				endif
				break
			endif
			if l =~ '^\s*`\s*\c\(ifdef\|ifndef\|elsif\|else\)\>'
				return indent(ln) + &shiftwidth
			endif
			if l =~ '^\s*`\s*\cinclude\>'
				let ln = prevnonblank(ln - 1)
				continue
			endif
			break
		endwhile
	endif
	" loop over previous lines for the preprocessor-continuation rules. A
	" macro CALL line (leading `name(...)) is ordinary code for this: it
	" takes the ifdef-body +1 and the endif-alignment like any statement.
	" Only the directives themselves (the `z` codes) are excluded.
	" `define and `undef are NOT excluded: they must enter this loop so a
	" `define/`undef after an `endif resolves through the closed region
	" (residual (a) for `define; same for `undef, demo33).
	if this_codeline !~ '^\s*`\s*\c\(begin_keywords\|celldefine\|default_nettype\|else\|elsif\|end_keywords\|endcelldefine\|endif\|ifdef\|ifndef\|include\|nounconnected_drive\|pragma\|resetall\|timescale\|unconnected_drive\|undefineall\)\>'
		let ln = prevnonblank(a:line_num - 1)
		" a line after a body-after-endif: prev1 is itself the body of a
		" control statement that is the last code line inside an `ifdef
		" region (demo84 Form 2). A bare close resolves through the
		" region like a close directly after the `endif; a regular
		" statement sits at the region's outer level.
		let l:baef = s:BodyAfterEndifIfdef(a:line_num)
		if l:baef > 0
			if l:this_codes_early =~ '^[he]$'
				let l:prev_start = l:baef
				let l:prev_start = s:PrevCodeLine(l:prev_start)
			else
				let l:enc = s:EnclosingCodeIndent(l:baef)
				return l:enc < indent(l:baef) ? l:enc : indent(l:baef)
			endif
		endif
		while ln > 0
			let l = getline(ln)
			if l =~ '^\s*//\|^\s*/\*\|^\s*\*\|^\s*\*/\|^\s*`\s*\c\(include\|undef\)\>'
				let ln = prevnonblank(ln - 1)
				continue
			endif
			if l =~ '^\s*`\s*\cdefine\>'
				" the sig is a `define: resolve through it to the
				" directive before it. A `define after an `endif means
				" the next line sits at the closed region's outer level;
				" a `define after an `ifdef (guard idiom) or after code
				" means the next line aligns with the `define itself.
				let l:prev_sig = prevnonblank(ln - 1)
				if l:prev_sig > 0 && getline(l:prev_sig) =~ '^\s*`\s*\cendif\>'
					let l:m = s:FindIfdefMatch(l:prev_sig)
					if l:m > 0
						if l:this_codes_early =~ '^[he]$'
							let l:prev_start = l:m
							let l:prev_start = s:PrevCodeLine(l:prev_start)
						else
							let l:enc = s:EnclosingCodeIndent(l:m)
							return l:enc < indent(l:m) ? l:enc : indent(l:m)
						endif
					endif
					break
				else
					" `define after an `ifdef (guard idiom) or after code:
					" fall through (break) to the normal prev1/prev2 +
					" GetCodeIndent path; see RollFastIndent above.
					if l:this_codes_early =~ '^[he]$'
						let l:prev_start = ln
					endif
					break
				endif
			endif
			if l =~ '^\s*`\s*\cendif\>'
				let l:m = s:FindIfdefMatch(ln)
				if l:m > 0
					" a bare block close (end, not a group close) after an
					" 'endif whose region ends with a block opener closes
					" that opener: align with it instead of resolving
					" through the region (demo101)
					if l:this_codes_early ==# 'e'
						let l:op = s:RegionEndsWithBlockOpener(ln, l:m)
						if l:op > 0
							return indent(l:op)
						endif
					endif
					if l:this_codes_early =~ '^[he]$'
						" a bare group/block close (end, endcase,
						" endfunction, ...) after an `endif: it closes
						" something that opened before the conditional
						" region. Make the region transparent: resolve
						" the previous code from before the matching
						" `ifdef instead of aligning with it
						let l:prev_start = l:m
						let l:prev_start = s:PrevCodeLine(l:prev_start)
					else
						" a statement after an `endif may be the body of
						" a control statement that is the last code line
						" inside the region (demo84 Form 2)
						let l:bind = s:AfterEndifBodyIndent(ln, l:m)
						if l:bind >= 0
							return l:bind
						endif
						let l:enc = s:EnclosingCodeIndent(l:m)
						return l:enc < indent(l:m) ? l:enc : indent(l:m)
					endif
				endif
				break
			endif
			if l =~ '^\s*`\s*\c\(ifdef\|ifndef\|elsif\|else\)\>'
				if l:this_codes_early =~ '^[he]$'
					let l:prev_start = ln
					break
				endif
				if this_codeline =~ '^\s*`\s*\cdefine\>'
					" a `define after an `ifdef/`ifndef (the file-guard idiom)
					" aligns with the `ifdef, not one level deeper
					return indent(ln)
				endif
				" a condition continuation split across branches must see
				" the code before the `ifdef, not indent+sw off the
				" directive: fall through to the prev1 resolution below
				" when PrevBeforeBranch would redirect this line
				let l:pp = prevnonblank(ln - 1)
				if l:pp > 0 && s:PrevBeforeBranch(l:pp, a:line_num) != l:pp
					break
				endif
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
					let l:enc = s:EnclosingCodeIndent(l:m)
					return l:enc < indent(l:m) ? l:enc : indent(l:m)
				endif
				break
			endif
			if l =~ '^\s*`\s*\c\(ifdef\|ifndef\|elsif\|else\)\>'
				return indent(ln) + &shiftwidth
			endif
			if l =~ '^\s*`\s*\cinclude\>'
				let ln = prevnonblank(ln - 1)
				continue
			endif
			break
		endwhile
	endif

	let prev1_line_num = s:GetPrevWholeLineNum (l:prev_start)
	let prev1_for_comment_line = prev1_line_num
	let prev1_codeline = s:GetWholeLine (prev1_line_num)
	let prev1_codes = s:ConvertToCodes(prev1_codeline)
	" this line closes a block comment ("*/ begin"): the lines above
	" it back to the opener are comment interior, so seed the walk
	" inside the comment; otherwise prev1 lands on an interior line
	" and this line inherits its arbitrary kept indent (demo103).
	let in_comment = (l:this_codes_early =~ s:BLOCK_COMMENT_STOP_ANY) ? 1 : 0
	let l:seeded_close = in_comment
	let l:saw_comment_start = 0
	let l:orig_p1_num = prev1_line_num
	let l:orig_p1_codes = prev1_codes
	" line bound: an unterminated comment (or a stray '*/') must stop at line 1, not walk forever (demo100).
	while (prev1_line_num > 0 && (prev1_codes =~ s:LINE_COMMENT || in_comment || prev1_codes =~ s:BLOCK_COMMENT_STOP || prev1_codes =~ s:BLOCK_COMMENT_START || prev1_codes =~ s:PREPROCESSOR))
		if (prev1_codes =~ s:BLOCK_COMMENT_STOP_ANY)
			let in_comment = 1
		endif
		if (prev1_codes =~ s:BLOCK_COMMENT_START)
			let in_comment = 0
			let l:saw_comment_start = 1
		endif
		" boundary line carrying code ("begin /*", "*/ end"):
		" use it as the previous code line instead of skipping
		" past it; comment-interior lines keep skipping even
		" when their text contains keywords (demo103).
		if (prev1_codes =~ s:BLOCK_COMMENT_STOP_ANY || prev1_codes =~ s:BLOCK_COMMENT_START) && s:BoundaryHasCode(prev1_codeline) && prev1_codes !~ s:LINE_COMMENT && prev1_codes !~ s:PREPROCESSOR
			break
		endif
		let prev1_line_num = s:GetPrevWholeLineNum (prev1_line_num)
		let prev1_codeline = s:GetWholeLine (prev1_line_num)
		let prev1_codes = s:ConvertToCodes(prev1_codeline)
	endwhile
	" a stray "*/" with no opener above: the seeded walk ran off the
	" top of the file without finding a comment start; fall back to
	" the unseeded previous line (demo103).
	if l:seeded_close && !l:saw_comment_start && prev1_line_num <= 0
		let prev1_line_num = l:orig_p1_num
		let prev1_codes = l:orig_p1_codes
	endif

	" a line in a branch after `else/`elsif must see the code before
	" the `ifdef, not the sibling branch's lines, when it closes the
	" shared condition or continues it (s:PrevBeforeBranch decides)
	if prev1_line_num > 0
		let l:np1 = s:PrevBeforeBranch(prev1_line_num, a:line_num)
		if l:np1 > 0 && l:np1 != prev1_line_num
			let prev1_line_num = l:np1
			let prev1_codeline = s:GetWholeLine (prev1_line_num)
			let prev1_codes = s:ConvertToCodes(prev1_codeline)
		endif
	endif

	let prev2_line_num = s:GetPrevWholeLineNum (prev1_line_num)
	let prev2_codeline = s:GetWholeLine (prev2_line_num)
	let prev2_codes = s:ConvertToCodes(prev2_codeline)
	let in_comment = 0
	" line bound: an unterminated comment (or a stray '*/') must stop at line 1, not walk forever (demo100).
	while (prev2_line_num > 0 && (prev2_codes =~ s:LINE_COMMENT || in_comment || prev2_codes =~ s:BLOCK_COMMENT_STOP || prev2_codes =~ s:BLOCK_COMMENT_START || prev2_codes =~ s:PREPROCESSOR))
		if (prev2_codes =~ s:BLOCK_COMMENT_STOP_ANY)
			let in_comment = 1
		endif
		if (prev2_codes =~ s:BLOCK_COMMENT_START)
			let in_comment = 0
		endif
		" boundary line carrying code ("begin /*", "*/ end"):
		" use it as the previous code line instead of skipping
		" past it; comment-interior lines keep skipping even
		" when their text contains keywords (demo103).
		if (prev2_codes =~ s:BLOCK_COMMENT_STOP_ANY || prev2_codes =~ s:BLOCK_COMMENT_START) && s:BoundaryHasCode(prev2_codeline) && prev2_codes !~ s:LINE_COMMENT && prev2_codes !~ s:PREPROCESSOR
			break
		endif
		let prev2_line_num = s:GetPrevWholeLineNum (prev2_line_num)
		let prev2_codeline = s:GetWholeLine (prev2_line_num)
		let prev2_codes = s:ConvertToCodes(prev2_codeline)
	endwhile

	let prev1_codes = s:StripPrototypeF(prev1_line_num, prev1_codeline, prev1_codes)
	let prev2_codes = s:StripPrototypeF(prev2_line_num, prev2_codeline, prev2_codes)

	" if prev1 is the tail of a multi-line MACRO call, it is that statement's
	" terminator: treat it as 'exec' and resolve prev2 to the code before the
	" head, so the "prev2 x + prev1 exec" rule dedents the next line back to
	" the enclosing control level. Method-call tails keep their natural codes
	" (their open line already carries a 'b' that the normal rules balance).
	let l:mhead = s:StatementTailHead(prev1_line_num)
	if l:mhead > 0 && getline(l:mhead) =~ '^\s*`'
		let prev1_codes = ';'
		let prev2_line_num = s:GetPrevWholeLineNum(l:mhead)
		let prev2_codeline = s:GetWholeLine(prev2_line_num)
		let prev2_codes = s:ConvertToCodes(prev2_codeline)
	endif

	" if prev1 is the tail of a multi-line CONTROL statement, it is that
	" statement's terminator: treat it as the control line ('x') so the
	" next line (the body) indents one level via the LINE_INDENT rule.
	" Likewise prev2: after a control body, the "prev2 x + prev1 exec"
	" rule must see the control line to dedent the following statement.
	let l:chead1 = s:ControlTailHead(prev1_line_num)
	if l:chead1 > 0
		let prev1_codes = 'x'
	endif
	if prev2_line_num > 0 && s:ControlTailHead(prev2_line_num) > 0
		let prev2_codes = 'x'
	endif

	let this_codes = l:this_codes_early
	let this_codes = s:StripPrototypeF(a:line_num, this_codeline, this_codes)

	" a continuation of a multi-line function/task PROTOTYPE signature aligns
	" its argument list to the '(' column (column alignment, not shiftwidth)
	let l:argcol = s:SigArgColumn(a:line_num)
	if l:argcol > 0
		return l:argcol
	endif

	" if this line opens '(' on its own line below a prototype signature
	" ('extern static function ...' on prev line, '(' on this line),
	" indent it one shiftwidth under the declaration
	if this_codeline =~ '^\s*('
		let l:head = s:PrototypeSigHead(a:line_num)
		if l:head > 0
			return indent(l:head) + &shiftwidth
		endif
	endif

	" if prev1 contains a same-line '...); endfunction' tail, return to the
	" function declaration's level
	if getline(prev1_line_num) =~ '\<endfunction\>' && getline(prev1_line_num) =~ ');'
		let l:ln = prevnonblank(prev1_line_num - 1)
		while l:ln > 0
			let l:l = getline(l:ln)
			if l:l =~ '\<\%(function\|task\)\>'
				return indent(l:ln)
			endif
			if l:l =~ '[;{}]' || l:l =~ '\<endclass\>'
				break
			endif
			let l:ln = prevnonblank(l:ln - 1)
		endwhile
	endif

	" the line after a signature's closing ');': a PROTOTYPE's next
	" declaration returns to the signature's level (a group stop one further
	" out); a DEFINITION's body sits one level in, its endfunction back at
	" the function's own level
	let l:mhead = s:StatementTailHead(prev1_line_num)
	if l:mhead <= 0
		let l:mhead = s:SigTailHead(prev1_line_num)
	endif
	if l:mhead > 0
		" the '(' may sit on its own line below the 'function/task ... name'
		let l:sig = (getline(l:mhead) =~ '\<\%(function\|task\)\>') ? l:mhead
			\ : (getline(l:mhead) =~ '^\s*(' ? s:PrototypeSigHead(l:mhead) : 0)
		if l:sig > 0 && getline(l:sig) =~ '\<\%(function\|task\)\>'
			let l:is_proto = (getline(l:sig) =~ '\<\%(extern\|pure\)\>' || s:ConvertToCodes(getline(l:sig)) !~# 'f')
			if l:is_proto
				" prototypes: next line returns to declaration level; group stop dedents further
				return indent(l:sig) - (this_codes =~# 'h' ? &shiftwidth : 0)
			else
				" definitions: next line is function body (+ &shiftwidth), or endfunction (same level)
				return indent(l:sig) + (this_codes =~# 'h' ? 0 : &shiftwidth)
			endif
		endif
	endif

	" Tail of a multi-line statement (macro or method call), e.g. the closing
	" "UVM_LOW)" of a `uvm_info, or "cfg.n_bytes, ...), UVM_LOW);" of a
	" uvm_report_error whose args span lines. The open line's '(' has no
	" matching ')' here, so the tail would dedent spuriously and cascade.
	" Keep the tail flat with the statement head.
	let l:mhead = s:StatementTailHead(a:line_num)
	if l:mhead <= 0
		let l:mhead = s:SigTailHead(a:line_num)
	endif
	if l:mhead > 0
		return indent(l:mhead)
	endif

	let indnt = indent( prev1_line_num )
	if l:chead1 > 0
		" the control head, not the (possibly deeper) condition tail,
		" is the indent base for the body
		let indnt = indent(l:chead1)
	endif

	" a prev2 buried in a region that closed before prev1 must not feed
	" the "prev2 control + prev1 statement" dedent rule (s:IsStalePrev2)
	let prev2_gci_codes = prev2_codes
	if prev2_line_num > 0 && prev2_codes =~ s:LINE_INDENT && s:IsStalePrev2(prev2_line_num, prev1_line_num)
		let prev2_gci_codes = ''
	endif

	let indnt = s:GetCodeIndent ( indnt, prev2_gci_codes, prev1_codes, this_codes)

	if this_codes =~ s:BLOCK_COMMENT_STOP_ANY || b:block_comment_change != b:changedtick || b:block_comment_line != prev1_for_comment_line
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
