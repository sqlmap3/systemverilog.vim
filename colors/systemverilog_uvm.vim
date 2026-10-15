" systemverilog_uvm.vim - color scheme tuned to sqlmap3/systemverilog.vim
"
" The systemverilog.vim syntax file defines ~150 custom groups (svType,
" svKeyword, uvmBaseClass, uvmGlobalFn, uvmEnum, uvmPort, svAssertLabel,
" svSVAOp, ...) but links them all to the generic Keyword/Type/Function/
" StorageClass/... groups, so every colorscheme renders them, yet loses the
" distinctions. This scheme assigns each SV/UVM semantic category its own
" color, in a dark and a light variant selected by &background.
"
" Install:  colorscheme systemverilog_uvm
" Tune:     edit the s:P palette below (each entry is [guifg, ctermfg]).
"
" Maintainer: sqlmap3 <https://github.com/sqlmap3>

hi clear
if exists("syntax_on")
  syntax reset
endif
let g:colors_name = "systemverilog_uvm"

" ---------------------------------------------------------------------------
" Palette. Keys are semantic roles; values are [guifg, ctermfg].
" ---------------------------------------------------------------------------
if &background ==# 'dark'
  let s:P = {
        \ 'bg':        ['#1e1e24', 234], 'fg': ['#dcdfe4', 252],
        \ 'comment':   ['#6a9955', 65 ], 'string': ['#ce9178', 173],
        \ 'number':    ['#b5cea8', 151], 'keyword': ['#c586c0', 175],
        \ 'type':      ['#4ec9b0', 79 ], 'storage': ['#569cd6', 75 ],
        \ 'struct':    ['#9cdcfe', 117], 'func':    ['#dcdcaa', 187],
        \ 'const':     ['#d7ba7d', 180], 'macro':   ['#ff7b72', 203],
        \ 'label':     ['#e5c07b', 180], 'svaop':   ['#f44747', 203],
        \ 'thissuper': ['#e5c07b', 180], 'special': ['#d7ba7d', 180],
        \ 'uvmtype':   ['#4fc1ff', 81 ], 'uvmfn':   ['#dcdcaa', 187],
        \ 'uvmenum':   ['#98c379', 114], 'uvmport': ['#e06c75', 168],
        \ 'uvmtlm':    ['#61afef', 75 ], 'uvmreg':  ['#56b6c2', 73 ],
        \ 'uvmconfig': ['#c678dd', 176], 'uvmresource': ['#e5c07b', 180],
        \ 'uvmphase':  ['#d19a66', 173], 'uvmobjection': ['#e06c75', 168],
        \ 'uvmfactory':['#d19a66', 173], 'ident':  ['#dcdfe4', 252],
        \ 'todo':      ['#d16969', 167],
        \ 'direction': ['#56b6c2', 73 ], 'instance': ['#e5c07b', 180],
        \ 'namedport': ['#7ee787', 120], 'structfield': ['#9cdcfe', 117],
        \ 'paramname': ['#d2a8ff', 183], 'bins':   ['#a8ff60', 155],
        \ 'formatspec':['#ffcb6b', 221], 'escape': ['#f78c6c', 209],
        \ 'doccomment':['#7ca668', 107], 'doctag': ['#56b6c2', 73 ],
        \ 'scope':     ['#c678dd', 176], 'property': ['#e5c07b', 180],
        \ }
else
  let s:P = {
        \ 'bg':        ['#fafafa', 255], 'fg': ['#383a42', 237],
        \ 'comment':   ['#a0a1a7', 245], 'string': ['#22863a', 28 ],
        \ 'number':    ['#986801', 136], 'keyword': ['#a626a4', 127],
        \ 'type':      ['#008080', 30 ], 'storage': ['#0000c0', 20 ],
        \ 'struct':    ['#8b4600', 130], 'func':    ['#c00087', 126],
        \ 'const':     ['#986801', 136], 'macro':   ['#d01010', 160],
        \ 'label':     ['#b76b01', 136], 'svaop':   ['#d01010', 160],
        \ 'thissuper': ['#c18401', 136], 'special': ['#986801', 136],
        \ 'uvmtype':   ['#005cc5', 26 ], 'uvmfn':   ['#e36209', 166],
        \ 'uvmenum':   ['#22863a', 28 ], 'uvmport': ['#6f42c1', 98 ],
        \ 'uvmtlm':    ['#0366d6', 26 ], 'uvmreg':  ['#0086a8', 31 ],
        \ 'uvmconfig': ['#b82f9e', 163], 'uvmresource': ['#7a4b00', 94 ],
        \ 'uvmphase':  ['#a75500', 130], 'uvmobjection': ['#ca1243', 161],
        \ 'uvmfactory':['#5b4a9e', 61 ], 'ident':  ['#383a42', 237],
        \ 'todo':      ['#d01010', 160],
        \ 'direction': ['#0086a8', 31 ], 'instance': ['#953800', 130],
        \ 'namedport': ['#1a7f37', 28 ], 'structfield': ['#0969da', 26 ],
        \ 'paramname': ['#8250df', 97 ], 'bins':   ['#116329', 28 ],
        \ 'formatspec':['#b76b01', 136], 'escape': ['#d01010', 160],
        \ 'doccomment':['#5c6370', 241], 'doctag': ['#0086a8', 31 ],
        \ 'scope':     ['#6f42c1', 98 ], 'property': ['#953800', 130],
        \ }
endif

function! s:h(group, key, ...) abort
  let l:c = s:P[a:key]
  let l:gui = a:0 ? a:1 : ''
  execute 'hi ' . a:group . ' guifg=' . l:c[0] . ' ctermfg=' . l:c[1] . ' guibg=NONE ' . l:gui
endfunction

" ---------------------------------------------------------------------------
" Base / standard groups (a minimal, usable base)
" ---------------------------------------------------------------------------
execute 'hi Normal guifg=' . s:P.fg[0] . ' ctermfg=' . s:P.fg[1] . ' guibg=' . s:P.bg[0] . ' ctermbg=' . s:P.bg[1]
hi NonText    guifg=NONE guibg=NONE
hi SpecialKey guifg=NONE guibg=NONE
hi EndOfBuffer guifg=#3c3836 guibg=NONE
hi LineNr     guifg=#6e6e6e ctermfg=242 guibg=NONE
hi CursorLine guibg=#2a2a2a ctermbg=236 guifg=NONE
hi CursorColumn guibg=#2a2a2a ctermbg=236 guifg=NONE
hi StatusLine  guifg=#d4d4d4 ctermfg=252 guibg=#3c3c3c ctermbg=238
hi StatusLineNC guifg=#6e6e6e ctermfg=242 guibg=#2a2a2a ctermbg=236
hi VertSplit   guifg=#3c3c3c ctermfg=238 guibg=NONE
hi Search      guifg=NONE guibg=#613214 ctermbg=52
hi IncSearch   guifg=NONE guibg=#7f5217 ctermbg=58
hi Visual      guibg=#264f78 ctermbg=24
hi Folded      guifg=#808080 ctermfg=244 guibg=#252526 ctermbg=235
hi FoldColumn  guifg=#808080 ctermfg=244 guibg=NONE
hi Title       guifg=#d4d4d4 ctermfg=252 gui=bold
hi ErrorMsg    guifg=#f44747 ctermfg=203 guibg=NONE
hi WarningMsg  guifg=#e5c07b ctermfg=180 guibg=NONE
hi Todo        guifg=#d16969 ctermfg=167 gui=bold

" ---------------------------------------------------------------------------
" systemverilog.vim generic groups
" ---------------------------------------------------------------------------
call s:h('Comment',      'comment', 'gui=italic')
call s:h('svLineComment','comment', 'gui=italic')
call s:h('svBlockComment','comment', 'gui=italic')
call s:h('svDocLineComment','doccomment', 'gui=italic')
call s:h('svDocBlockComment','doccomment', 'gui=italic')
call s:h('svDocTag',     'doctag', 'gui=bold,italic')
call s:h('svString',     'string')
call s:h('svFormatSpecifier','formatspec', 'gui=bold')
call s:h('svStringEscape','escape')
call s:h('svIncludeString','string')
call s:h('svIncludeAngle','string')
call s:h('svInteger',    'number')
call s:h('svReal',       'number')
call s:h('svHashNumber', 'number')
call s:h('svKeyword',    'keyword')
call s:h('svConditional','keyword')
call s:h('svRepeat',     'storage')
call s:h('svOperator',   'fg')
call s:h('svDelimiter',  'fg')
call s:h('svType',       'type')
call s:h('svUserType',   'type')
call s:h('svScopePrefix','scope')
call s:h('svVirtualIfaceType','type')
call s:h('svClassName',  'type')
call s:h('svTypedefName','type')
call s:h('svCovergroupName','type')
call s:h('svStorageClass','storage')
call s:h('svDirection',  'direction', 'gui=italic')
call s:h('svStructure',  'struct')
call s:h('svTypedef',    'keyword')
call s:h('svFunctionName','func')
call s:h('svTaskName',   'func')
call s:h('svSystemCall', 'func')
call s:h('svObjectFunctions','func')
call s:h('svMethodCall',   'func')
call s:h('svMemberAccess', 'structfield')
call s:h('svCtorCall',   'func')
call s:h('svThisSuper',  'thissuper', 'gui=italic')
call s:h('svEnumerator', 'const')
call s:h('svUpperIdent', 'const')
call s:h('svUpperDot',   'const')
call s:h('svMacroRef',   'macro')
call s:h('svDefineName', 'macro')
call s:h('svIfdefName',  'macro')
call s:h('svIfndefName', 'macro')
call s:h('svMacroArgs',  'special')
call s:h('svAssertLabel','label', 'gui=bold')
call s:h('svCoverLabel', 'label')
call s:h('svCoverOption','label')
call s:h('svCoverTypeOption','label')
call s:h('svSVAOp',      'svaop', 'gui=bold')
call s:h('svPreProc',    'keyword')
call s:h('svPreCondit',  'keyword')
call s:h('svPreConditElsif','keyword')
call s:h('svInclude',    'keyword')
call s:h('svDefine',     'keyword')
call s:h('svUndef',      'keyword')
call s:h('svIfdefTok',   'keyword')
call s:h('svIfndefTok',  'keyword')
call s:h('svIncludeExt', 'special')
call s:h('svTimeUnitHash','special')
call s:h('svTimeUnitPlain','special')
call s:h('svModuleName', 'type', 'gui=bold')
call s:h('svInterfaceName','type', 'gui=bold')
call s:h('svPackageName','type', 'gui=bold')
call s:h('svParamName',  'paramname')
call s:h('svPortName',   'namedport')
call s:h('svInstanceName','instance', 'gui=bold')
call s:h('svStructField','structfield')
call s:h('svArgName',    'structfield')
call s:h('svNamedPort',  'namedport', 'gui=bold')
call s:h('svBinsName',   'bins')
call s:h('svBinsofExpr', 'bins')
call s:h('svIntersectExpr','bins')
call s:h('svCoverWithPred','bins')
call s:h('svCoverIffPred','bins')
call s:h('svModuleKw',   'keyword', 'gui=bold')
call s:h('svInterfaceKw','keyword', 'gui=bold')
call s:h('svPackageKw',  'keyword', 'gui=bold')
call s:h('svClassKw',    'keyword', 'gui=bold')
call s:h('svFunctionKw', 'keyword', 'gui=bold')
call s:h('svTaskKw',     'keyword', 'gui=bold')
call s:h('Keyword',      'keyword', 'gui=bold')
call s:h('Statement',    'keyword')
call s:h('StorageClass', 'storage')
call s:h('Type',         'type')
call s:h('Function',     'func')
call s:h('Constant',     'const')
call s:h('PreProc',      'keyword')
call s:h('Special',      'special')

" ---------------------------------------------------------------------------
" UVM groups - high distinction: each semantic category gets its own color
" ---------------------------------------------------------------------------
" class hierarchy / scalar types / phases
call s:h('uvmBaseClass', 'uvmtype')
call s:h('uvmScalarType', 'uvmtype')
call s:h('uvmPhase',     'uvmphase')
call s:h('uvmPhaseClass2','uvmphase')
call s:h('uvmUserClass', 'uvmtype')
" global functions / run test
call s:h('uvmGlobalFn',  'uvmfn')
call s:h('uvmRunTest',   'uvmfn', 'gui=bold')
call s:h('uvmTestDone',  'uvmfn')
call s:h('uvmTopGlobal', 'uvmfn')
call s:h('uvmGlobal',    'uvmfn')
call s:h('uvmDefaultPrinter','uvmfn')
call s:h('uvmDefaultComparer','uvmfn')
call s:h('uvmDefaultPacker','uvmfn')
call s:h('uvmMethodInfo', 'uvmfn')
" enums / constants
call s:h('uvmEnum',      'uvmenum')
" ports / sockets / TLM / RAL
call s:h('uvmPort',      'uvmport')
call s:h('uvmSocket',    'uvmtlm')
call s:h('uvmTLM',       'uvmtlm')
call s:h('uvmReg',       'uvmreg')
" config / resource DB
call s:h('uvmConfig',    'uvmconfig')
call s:h('uvmResource',  'uvmresource')
" objection / factory / API methods
call s:h('uvmObjectionClass', 'uvmobjection')
call s:h('uvmMethodObjection','uvmobjection')
call s:h('uvmMethodFactory','uvmfactory')
call s:h('uvmApiMethod', 'func')
call s:h('uvmConfigApi', 'label')
call s:h('uvmMethodConfig','label')
call s:h('uvmTypeIdCreate','func')
call s:h('uvmSeq',       'ident')
call s:h('uvmRegSeqName','ident')
call s:h('uvmEventMethod','func')
" operator-style UVM methods
call s:h('uvmMethodTrans','fg')
call s:h('uvmMethodSeqCtrl','storage')
call s:h('uvmRegApi',    'fg')
call s:h('uvmHDLApi',    'fg')
" macros
call s:h('uvmMacros',    'macro')
call s:h('uvmCallbackMacros','macro')
" the full specific-class list: same "UVM class" tone as uvmBaseClass
for s:g in ['uvmDomainClass','uvmBarrierClass','uvmBarrierPoolClass',
      \ 'uvmEventClass','uvmEventPoolClass','uvmAnalysisFifoClass',
      \ 'uvmGenericPayloadClass','uvmResourceClass','uvmRegAdapterClass',
      \ 'uvmRegSequenceClass','uvmRegBusOpClass','uvmCoreClass',
      \ 'uvmPrinterClass','uvmAnalysisClass','uvmCallbacksClass',
      \ 'uvmCmdlineClass','uvmRecorderClass','uvmComparerClass',
      \ 'uvmPackerClass','uvmMemClass','uvmMemMamClass','uvmMemMamCfgClass',
      \ 'uvmRegFrontdoorClass','uvmRegBackdoorClass','uvmRegCbsClass',
      \ 'uvmRegItemClass','uvmReportHandlerClass','uvmReportCatcherClass',
      \ 'uvmTrDbClass','uvmTrStreamClass','uvmTrRecClass',
      \ 'uvmTlmFifoClass','uvmSeqLibClass']
  call s:h(s:g, 'uvmtype')
endfor
unlet s:g

delfunction s:h
