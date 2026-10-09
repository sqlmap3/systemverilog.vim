" Vim syntax file
" Language:	systemverilog
" Maintainer:	sqlmap3 < https://github.com/sqlmap3 >
" Version:	0.1
" First Change:	Sat Dec 06 11:15:30 CST 2025
" Last Change:	Wed Feb 11 21:08:29 CST 2026
if exists("b:current_syntax")
	finish
endif

let b:current_syntax = "systemverilog"

syntax match svTodo "\c\<\(todo\|fixme\|fix\|xxx\|bug\|hack\|note\|warn\|warning\|optimize\|review\|tbd\)\>" contained
syntax match svLineComment "//.*" contains=svTodo
syntax region svBlockComment start="/\*" end="\*/" contains=svTodo
syntax region svString start=+"+ skip=+\\"+ end=+"+ contains=NONE
syntax keyword svType real realtime event reg wire integer logic bit time byte chandle genvar signed unsigned shortint shortreal string void int specparam
syntax keyword svDirection input output inout ref
syntax keyword svStorageClass virtual var protected rand const static automatic extern forkjoin export import
syntax match svMacroRef "`\h\%(\w\|\$\)*"
syntax match svDefine "^\s*`define\>" nextgroup=svDefineName skipwhite
syntax match svUndef  "^\s*`undef\>"  nextgroup=svDefineName skipwhite
syntax match svPreProc "^\s*`\(__FILE__\|__LINE__\|begin_keywords\|celldefine\|default_nettype\|end_keywords\|endcelldefine\|line\|nounconnected_drive\|pragma\|resetall\|timescale\|unconnected_drive\|undefineall\)\>"
syntax match svInclude "^\s*`include\>" nextgroup=svIncludeString,svIncludeAngle skipwhite
syntax region svIncludeString start=+"+ skip=+\\"+ end=+"+ contained contains=svIncludeExt
syntax region svIncludeAngle  start=+<+ end=+>+ contained contains=svIncludeExt
syntax match svIncludeExt "\.\c\(svh\|sv\|vh\|v\)\>" contained
syntax match svPreConditElsif "^\s*`elsif\>" nextgroup=svIfdefName skipwhite
syntax match svPreCondit "^\s*`\(else\|endif\)\>"

syntax keyword svConditional if else iff case casez casex endcase
syntax keyword svRepeat for foreach do while forever repeat
syntax keyword svKeyword fork join join_any join_none begin end endmodule endfunction endtask always always_ff always_latch always_comb initial generate endgenerate config endconfig endclass clocking endclocking endinterface endpackage modport posedge negedge edge defparam assign deassign alias return disable wait continue and buf bufif0 bufif1 nand nor not or xnor xor tri tri0 tri1 triand trior trireg pull0 pull1 pullup pulldown cmos default endprimitive endspecify endtable force highz0 highz1 ifnone large macromodule medium nmos notif0 notif1 pmos primitive rcmos release rnmos rpmos rtran rtranif0 rtranif1 scalared small specify strong0 strong1 supply0 supply1 table tran tranif0 tranif1 vectored wand weak0 weak1 wor cell design incdir liblist library noshowcancelled pulsestyle_ondetect pulsestyle_onevent showcancelled use instance uwire assert assume before bind bins binsof break constraint context cover coverpoint cross dist endgroup endprogram endproperty endsequence expect extends final first_match ignore_bins illegal_bins inside intersect local longint matches new null packed unpacked priority program property pure randc randcase randsequence sequence solve tagged throughout timeprecision timeunit type unique wait_order wildcard with within accept_on checker endchecker eventually global implies let nexttime reject_on restrict s_always s_eventually s_nexttime s_until s_until_with strong sync_accept_on sync_reject_on unique0 until until_with untyped weak implements interconnect nettype soft
syntax match svInteger "\<\(\.\)\@<![0-9_]\+\(\s*['.]\)\@!\>"
syntax match svInteger "\(\<[0-9_]\+\s*\)\?'\(s\|S\)\?\(d\|D\)\s*[0-9_ZzXx?]\+"
syntax match svInteger "\(\<[0-9_]\+\s*\)\?'\(s\|S\)\?\(h\|H\)\s*[0-9a-fA-F_ZzXx?]\+"
syntax match svInteger "\(\<[0-9_]\+\s*\)\?'\(s\|S\)\?\(o\|O\)\s*[0-7_ZzXx?]\+"
syntax match svInteger "\(\<[0-9_]\+\s*\)\?'\(s\|S\)\?\(b\|B\)\s*[01_ZzXx?]\+"
syntax match svInteger "\<'\(d\|D\|h\|H\|o\|O\|b\|B\)\>"
syntax match svInteger "'[01xXzZ?]\>"
syntax match svReal "\<[0-9_]\+\.[0-9_]\+\(\(e\|E\)[+-]\?[0-9_]\+\)\?\>"
syntax match svReal "\<[0-9_]\+\(e\|E\)[+-]\?[0-9_]\+\>"
" struct/union/enum are NOT keywords on purpose: a keyword would win the
" start position of the svStructBody / svEnumBody regions below and stop
" them from ever opening, leaving struct fields / enumerators unhighlighted.
" (They are always followed by a {...} body, so the transparent regions own
" them.)
syntax match svStructure "\<\%(struct\|union\|enum\)\>"
syntax keyword svTypedef typedef parameter localparam
syntax region svEnumBody start="\<enum\>\_.\{-}{" end="}" keepend transparent contains=ALLBUT,svDefineName,svMacroArgs,svIfdefName,svIfndefName,svModuleName,svInterfaceName,svPackageName,svClassName,svCovergroupName
syntax match svEnumerator "\<\h\w*\>\ze\_s*[=,}]" contained containedin=svEnumBody
syntax region svPortList start="^\s*\%(module\|interface\)\>\_.\{-}\%(\_s*#\_s*(\_.\{-})\)\?\_s*(" end=");" keepend transparent contains=ALLBUT,svDefineName,svMacroArgs,svIfdefName,svIfndefName,svModuleName,svInterfaceName,svPackageName,svClassName,svCovergroupName
syntax match svPortName "\<\h\w*\>\ze\%(\_s*\(\[[^]]*\]\_s*\)\*\)\_s*\%(,\|)\|=\)" contained containedin=svPortList
syntax region svInstStmt start="^\s*\%(\%(module\|interface\|function\|task\|class\|package\|typedef\|property\|sequence\|covergroup\)\>\)\@!\h\w*\%(\_s*#\_s*(\_.\{-})\)\?\_s\+\h\w*\_s*\%(\[[^]]*]\_s*\)\?(" end=";" keepend transparent contains=ALLBUT,svDefineName,svMacroArgs,svIfdefName,svIfndefName,svModuleName,svInterfaceName,svPackageName,svClassName,svCovergroupName
syntax match svInstanceName "^\s*\%(\%(module\|interface\|function\|task\|class\|package\|typedef\|property\|sequence\|covergroup\)\>\)\@!\h\w*\%(\_s*#\_s*(\_.\{-})\)\?\_s\+\zs\h\w*\ze\_s*\%(\[[^]]*]\_s*\)\?(" contained containedin=svInstStmt
syntax match svInstanceName ",\_s*\zs\h\w*\ze\_s*\%(\[[^]]*]\_s*\)\?(" contained containedin=svInstStmt
" names after module/interface/package/class. nextgroup-based (not \zs): a
" \zs in a :syntax match anchors the match there, so the leading keyword
" never matches. The *_Kw keywords keep the Keyword color.
syntax keyword svModuleKw module nextgroup=svModuleName skipwhite skipempty
syntax keyword svInterfaceKw interface nextgroup=svInterfaceName skipwhite skipempty
syntax keyword svPackageKw package nextgroup=svPackageName skipwhite skipempty
syntax keyword svClassKw class nextgroup=svClassName skipwhite skipempty
syntax match svModuleName "\h\w*" contained
syntax match svInterfaceName "\h\w*" contained
syntax match svPackageName "\h\w*" contained
syntax match svClassName "\h\w*" contained
highlight! default link svModuleKw Keyword
highlight! default link svInterfaceKw Keyword
highlight! default link svPackageKw Keyword
highlight! default link svClassKw Keyword
" virtual interface declarations: highlight the type in "virtual my_if vif;"
syntax match svVirtualIfaceType "\<virtual\_s\+\zs\h\w*\ze\_s\+\h\w*\%(\_s*\[[^][]*\]\)*\_s*;"
" task/function names. The keyword is a MATCH (not a :syntax keyword) so the
" transparent signature region below can start at it - a keyword would win
" the start position and the region would never open. The name is the word
" immediately before '(' inside the region body.
syntax match svTaskKw "\<task\>"
syntax match svFunctionKw "\<function\>"
syntax region svTaskSig start="\<task\>" end="(" keepend transparent contains=ALLBUT,svDefineName,svMacroArgs,svIfdefName,svIfndefName,svModuleName,svInterfaceName,svPackageName,svClassName,svCovergroupName,svFunctionName
syntax region svFunctionSig start="\<function\>" end="(" keepend transparent contains=ALLBUT,svDefineName,svMacroArgs,svIfdefName,svIfndefName,svModuleName,svInterfaceName,svPackageName,svClassName,svCovergroupName,svTaskName
syntax match svTaskName "\h\w*\ze\_s*(" contained containedin=svTaskSig
syntax match svFunctionName "\h\w*\ze\_s*(" contained containedin=svFunctionSig
highlight! default link svTaskKw Keyword
highlight! default link svFunctionKw Keyword
syntax match svParamName "^\s*\%(parameter\|localparam\)\>.\{-}\zs\h\w*\ze\_s*="
syntax match svTypedefName "\<typedef\>\_.\{-}\zs\h\w*\ze\_s*;"
syntax region svStructBody start="\<\(struct\|union\)\>\%(\_s\+packed\)\?\_s*{" end="}" keepend transparent contains=ALLBUT,svDefineName,svMacroArgs,svIfdefName,svIfndefName,svModuleName,svInterfaceName,svPackageName,svClassName,svCovergroupName
" split into two fixed-lookahead patterns: a \?/\* after \ze inside a
" :syntax match does not make the atom optional, so the field-before-[...]
" and field-before-;/=/ , cases must be listed separately
syntax match svStructField "\<\h\w*\>\ze\_s*[;=,]" contained containedin=svStructBody
syntax match svStructField "\<\h\w*\>\ze\_s*\[[^]]*\]\_s*[;=,]" contained containedin=svStructBody
syntax match svNamedPort "\%(\s\|[(,]\)\.\zs\h\w*\ze\_s*(" containedin=ALL,svInstStmt
syntax match svAssertLabel "\<\zs\h\w*\ze\s*:\s*\%(assert\|assume\|cover\)\>" containedin=ALL
" all $-system calls ($display, $rose, $clog2, $cast, $fscanf, ...) share one
" catch-all group instead of a huge redundant keyword list
syntax match svSystemCall "\$\h\w*\>"
syntax match svObjectFunctions "\.\(randomize\|srandomize\|num\|size\|delete\|exists\|first\|last\|next\|prev\|insert\|pop_front\|pop_back\|push_front\|push_back\|find\|find_index\|find_first\|find_first_index\|find_last\|find_last_index\|min\|max\|reverse\|sort\|rsort\|shuffle\|sum\|product\|and\|or\|xor\)\>\_s*("he=e-1
syntax match svOperator "\(\~\|&\|||\|\^\|=\|!\|?\|:\|@\|<\|>\|%\|+\|-\|\*\|\/[\/\*]\@!\)"
syntax match svDelimiter "\({\|}\|(\|)\)"

syntax match svSVAOp "\(|->\||=>\|##\d\+\|##\|\[\*\(\d\+\(:\d\+\)\?\)\?\]\)"

" Covergroup / coverpoint / bins names
syntax keyword svCovergroupKw covergroup nextgroup=svCovergroupName skipwhite skipempty
syntax match svCovergroupName "\h\w*" contained
highlight! default link svCovergroupKw Keyword
" Macro guard names
syntax match svIfndefTok "^\s*`ifndef\>" nextgroup=svIfndefName skipwhite
syntax match svIfdefTok  "^\s*`ifdef\>"  nextgroup=svIfdefName  skipwhite
syntax match svIfndefName "\h\%(\w\|\$\)*" contained
syntax match svIfdefName  "\h\%(\w\|\$\)*" contained
syntax match svDefineName "\h\%(\w\|\$\)*" contained nextgroup=svMacroArgs skipwhite
syntax region svMacroArgs start="(" end=")" contained contains=NONE
syntax match svUpperDot    "\<[A-Z0-9_]\+\(\.[A-Z0-9_]\+\)\+\>" containedin=ALL
syntax match svUpperIdent  "\<\(UVM_\)\@![A-Z][A-Z0-9_]*\>"
syntax match svHashNumber  "#[0-9_]\+" containedin=ALL
syntax match svTimeUnitHash     "#[0-9_]\+\s*\zs\c\(fs\|ps\|ns\|us\|ms\|s\|step\)\>" containedin=ALL
syntax match svTimeUnitHash     "#[0-9_]\+\.[0-9_]\+\s*\zs\c\(fs\|ps\|ns\|us\|ms\|s\|step\)\>" containedin=ALL
syntax match svTimeUnitPlain    "\<[0-9_]\+\s*\zs\c\(fs\|ps\|ns\|us\|ms\|s\|step\)\>" containedin=ALL
syntax match svTimeUnitPlain    "\<[0-9_]\+\.[0-9_]\+\s*\zs\c\(fs\|ps\|ns\|us\|ms\|s\|step\)\>" containedin=ALL
syntax match svCoverLabel "\<\zs\h\w*\ze\s*:\s*\(coverpoint\|cross\)\>"
syntax match svBinsName "\<\(wildcard\s\+\)\?bins\>\s\+\zs\h\w*"
syntax match svBinsName "\<\(illegal_bins\|ignore_bins\)\>\s\+\zs\h\w*"

" binsof/intersect expressions and with/iff predicates
syntax region svBinsofExpr start="\<binsof\>\s*(" end=")" keepend
syntax region svIntersectExpr start="\<intersect\>\s*{" end="}" keepend
syntax region svCoverWithPred start="\<with\>\s*(" end=")" keepend
syntax region svCoverIffPred start="\<iff\>\s*(" end=")" keepend



" generic catch-alls FIRST: later-defined matches win, so these must come
" before the specific class groups below or they would shadow them (e.g.
" uvmReg over uvmRegAdapterClass, uvmTLM over uvmGenericPayloadClass)
syntax match uvmPort "\<uvm_\(non\)\?blocking_\w\+_\(port\|export\|imp\)\>"
syntax match uvmSocket "\<uvm_\(tlm_\)\?b\?_\(initiator\|target\)_socket\(_base\)\?\>"
syntax match uvmTLM "\<uvm_tlm_\w\+\>"
syntax match uvmReg "\<uvm_reg_\w\+\>"
syntax match uvmEnum "\<UVM_[A-Z0-9_]\+\>"
highlight! default link uvmPort StorageClass
highlight! default link uvmSocket Structure
highlight! default link uvmTLM Structure
highlight! default link uvmReg Structure
highlight! default link uvmEnum Constant

" domain/event/barrier/analysis fifo and payload
syntax match uvmDomainClass "\<uvm_domain\>"

syntax match uvmBarrierClass "\<uvm_barrier\>"
syntax match uvmBarrierPoolClass "\<uvm_barrier_pool\>"

syntax match uvmEventClass "\<uvm_event\>"
syntax match uvmEventPoolClass "\<uvm_event_pool\>"

syntax match uvmAnalysisFifoClass "\<uvm_tlm_analysis_fifo\>"

syntax match uvmGenericPayloadClass "\<uvm_tlm_generic_payload\>"

syntax match uvmResourceClass "\<uvm_resource\>"

syntax match uvmRegAdapterClass "\<uvm_reg_adapter\>"
syntax match uvmRegSequenceClass "\<uvm_reg_sequence\>"
syntax match uvmRegBusOpClass "\<uvm_reg_bus_op\>"

" uvm_objection class and APIs
syntax match uvmObjectionClass "\<uvm_objection\>"

" core classes and printers
syntax keyword uvmCoreClass uvm_object uvm_component uvm_root uvm_test uvm_env uvm_agent uvm_driver uvm_monitor uvm_scoreboard uvm_sequencer uvm_sequence uvm_sequence_item uvm_report_object
syntax match uvmPrinterClass "\<uvm_\(printer\|table_printer\|tree_printer\|line_printer\)\>"
syntax match uvmAnalysisClass "\<uvm_analysis_\(port\|imp\|export\)\>"

" callbacks
syntax match uvmCallbacksClass "\<uvm_\(callback\|callbacks\)\>"
syntax match uvmCallbackMacros "\<uvm_\(register_cb\|do_callbacks\|do_callbacks_exit\)\>"

" globals
syntax match uvmTopGlobal "\<uvm_top\>"

" uvm_phase class and APIs
syntax match uvmPhaseClass "\<uvm_phase\>"

" cmdline processor
syntax match uvmCmdlineClass "\<uvm_cmdline_processor\>"

" recorder/comparer/packer
syntax match uvmRecorderClass "\<uvm_recorder\>"
syntax match uvmComparerClass "\<uvm_comparer\>"
syntax match uvmPackerClass   "\<uvm_packer\>"

" add do_record/do_unpack to method set
syntax keyword uvmMethodTrans do_record pack unpack unpack_bytes pack_bytes

" RAL: memory and MAM
syntax match uvmMemClass "\<uvm_mem\>"

syntax match uvmMemMamClass    "\<uvm_mem_mam\>"
syntax match uvmMemMamCfgClass "\<uvm_mem_mam_cfg\>"

" RAL: frontdoor/backdoor
syntax match uvmRegFrontdoorClass "\<uvm_reg_frontdoor\>"
syntax match uvmRegBackdoorClass  "\<uvm_reg_backdoor\>"

" RAL: callbacks and items
syntax match uvmRegCbsClass "\<uvm_reg_cbs\>"
syntax match uvmRegItemClass "\<uvm_reg_item\>"

" Report handler/catcher
syntax match uvmReportHandlerClass "\<uvm_report_handler\>"
syntax match uvmReportCatcherClass "\<uvm_report_catcher\>"

" Transaction recording
syntax match uvmTrDbClass     "\<uvm_tr_database\>"
syntax match uvmTrStreamClass "\<uvm_tr_stream\>"
syntax match uvmTrRecClass    "\<uvm_tr_recorder\>"

" TLM FIFO (generic)
syntax match uvmTlmFifoClass "\<uvm_tlm_fifo\>"

" Sequence library
syntax match uvmSeqLibClass "\<uvm_sequence_library\>"

" Default globals
syntax match uvmDefaultPrinter   "\<uvm_default_printer\>"
syntax match uvmDefaultComparer  "\<uvm_default_comparer\>"
syntax match uvmDefaultPacker    "\<uvm_default_packer\>"

" Covergroup options
syntax match svCoverOption "\<option\>\.\h\w*"
syntax match svCoverTypeOption "\<type_option\>\.\h\w*"

" RAL common sequences names
syntax match uvmRegSeqName "\<uvm_reg_\(bit_bash\|access\|hw_reset\|mem_built_in\|mem_access\)_seq\>"

" Root and run_test
syntax match uvmRunTest "\<run_test\>"

" Global test objection
syntax match uvmTestDone "\<uvm_test_done\>"

syntax match svCtorCall "\<\(super\|this\)\>\s*\.\s*new\>"
syntax match uvmTypeIdCreate "\<type_id\>\s*::\s*create\>"
syntax keyword svRandCallback pre_randomize post_randomize
syntax match uvmConfig "\<uvm_config_db\>"
syntax match uvmResource "\<uvm_resource_db\>"
highlight! default link uvmConfig Structure
highlight! default link uvmResource Structure

" ::get / ::set / static method calls. Matched as plain "::name" (NOT with
" a leading class + \zs): \zs in a :syntax match anchors the match at \zs,
" so the leading class never matches and the rule is dead code. The generic
" group is defined first so the config/resource API group (below) wins for
" the overlapping set/get/exists/... names.
syntax match uvmApiMethod   "::\_s*\h\w*"
syntax match uvmConfigApi   "::\_s*\%(set\|get\|exists\|find\|get_by_name\|get_by_type\|set_default\)\>"
highlight! default link uvmApiMethod Function
highlight! default link uvmConfigApi Label


syntax match uvmMacros "\<uvm_field_\w\+\>"
syntax match uvmMacros "\<uvm_object_utils\(_begin\|_end\|_param\w*\)\>"
syntax match uvmMacros "\<uvm_component_utils\(_begin\|_end\|_param\w*\)\>"
syntax match uvmMacros "\<uvm_do\(_\w\+\)\?\>"
syntax match uvmMacros "\<uvm_\(pack\|unpack\|record\|print\)_\w\+\>"
syntax match uvmMacros "\<uvm_\(error\|warning\|info\|fatal\)\(_context\)\?\>"
highlight! default link uvmMacros Macro

syntax keyword uvmMethodObjection raise_objection drop_objection global_stop_request
" as a match (not keyword) with a ::-lookbehind: keyword priority would
" otherwise swallow the method after a class reference, e.g. the `get` of
" uvm_config_db::get() or uvm_factory::get() (see uvmConfigApi/uvmApiMethod)
syntax match uvmMethodTrans "\%(::\s*\)\@<!\<\(get\|put\|peek\|try_get\|try_put\|try_peek\|try_next_item\|b_transport\|nb_transport_fw\|nb_transport_bw\)\>"
syntax keyword uvmMethodSeqCtrl start_item finish_item item_done
syntax keyword uvmMethodSeqCtrl wait_for_grant send_request wait_for_item_done
syntax keyword uvmMethodSeqCtrl grab ungrab lock unlock
syntax keyword uvmMethodFactory create set_type_override_by_type set_inst_override_by_type
syntax keyword uvmMethodConfig set_config set_report_verbosity_level set_report_severity_action set_report_id_action set_report_default_file
highlight! default link uvmMethodObjection Keyword
highlight! default link uvmMethodTrans Operator
highlight! default link uvmMethodSeqCtrl Repeat
highlight! default link uvmMethodFactory Structure
highlight! default link uvmMethodConfig Label

" UVM 1.2 library classes not covered by the groups above (derived from
" the uvm-1.2 source tree): base classes, factory/registry, pools, queues,
" visitors, report/message plumbing, links, DAPs, RAL memory regions and
" virtual registers, TLM1/comps helpers
syntax keyword uvmBaseClass uvm_void uvm_transaction uvm_sequence_base uvm_sequence_process_wrapper uvm_sequence_request uvm_sequence_library_cfg uvm_sequencer_base uvm_sequencer_param_base uvm_push_sequencer uvm_random_sequence uvm_exhaustive_sequence uvm_simple_sequence uvm_pool uvm_queue uvm_factory uvm_component_registry uvm_object_registry uvm_root uvm_report_server uvm_default_report_server uvm_report_message uvm_report_message_element_base uvm_report_message_element_container uvm_event_base uvm_resource_base uvm_resource_pool uvm_resource_types uvm_resource_options uvm_callback_iter uvm_callbacks_base uvm_typed_callbacks uvm_derived_callbacks uvm_typeid uvm_typeid_base uvm_visitor uvm_visitor_adapter uvm_structure_proxy uvm_component_proxy uvm_component_name_check_visitor uvm_coreservice_t uvm_default_coreservice_t uvm_spell_chkr uvm_printer_knobs uvm_text_tr_stream uvm_scope_stack uvm_status_container uvm_seed_map uvm_utils uvm_heartbeat uvm_port_base uvm_port_component_base uvm_push_driver uvm_subscriber uvm_pair uvm_policies uvm_random_stimulus uvm_algorithmic_comparator uvm_in_order_comparator uvm_in_order_built_in_comparator uvm_in_order_class_comparator uvm_mem_region uvm_mem_mam_policy uvm_predict_s uvm_vreg uvm_vreg_field uvm_vreg_cbs uvm_vreg_field_cbs uvm_link_base uvm_cause_effect_link uvm_parent_child_link uvm_related_link uvm_simple_lock_dap uvm_set_before_get_dap uvm_get_to_lock_dap uvm_set_get_dap_base
highlight! default link uvmBaseClass Type

" UVM 1.2 lowercase scalar types / enums (uvm_object_globals.svh etc.)
syntax keyword uvmScalarType uvm_verbosity uvm_action uvm_severity uvm_radix_enum uvm_active_passive_enum uvm_access_e uvm_check_e uvm_coverage_model_e uvm_bitstream_t uvm_objection_event uvm_phase_state uvm_phase_type
highlight! default link uvmScalarType Type

" UVM 1.2 global functions (uvm_globals.svh); the class names keep their
" own groups, the report_* call sites are what gets highlighted here
syntax match uvmGlobalFn "\<uvm_report_\(info\|warning\|error\|fatal\|enabled\|hook\|separator\)\>"
syntax match uvmGlobalFn "\<uvm_wait_for_nba_region\>"
highlight! default link uvmGlobalFn Function

syntax keyword uvmPhase build_phase check_phase configure_phase connect_phase define_domain do_kill end_of_elaboration_phase exec_task extract_phase final_phase main_phase phase_ended phase_ready_to_end phase_started post_configure_phase post_main_phase post_reset_phase post_shutdown_phase pre_configure_phase pre_main_phase pre_reset_phase pre_shutdown_phase report_phase reset_phase run_phase shutdown_phase start_of_simulation_phase
highlight! default link uvmPhase Type

syntax match uvmPhase "\<uvm_\(pre_reset\|reset\|post_reset\|pre_configure\|configure\|post_configure\|pre_main\|main\|post_main\|pre_shutdown\|shutdown\|post_shutdown\)_phase\>"

syntax match uvmPhase "\<uvm_\(build\|connect\|end_of_elaboration\|start_of_simulation\|run\|extract\|check\|report\|final\)_phase\>"

syntax match uvmPhaseGet "\<uvm_\w\+_phase\>\s*::\s*get\>"
highlight! default link uvmPhaseGet Function

syntax keyword uvmSeq uvm_reg_bit_hash_seq uvm_reg_hw_reset_seq uvm_reg_mem_built_in_seq uvm_reg_single_access_seq uvm_reg_single_bit_bash_seq uvm_reg_mem_shared_access_seq uvm_reg_mem_hdl_paths_seq uvm_mem_single_access_seq uvm_mem_access_seq uvm_mem_single_walk_seq uvm_mem_walk_seq uvm_mem_shared_access_seq
highlight! default link uvmSeq Identifier

" UVM version flavor -------------------------------------------------------
" Highlighting cannot auto-detect which UVM library a project uses (the
" class names are ~identical); configure it per project instead:
"   let g:systemverilog_uvm_version = '1.1'   " UVM 1.1 phase callbacks
"   let g:systemverilog_uvm_version = '1.2'   " (default)
" A buffer-local b:systemverilog_uvm_version wins over the global.
" Extra (e.g. VIP) class names: let g:systemverilog_uvm_names = ['my_agent']
let s:uvm_ver = get(b:, 'systemverilog_uvm_version',
	\ get(g:, 'systemverilog_uvm_version', '2'))
if s:uvm_ver =~# '^\s*1\%(\.1\)\?\s*$'
	" UVM 1.1: component phase callbacks without the _phase suffix
	syntax keyword uvmPhase build connect end_of_elaboration
	syntax keyword uvmPhase start_of_simulation run extract check report
	syntax keyword uvmPhase pre_reset reset post_reset
	syntax keyword uvmPhase pre_configure configure post_configure
	syntax keyword uvmPhase pre_main main post_main
	syntax keyword uvmPhase pre_shutdown shutdown post_shutdown
	" UVM 1.1-era test-done objection and stop request
	syntax keyword uvmGlobal uvm_test_done global_stop_request
	highlight! default link uvmGlobal Global
else
	" UVM 1.2 additions (phase schedule classes and domains)
	syntax keyword uvmPhaseClass2 uvm_domain uvm_tlm_time
	syntax keyword uvmPhaseClass2 uvm_topdown_phase uvm_bottomup_phase
	syntax keyword uvmPhaseClass2 uvm_task_phase uvm_runtime_phase
	highlight! default link uvmPhaseClass2 Type
endif
if exists('g:systemverilog_uvm_names')
	for s:name in g:systemverilog_uvm_names
		execute 'syntax keyword uvmUserClass' s:name
	endfor
	unlet! s:name
	highlight! default link uvmUserClass Type
endif

syntax match uvmRegApi "\<uvm_reg_[A-Za-z0-9_]\+\>\s*::\s*\(read\|write\|mirror\|predict\|poke\|peek\|update\)\>"
highlight! default link uvmRegApi Operator

syntax match uvmHDLApi "\<uvm_hdl_\(read\|write\|force\|release\)\>"
highlight! default link uvmHDLApi Operator

syntax keyword uvmEventMethod trigger wait_on wait_off wait_for wait_ptrigger wait_trigger
highlight! default link uvmEventMethod Statement

syntax keyword uvmMethodInfo get_type_name get_full_name get_name get_parent get_children get_child get_children
highlight! default link uvmMethodInfo Global

" Consolidated highlight mappings (SV + SVA + UVM)
highlight! default link svTodo Todo
highlight! default link svLineComment Comment
highlight! default link svBlockComment Comment
highlight! default link svString String
highlight! default link svType Type
highlight! default link svDirection StorageClass
highlight! default link svStorageClass StorageClass
highlight! default link svPreProc PreProc
highlight! default link svPreCondit PreCondit
highlight! default link svPreConditElsif PreCondit
highlight! default link svInclude Include
highlight! default link svIncludeString String
highlight! default link svIncludeAngle String
highlight! default link svIncludeExt Special
highlight! default link svDefine PreCondit      " `define keyword as PreCondit
highlight! default link svUndef PreProc
" macros in conditional guards/defines
highlight! default link svIfndefTok PreCondit   " `ifndef keyword as PreCondit
highlight! default link svIfdefTok  PreCondit   " `ifdef  keyword as PreCondit
highlight! default link svConditional Conditional
highlight! default link svRepeat Repeat
highlight! default link svKeyword Keyword
highlight! default link svInteger Number
highlight! default link svReal Float
highlight! default link svStructure Structure
highlight! default link svModuleName Identifier
highlight! default link svInterfaceName Identifier
highlight! default link svVirtualIfaceType Type
highlight! default link svPackageName Identifier
highlight! default link svClassName Type
highlight! default link svTaskName Function
highlight! default link svFunctionName Function
highlight! default link svParamName Identifier
highlight! default link svTypedefName Type
highlight! default link svPortName Identifier
highlight! default link svInstanceName Identifier
highlight! default link svEnumerator Constant
highlight! default link svStructField Identifier
highlight! default link svTypedef Typedef
highlight! default link svSystemCall Function
highlight! default link svOperator Operator
highlight! default link svNamedPort Identifier
highlight! default link svAssertLabel Label
highlight! default link svDelimiter Delimiter
highlight! default link svObjectFunctions Function
highlight! default link svSVAOp Operator
highlight! default link svCovergroupName Type
highlight! default link svCoverLabel Label
highlight! default link svBinsName Identifier
highlight! default link svBinsofExpr Identifier
highlight! default link svIntersectExpr Identifier
highlight! default link svCoverWithPred Identifier
highlight! default link svCoverIffPred Identifier
highlight! default link svCoverOption Label
highlight! default link svCoverTypeOption Label
highlight! default link svIfndefName Macro      " macro name after `ifndef as Macro
highlight! default link svIfdefName  Macro      " macro name after `ifdef  as Macro
highlight! default link svDefineName Macro      " macro name after `define as Macro
highlight! default link svMacroArgs Special
highlight! default link svUpperDot Constant
highlight! default link svUpperIdent Constant
highlight! default link svHashNumber Number
" Highlight user macro usage
highlight! default link svMacroRef Macro
highlight! default link svTimeUnitHash Special
highlight! default link svTimeUnitPlain Special

highlight! default link uvmDomainClass Type
highlight! default link uvmBarrierClass Type
highlight! default link uvmBarrierPoolClass Type
highlight! default link uvmEventClass Type
highlight! default link uvmEventPoolClass Type
highlight! default link uvmAnalysisFifoClass Structure
highlight! default link uvmGenericPayloadClass Type
highlight! default link uvmResourceClass Type
highlight! default link uvmRegAdapterClass Type
highlight! default link uvmRegSequenceClass Type
highlight! default link uvmRegBusOpClass Type
highlight! default link uvmObjectionClass Type
highlight! default link uvmCoreClass Type
highlight! default link uvmPrinterClass Type
highlight! default link uvmAnalysisClass Type
highlight! default link uvmCallbacksClass Type
highlight! default link uvmCallbackMacros Macro
highlight! default link uvmTopGlobal Global
highlight! default link uvmPhaseClass Type
highlight! default link uvmCmdlineClass Type
highlight! default link uvmRecorderClass Type
highlight! default link uvmComparerClass Type
highlight! default link uvmPackerClass Type
highlight! default link uvmMemClass Type
highlight! default link uvmMemMamClass Type
highlight! default link uvmMemMamCfgClass Type
highlight! default link uvmRegFrontdoorClass Type
highlight! default link uvmRegBackdoorClass Type
highlight! default link uvmRegCbsClass Type
highlight! default link uvmRegItemClass Type
highlight! default link uvmReportHandlerClass Type
highlight! default link uvmReportCatcherClass Type
highlight! default link uvmTrDbClass Type
highlight! default link uvmTrStreamClass Type
highlight! default link uvmTrRecClass Type
highlight! default link uvmTlmFifoClass Structure
highlight! default link uvmSeqLibClass Type
highlight! default link uvmDefaultPrinter Global
highlight! default link uvmDefaultComparer Global
highlight! default link uvmDefaultPacker Global
highlight! default link uvmRegSeqName Identifier
highlight! default link uvmRunTest Function
highlight! default link uvmTestDone Global
highlight! default link svCtorCall Function
highlight! default link uvmTypeIdCreate Function
highlight! default link svRandCallback Function

highlight! default link uvmConfig Structure
highlight! default link uvmResource Structure
highlight! default link uvmPort StorageClass
highlight! default link uvmSocket Structure
highlight! default link uvmTLM Structure
highlight! default link uvmReg Structure
highlight! default link uvmEnum Constant
highlight! default link uvmMacros Macro
highlight! default link uvmMethodObjection Keyword
highlight! default link uvmMethodTrans Operator
highlight! default link uvmMethodSeqCtrl Repeat
highlight! default link uvmMethodFactory Structure
highlight! default link uvmMethodConfig Label
highlight! default link uvmPhase Type
highlight! default link uvmSeq Identifier
highlight! default link uvmRegApi Operator
highlight! default link uvmHDLApi Operator
highlight! default link uvmEventMethod Statement
highlight! default link uvmMethodInfo Global
