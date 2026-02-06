" Vim syntax file
" Language:	systemverilog
" Maintainer:	sqlmap3 < https://github.com/sqlmap3 >
" Version:	0.1
" First Change:	Sat Dec 06 11:15:30 CST 2025
" Last Change:	Sat Dec 06 11:15:30 CST 2025
if exists("b:current_syntax")
	finish
endif

let b:current_syntax = "systemverilog"

syntax keyword svTodo TODO contained
syntax match svLineComment "//.*" contains=svTodo
syntax region svBlockComment start="/\*" end="\*/" contains=svTodo
syntax region svString start=+"+ skip=+\\"+ end=+"+
syntax keyword svType real realtime event reg wire integer logic bit time byte chandle genvar signed unsigned shortint shortreal string void int specparam
syntax keyword svDirection input output inout ref
syntax keyword svStorageClass virtual var protected rand const static automatic extern forkjoin export import
syntax match svPreProc "`\(__FILE__\|__LINE__\|begin_keywords\|celldefine\|default_nettype\|end_keywords\|endcelldefine\|include\|line\|nounconnected_drive\|pragma\|resetall\|timescale\|unconnected_drive\|undef\|undefineall\)\>"
" only else/elsif/endif here
syntax match svPreCondit "`\(else\|elsif\|endif\)\>"
syntax match svInclude "`include\>"
" `define itself, and let next token be svDefineName
syntax match svDefine "`define\>" nextgroup=svDefineName skipwhite

syntax keyword svConditional if else iff case casez casex endcase
syntax keyword svRepeat for foreach do while forever repeat
syntax keyword svKeyword fork join join_any join_none begin end module endmodule function endfunction task endtask always always_ff always_latch always_comb initial this generate endgenerate config endconfig class endclass clocking endclocking interface endinterface package endpackage modport posedge negedge edge defparam assign deassign alias return disable wait continue and buf bufif0 bufif1 nand nor not or xnor xor tri tri0 tri1 triand trior trireg pull0 pull1 pullup pulldown cmos default endprimitive endspecify endtable force highz0 highz1 ifnone large macromodule medium nmos notif0 notif1 pmos primitive rcmos release rnmos rpmos rtran rtranif0 rtranif1 scalared small specify strong0 strong1 supply0 supply1 table tran tranif0 tranif1 vectored wand weak0 weak1 wor cell design incdir liblist library noshowcancelled pulsestyle_ondetect pulsestyle_onevent showcancelled use instance uwire assert assume before bind bins binsof break constraint context cover covergroup coverpoint cross dist endgroup endprogram endproperty endsequence expect extends final first_match ignore_bins illegal_bins inside intersect local longint matches new null packed priority program property pure randc randcase randsequence sequence solve super tagged throughout timeprecision timeunit type unique wait_order wildcard with within accept_on checker endchecker eventually global implies let nexttime reject_on restrict s_always s_eventually s_nexttime s_until s_until_with strong sync_accept_on sync_reject_on unique0 until until_with untyped weak implements interconnect nettype soft
" Numeric literals
" Plain decimal without base specifier
syntax match svInteger "\<\(\.\)\@<![0-9_]\+\(\s*['.]\)\@!\>"
" Based literals: [width]'[signed][base][digits] with base-specific digit validation
syntax match svInteger "\(\<[0-9_]\+\s*\)\?'\(s\|S\)\?\(d\|D\)\s*[0-9_ZzXx?]\+"
syntax match svInteger "\(\<[0-9_]\+\s*\)\?'\(s\|S\)\?\(h\|H\)\s*[0-9a-fA-F_ZzXx?]\+"
syntax match svInteger "\(\<[0-9_]\+\s*\)\?'\(s\|S\)\?\(o\|O\)\s*[0-7_ZzXx?]\+"
syntax match svInteger "\(\<[0-9_]\+\s*\)\?'\(s\|S\)\?\(b\|B\)\s*[01_ZzXx?]\+"
" Unbased unsized literals: 'd, 'h, 'o, 'b
syntax match svInteger "\<'\(d\|D\|h\|H\|o\|O\|b\|B\)\>"
" Single bit literals
syntax match svInteger "'[01xXzZ?]\>"
" Real number literals
syntax match svReal "\<[0-9_]\+\.[0-9_]\+\(\(e\|E\)[+-]\?[0-9_]\+\)\?\>"
syntax match svReal "\<[0-9_]\+\(e\|E\)[+-]\?[0-9_]\+\>"
syntax keyword svStructure struct union enum
syntax keyword svTypedef typedef parameter localparam
syntax match svSystemFunction "\$\(display\|displayb\|displayo\|displayh\|write\|writeb\|writeo\|writeh\|strobe\|strobeb\|strobeh\|strobeo\|monitor\|monitorb\|monitorh\|monitoro\|fopen\|fclose\|ftell\|fseek\|rewind\|fdisplay\|fdisplayb\|fdisplayh\|fdisplayo\|fwrite\|fwriteb\|fwriteh\|fwriteo\|fstrobe\|fstrobeb\|fstrobeh\|fstrobeo\|fmonitor\|fmonitorb\|fmonitorh\|fmonitoro\|finish\|stop\|exit\|realtime\|stime\|time\|printtimescale\|timeformat\|bitstoreal\|realtobits\|bitstoshortreal\|shortrealtobits\|itor\|rtoi\|signed\|unsigned\|cast\|bits\|isunbounded\|typename\|unpacked_dimensions\|dimensions\|left\|right\|low\|high\|increment\|size\|clog2\|asin\|ln\|acos\|log10\|atan\|exp\|atan2\|sqrt\|hypot\|pow\|sinh\|floor\|cosh\|ceil\|tanh\|sin\|asinh\|cos\|acosh\|tan\|atanh\|countbits\|countones\|onehot\|onehot0\|isunknown\|fatal\|error\|warning\|info\|fatal\|error\|warning\|info\|asserton\|assertoff\|assertkill\|assertcontrol\|assertpasson\|assertpassoff\|assertfailon\|assertfailoff\|assertnonvacuouson\|assertvacuousoff\|sampled\|rose\|fell\|stable\|changed\|past\|past_gclk\|rose_gclk\|fell_gclk\|stable_gclk\|changed_gclk\|future_gclk\|rising_gclk\|falling_gclk\|steady_gclk\|changing_gclk\|coverage_control\|coverage_get_max\|coverage_get\|coverage_merge\|coverage_save\|get_coverage\|set_coverage_db_name\|load_coverage_db\|random\|urandom\|urandom_range\|dist_chi_square\|dist_erlang\|dist_exponential\|dist_normal\|dist_poisson\|dist_t\|dist_uniform\|q_initialize\|q_add\|q_remove\|q_full\|q_exam\|asyncandarray\|asyncandplane\|asyncnandarray\|asyncnandplane\|asyncorarray\|asyncorplane\|asyncnorarray\|asyncnorplane\|syncandarray\|syncandplane\|syncnandarray\|syncnandplane\|syncorarray\|syncorplane\|syncnorarray\|syncnorplane\|system\|contained\|transparent\|dumpfile\|dumpvars\|dumpon\|dumpoff\|dumpall\|dumplimit\|dumpflush\|readmemb\|readmemh\|writememb\|writememh\)\>"
syntax match svObjectFunctions "\.\(num\|size\|delete\|exists\|first\|last\|next\|prev\|insert\|pop_front\|pop_back\|push_front\|push_back\|find\|find_index\|find_first\|find_first_index\|find_last\|find_last_index\|min\|max\|reverse\|sort\|rsort\|shuffle\|sum\|product\|and\|or\|xor\)\>\_s*("he=e-1
syntax match svOperator "\(\~\|&\|||\|\^\|=\|!\|?\|:\|@\|<\|>\|%\|+\|-\|\*\|\/[\/\*]\@!\)"
syntax match svDelimiter "\({\|}\|(\|)\)"

syntax match svSVAOp "\(|->\|=>\|##\d\+\|##\|\[\*\(\d\+\(:\d\+\)\?\)\?\]\)"

" Covergroup / coverpoint / bins names
syntax match svCovergroupName "\<covergroup\>\s\+\zs\h\w*"
" Macro guard names
syntax match svIfndefTok "`ifndef\>" skipwhite
syntax match svIfdefTok  "`ifdef\>"  skipwhite
" Highlight macro names that follow `ifndef/`ifdef/`define
" e.g. `ifndef AAA / `ifdef FOO_BAR / `define MY_MACRO
syntax match svIfndefName "\%(`ifndef\s\+\)\@<=\h\w*"
syntax match svIfdefName  "\%(`ifdef\s\+\)\@<=\h\w*"
syntax match svDefineName "\%(`define\s\+\)\@<=\h\w*"
" Macro usage in normal code: `AAA, `foo_bar, etc.
syntax match svMacroRef "`\h\w*"
syntax match svUpperDot    "\<[A-Z0-9_]\+\(\.[A-Z0-9_]\+\)\+\>"
syntax match svHashNumber  "#[0-9_]\+"
syntax match svTimeUnitHash  "#[0-9_]\+\s*\zs\(fs\|ps\|ns\|us\|ms\|s\)\>"
syntax match svTimeUnitPlain "\<[0-9_]\+\s*\zs\(fs\|ps\|ns\|us\|ms\|s\)\>"
syntax match svCoverLabel "\<\zs\h\w*\ze\s*:\s*\(coverpoint\|cross\)\>"
syntax match svBinsName "\<\(wildcard\s\+\)\?bins\>\s\+\zs\h\w*"
syntax match svBinsName "\<\(illegal_bins\|ignore_bins\)\>\s\+\zs\h\w*"

" binsof/intersect expressions and with/iff predicates
syntax region svBinsofExpr start="\<binsof\>\s*(" end=")" keepend
syntax region svIntersectExpr start="\<intersect\>\s*{" end="}" keepend
syntax region svCoverWithPred start="\<with\>\s*(" end=")" keepend
syntax region svCoverIffPred start="\<iff\>\s*(" end=")" keepend



" domain/event/barrier/analysis fifo and payload
syntax match uvmDomainClass "\<uvm_domain\>"
syntax match uvmDomainApi "\<uvm_domain#\>\s*::\s*\(add\|find\|get_common_domain\|add_phase\|remove_phase\|sync\)\>"

syntax match uvmBarrierClass "\<uvm_barrier\>"
syntax match uvmBarrierPoolClass "\<uvm_barrier_pool\>"
syntax match uvmBarrierApi "\<uvm_barrier#\>\s*::\s*\(set\|get\|wait\|reset\|set_auto\)\>"

syntax match uvmEventClass "\<uvm_event\>"
syntax match uvmEventPoolClass "\<uvm_event_pool\>"
syntax match uvmEventApi "\<uvm_event#\>\s*::\s*\(trigger\|wait_trigger\|wait_ptrigger\|wait_on\|wait_off\)\>"

syntax match uvmAnalysisFifoClass "\<uvm_tlm_analysis_fifo\>"

syntax match uvmGenericPayloadClass "\<uvm_tlm_generic_payload\>"

syntax match uvmResourceClass "\<uvm_resource\>"
syntax match uvmResourceApi3 "\<uvm_resource#\>\s*::\s*\(set\|get\|get_default\|set_default\|lookup_name\|match\)\>"

syntax match uvmRegBlockApi "\<uvm_reg_block#\>\s*::\s*\(build\|lock_model\|reset\|get_map\|add_reg\|get_reg_by_name\)\>"
syntax match uvmRegMapApi "\<uvm_reg_map#\>\s*::\s*\(add_reg\|set_base_addr\|get_addr\|read\|write\)\>"
syntax match uvmRegFieldApi "\<uvm_reg_field#\>\s*::\s*\(set\|get\|predict\|mirror\|write\|read\)\>"
syntax match uvmRegPredictorApi "\<uvm_reg_predictor#\>\s*::\s*\(map\|set_sequencer\|set_adapter\|write\|read\)\>"
syntax match uvmRegAdapterClass "\<uvm_reg_adapter\>"
syntax match uvmRegSequenceClass "\<uvm_reg_sequence\>"
syntax match uvmRegBusOpClass "\<uvm_reg_bus_op\>"
syntax match uvmFactoryApi "\<uvm_factory#\>\s*::\s*\(set_type_override_by_type\|set_type_override\|set_inst_override_by_type\|set_inst_override\|create_object\|create_object_by_name\|create_component\|create_component_by_name\|print\)\>"
syntax match uvmResourcePoolApi "\<uvm_resource_pool#\>\s*::\s*\(set\|get\|find\|get_by_name\|lookup_name\|match\|push\|pop\)\>"

" uvm_objection class and APIs
syntax match uvmObjectionClass "\<uvm_objection\>"
syntax match uvmObjectionApiOb    "\<uvm_objection#\>\s*::\s*\(raise_objection\|drop_objection\)\>"
syntax match uvmObjectionApiDrain "\<uvm_objection#\>\s*::\s*\(set_drain_time\|get_drain_time\)\>"
syntax match uvmObjectionApiOther "\<uvm_objection#\>\s*::\s*\(clear\|get_objection\)\>"

" core classes and printers
syntax keyword uvmCoreClass uvm_object uvm_component uvm_root uvm_test uvm_env uvm_agent uvm_driver uvm_monitor uvm_scoreboard uvm_sequencer uvm_sequence uvm_sequence_item uvm_report_object
syntax match uvmPrinterClass "\<uvm_\(printer\|table_printer\|tree_printer\|line_printer\)\>"
syntax match uvmAnalysisClass "\<uvm_analysis_\(port\|imp\|export\)\>"

" callbacks
syntax match uvmCallbacksClass "\<uvm_\(callback\|callbacks\)\>"
syntax match uvmCallbacksApi "\<uvm_callbacks#\>\s*::\s*\(add\|delete\|reset\|enable\|disable\|exists\)\>"
syntax match uvmCallbackMacros "\<uvm_\(register_cb\|do_callbacks\|do_callbacks_exit\)\>"

" globals
syntax match uvmTopGlobal "\<uvm_top\>"

" uvm_phase class and APIs
syntax match uvmPhaseClass "\<uvm_phase\>"
syntax match uvmPhaseApiOb   "\<uvm_phase#\>\s*::\s*\(raise_objection\|drop_objection\)\>"
syntax match uvmPhaseApiCtrl "\<uvm_phase#\>\s*::\s*\(jump\|kill\|sync\)\>"
syntax match uvmPhaseApiInfo "\<uvm_phase#\>\s*::\s*\(get_name\|is_ready_to_end\)\>"

" cmdline processor
syntax match uvmCmdlineClass "\<uvm_cmdline_processor\>"
syntax match uvmCmdlineApi "\<uvm_cmdline_processor#\>\s*::\s*\(get_argc\|get_argv\|get_switches\|get_arg_value\|get_arg_values\|check_switch\)\>"

" recorder/comparer/packer
syntax match uvmRecorderClass "\<uvm_recorder\>"
syntax match uvmComparerClass "\<uvm_comparer\>"
syntax match uvmPackerClass   "\<uvm_packer\>"
syntax match uvmRecorderApi "\<uvm_recorder#\>\s*::\s*\(record_field\|record_object\|record_string\|record_int\|record_real\)\>"
syntax match uvmComparerApi "\<uvm_comparer#\>\s*::\s*\(compare_field\|compare_object\|compare_string\|compare_int\|compare_real\)\>"
syntax match uvmPackerApi   "\<uvm_packer#\>\s*::\s*\(pack_field\|pack_object\|unpack_field\|unpack_object\)\>"

" add do_record/do_unpack to method set
syntax keyword uvmMethodTrans do_record pack unpack unpack_bytes pack_bytes

" RAL: memory and MAM
syntax match uvmMemClass "\<uvm_mem\>"
syntax match uvmMemApi "\<uvm_mem#\>\s*::\s*\(read\|write\|poke\|peek\|get\|set\|get_default_map\|set_default_map\|set_frontdoor\|set_backdoor\|set_hdl_path\)\>"

syntax match uvmMemMamClass    "\<uvm_mem_mam\>"
syntax match uvmMemMamCfgClass "\<uvm_mem_mam_cfg\>"
syntax match uvmMemMamCfgApi "\<uvm_mem_mam_cfg#\>\s*::\s*\(set_mode\|get_mode\|set_min_addr\|set_max_addr\|set_alignment\|set_granularity\)\>"
syntax match uvmMemMamApi "\<uvm_mem_mam#\>\s*::\s*\(request\|release\|reserve\|free\|align\)\>"

" RAL: frontdoor/backdoor
syntax match uvmRegFrontdoorClass "\<uvm_reg_frontdoor\>"
syntax match uvmRegBackdoorClass  "\<uvm_reg_backdoor\>"
syntax match uvmRegFrontdoorApi "\<uvm_reg_frontdoor#\>\s*::\s*\(set_sequencer\|set_adapter\)\>"
syntax match uvmRegBackdoorApi  "\<uvm_reg_backdoor#\>\s*::\s*\(set_hdl_path\|get_hdl_path\|set_access\)\>"

" RAL: callbacks and items
syntax match uvmRegCbsClass "\<uvm_reg_cbs\>"
syntax match uvmRegCbsApi "\<uvm_reg_cbs#\>\s*::\s*\(pre_read\|post_read\|pre_write\|post_write\|post_predict\)\>"
syntax match uvmRegItemClass "\<uvm_reg_item\>"

" RAL: block HDL path helpers
syntax match uvmRegBlockHdlApi "\<uvm_reg_block#\>\s*::\s*\(set_hdl_path_root\|get_hdl_path_root\|add_hdl_path\|clear_hdl_path\)\>"

" Report handler/catcher
syntax match uvmReportHandlerClass "\<uvm_report_handler\>"
syntax match uvmReportHandlerApi "\<uvm_report_handler#\>\s*::\s*\(set_verbosity\|set_max_quit_count\|set_id_action\|set_severity_action\|set_severity_id_action\|set_file\)\>"
syntax match uvmReportCatcherClass "\<uvm_report_catcher\>"
syntax match uvmReportCatcherApi "\<uvm_report_catcher#\>\s*::\s*\(add\|delete\|catch\|process\)\>"

" Transaction recording
syntax match uvmTrDbClass     "\<uvm_tr_database\>"
syntax match uvmTrStreamClass "\<uvm_tr_stream\>"
syntax match uvmTrRecClass    "\<uvm_tr_recorder\>"
syntax match uvmTrDbApi     "\<uvm_tr_database#\>\s*::\s*\(open_db\|close\|create_stream\)\>"
syntax match uvmTrStreamApi "\<uvm_tr_stream#\>\s*::\s*\(open_stream\|close\|begin_tr\|end_tr\)\>"
syntax match uvmTrRecApi    "\<uvm_tr_recorder#\>\s*::\s*\(record_attribute\|flush\|start\|stop\)\>"

" TLM FIFO (generic)
syntax match uvmTlmFifoClass "\<uvm_tlm_fifo\>"
syntax match uvmTlmFifoApi "\<uvm_tlm_fifo#\>\s*::\s*\(write\|try_write\|get\|try_get\|peek\|try_peek\|can_get\|can_put\|can_peek\|is_empty\|size\)\>"

" Sequence library
syntax match uvmSeqLibClass "\<uvm_sequence_library\>"
syntax match uvmSeqLibApi "\<uvm_sequence_library#\>\s*::\s*\(add_sequence\|randomize\|execute\|get_sequences\)\>"

" Default globals
syntax match uvmDefaultPrinter   "\<uvm_default_printer\>"
syntax match uvmDefaultComparer  "\<uvm_default_comparer\>"
syntax match uvmDefaultPacker    "\<uvm_default_packer\>"

" Covergroup options
syntax match svCoverOption "\<option\>\.\h\w*"
syntax match svCoverTypeOption "\<type_option\>\.\h\w*"

" RAL common sequences names
syntax match uvmRegSeqName "\<uvm_reg_\(bit_bash\|access\|hw_reset\|mem_built_in\|mem_access\)_seq\>"

" Resource DB extra
syntax match uvmResourceApi4 "\<uvm_resource_db#\>\s*::\s*\(get_by_scope\)\>"

" Reg block extras
syntax match uvmRegBlockApi2 "\<uvm_reg_block#\>\s*::\s*\(add_mem\|get_mem_by_name\|get_field_by_name\)\>"

" Root and run_test
syntax match uvmRunTest "\<run_test\>"
syntax match uvmRootApi "\<uvm_root#\>\s*::\s*\(get\|set_timeout\|get_timeout\|set_report_verbosity_level\|set_max_quit_count\|enable_stop_request\|stop_request\)\>"

" Report object getters/setters
syntax match uvmReportObjectApi "\<uvm_report_object#\>\s*::\s*\(set_report_verbosity_level\|get_report_verbosity_level\|set_report_severity_action\|get_report_severity_action\|set_report_id_action\|set_report_default_file\)\>"

syntax match uvmReportObjectApi2 "\<uvm_report_object#\>\s*::\s*\(set_report_severity_override\|get_report_severity_override\|set_report_severity_id_override\|get_report_severity_id_override\|clear_report_severity_override\|clear_report_severity_id_override\)\>"

" Sequence item helpers
syntax match uvmSeqItemApi "\<uvm_sequence_item#\>\s*::\s*\(set_id_info\|set_sequence_id\|get_transaction_id\|is_response\)\>"

" Global test objection
syntax match uvmTestDone "\<uvm_test_done\>"

syntax match uvmCtor "\<uvm_[A-Za-z0-9_]\+#\>\s*::\s*new\>"
syntax match svCtorCall "\<\(super\|this\)\>\s*\.\s*new\>"
syntax match uvmTypeIdCreate "\<type_id\>\s*::\s*create\>"
syntax match uvmObjectCreate "\<uvm_object#\>\s*::\s*create\>"
syntax keyword svRandCallback pre_randomize post_randomize
syntax match uvmConfig "\<uvm_config_db\>"
syntax match uvmResource "\<uvm_resource_db\>"
highlight! default link uvmConfig Structure
highlight! default link uvmResource Structure

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

syntax match uvmMacros "\<uvm_field_\w\+\>"
syntax match uvmMacros "\<uvm_object_utils\(_begin\|_end\|_param\w*\)\>"
syntax match uvmMacros "\<uvm_component_utils\(_begin\|_end\|_param\w*\)\>"
syntax match uvmMacros "\<uvm_do\(_\w\+\)\?\>"
syntax match uvmMacros "\<uvm_\(pack\|unpack\|record\|print\)_\w\+\>"
syntax match uvmMacros "\<uvm_\(error\|warning\|info\|fatal\)\(_context\)\?\>"
highlight! default link uvmMacros Macro

syntax keyword uvmMethodObjection raise_objection drop_objection global_stop_request
syntax keyword uvmMethodTrans get put peek try_get try_put try_peek try_next_item b_transport nb_transport_fw nb_transport_bw
syntax keyword uvmMethodSeqCtrl start_item finish_item item_done
syntax keyword uvmMethodSeqCtrl wait_for_grant send_request wait_for_item_done
syntax keyword uvmMethodSeqCtrl grab ungrab lock unlock
syntax keyword uvmMethodFactory create type_id set_type_override_by_type set_inst_override_by_type
syntax keyword uvmMethodConfig set_config set_report_verbosity_level set_report_severity_action set_report_id_action set_report_default_file
highlight! default link uvmMethodObjection Keyword
highlight! default link uvmMethodTrans Operator
highlight! default link uvmMethodSeqCtrl Repeat
highlight! default link uvmMethodFactory Structure
highlight! default link uvmMethodConfig Label

syntax keyword uvmPhase build_phase check_phase configure_phase connect_phase define_domain do_kill end_of_elaboration_phase exec_task extract_phase final_phase main_phase phase_ended phase_ready_to_end phase_started post_configure_phase post_main_phase post_reset_phase post_shutdown_phase pre_configure_phase pre_main_phase pre_reset_phase pre_shutdown_phase report_phase reset_phase run_phase shutdown_phase start_of_simulation_phase
" Match uvm_*_phase patterns for standard UVM phases
syntax match uvmPhase "\<uvm_\(build\|connect\|end_of_elaboration\|start_of_simulation\|run\|extract\|check\|report\|final\)_phase\>"
" Match uvm_*_phase patterns for reset phases
syntax match uvmPhase "\<uvm_\(pre_reset\|reset\|post_reset\)_phase\>"
" Match uvm_*_phase patterns for configure/main/shutdown phases
syntax match uvmPhase "\<uvm_\(pre_configure\|configure\|post_configure\|pre_main\|main\|post_main\|pre_shutdown\|shutdown\|post_shutdown\)_phase\>"
highlight! default link uvmPhase Type

syntax keyword uvmSeq uvm_reg_bit_hash_seq uvm_reg_hw_reset_seq uvm_reg_mem_built_in_seq
highlight! default link uvmSeq Identifier

syntax match uvmConfigApi "\<uvm_config_db#\>\s*::\s*\(set\|get\|exists\)\>"
syntax match uvmResourceApi "\<uvm_resource_db#\>\s*::\s*\(set\|get\|find\|get_by_name\)\>"
highlight! default link uvmConfigApi Label
highlight! default link uvmResourceApi Label

syntax match uvmResourceApi2 "\<uvm_resource_db#\>\s*::\s*\(get_by_type\|set_default\)\>"
highlight! default link uvmResourceApi2 Label

syntax match uvmRegApi "\<uvm_reg_[A-Za-z0-9_]\+\>\s*::\s*\(read\|write\|mirror\|predict\|poke\|peek\|update\)\>"
highlight! default link uvmRegApi Operator

syntax match uvmHDLApi "\<uvm_hdl_\(read\|write\|force\|release\)\>"
highlight! default link uvmHDLApi Operator

syntax keyword uvmEventMethod trigger wait_on wait_off wait_for wait_ptrigger wait_trigger
highlight! default link uvmEventMethod Statement

syntax keyword uvmMethodInfo get_type_name get_full_name get_name get_parent get_children get_child get_children
highlight! default link uvmMethodInfo Global
syntax match uvmFactoryApi2 "\<uvm_factory#\>\s*::\s*\(set_type_override_by_name\|set_inst_override_by_name\)\>"
highlight! default link uvmFactoryApi2 Structure
syntax match uvmAnalysisApi "\<uvm_analysis_\(port\|imp\|export\)#\>\s*::\s*write\>"
highlight! default link uvmAnalysisApi Function
syntax match uvmSubscriberApi "\<uvm_subscriber#\>\s*::\s*write\>"
highlight! default link uvmSubscriberApi Function
syntax match uvmReportServerApi "\<uvm_report_server#\>\s*::\s*\(process_report\|summarize\|report_hook\)\>"
highlight! default link uvmReportServerApi Global
syntax match uvmSequenceApi "\<uvm_sequence_\(base\|item\)#\>\s*::\s*\(start\|stop\|pre_body\|post_body\)\>"
highlight! default link uvmSequenceApi Repeat
syntax match uvmSequencerApi "\<uvm_sequencer_\(base\)#\>\s*::\s*\(start_item\|finish_item\|get_next_item\|try_next_item\)\>"
highlight! default link uvmSequencerApi Repeat
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
highlight! default link svInclude Include
highlight! default link svDefine Macro          " `define keyword as Macro
" macros in conditional guards/defines
highlight! default link svIfndefTok Macro       " `ifndef keyword as Macro
highlight! default link svIfdefTok  Macro       " `ifdef  keyword as Macro
highlight! default link svConditional Conditional
highlight! default link svRepeat Repeat
highlight! default link svKeyword Keyword
highlight! default link svInteger Number
highlight! default link svReal Float
highlight! default link svStructure Structure
highlight! default link svTypedef Typedef
highlight! default link svSystemFunction Function
highlight! default link svOperator Operator
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
highlight! default link svUpperDot Number
highlight! default link svHashNumber Number
" Highlight user macro usage
highlight! default link svMacroRef Macro
highlight! default link svTimeUnitHash Special
highlight! default link svTimeUnitPlain Special

highlight! default link uvmDomainClass Type
highlight! default link uvmDomainApi Structure
highlight! default link uvmBarrierClass Type
highlight! default link uvmBarrierPoolClass Type
highlight! default link uvmBarrierApi Label
highlight! default link uvmEventClass Type
highlight! default link uvmEventPoolClass Type
highlight! default link uvmEventApi Statement
highlight! default link uvmAnalysisFifoClass Structure
highlight! default link uvmGenericPayloadClass Type
highlight! default link uvmResourceClass Type
highlight! default link uvmResourceApi3 Label
highlight! default link uvmRegBlockApi Structure
highlight! default link uvmRegMapApi Operator
highlight! default link uvmRegFieldApi Operator
highlight! default link uvmRegPredictorApi Structure
highlight! default link uvmRegAdapterClass Type
highlight! default link uvmRegSequenceClass Type
highlight! default link uvmRegBusOpClass Type
highlight! default link uvmFactoryApi Structure
highlight! default link uvmResourcePoolApi Label
highlight! default link uvmObjectionClass Type
highlight! default link uvmObjectionApiOb Keyword
highlight! default link uvmObjectionApiDrain Label
highlight! default link uvmObjectionApiOther Global
highlight! default link uvmCoreClass Type
highlight! default link uvmPrinterClass Type
highlight! default link uvmAnalysisClass Type
highlight! default link uvmCallbacksClass Type
highlight! default link uvmCallbacksApi Label
highlight! default link uvmCallbackMacros Macro
highlight! default link uvmTopGlobal Global
highlight! default link uvmPhaseClass Type
highlight! default link uvmPhaseApiOb Keyword
highlight! default link uvmPhaseApiCtrl Operator
highlight! default link uvmPhaseApiInfo Global
highlight! default link uvmCmdlineClass Type
highlight! default link uvmCmdlineApi Label
highlight! default link uvmRecorderClass Type
highlight! default link uvmComparerClass Type
highlight! default link uvmPackerClass Type
highlight! default link uvmRecorderApi Operator
highlight! default link uvmComparerApi Operator
highlight! default link uvmPackerApi Operator
highlight! default link uvmMemClass Type
highlight! default link uvmMemApi Operator
highlight! default link uvmMemMamClass Type
highlight! default link uvmMemMamCfgClass Type
highlight! default link uvmMemMamCfgApi Label
highlight! default link uvmMemMamApi Operator
highlight! default link uvmRegFrontdoorClass Type
highlight! default link uvmRegBackdoorClass Type
highlight! default link uvmRegFrontdoorApi Structure
highlight! default link uvmRegBackdoorApi Label
highlight! default link uvmRegCbsClass Type
highlight! default link uvmRegCbsApi Function
highlight! default link uvmRegItemClass Type
highlight! default link uvmRegBlockHdlApi Label
highlight! default link uvmReportHandlerClass Type
highlight! default link uvmReportHandlerApi Label
highlight! default link uvmReportCatcherClass Type
highlight! default link uvmReportCatcherApi Function
highlight! default link uvmTrDbClass Type
highlight! default link uvmTrStreamClass Type
highlight! default link uvmTrRecClass Type
highlight! default link uvmTrDbApi Structure
highlight! default link uvmTrStreamApi Operator
highlight! default link uvmTrRecApi Operator
highlight! default link uvmTlmFifoClass Structure
highlight! default link uvmTlmFifoApi Operator
highlight! default link uvmSeqLibClass Type
highlight! default link uvmSeqLibApi Repeat
highlight! default link uvmDefaultPrinter Global
highlight! default link uvmDefaultComparer Global
highlight! default link uvmDefaultPacker Global
highlight! default link uvmRegSeqName Identifier
highlight! default link uvmResourceApi4 Label
highlight! default link uvmRegBlockApi2 Structure
highlight! default link uvmRunTest Function
highlight! default link uvmRootApi Label
highlight! default link uvmReportObjectApi Label
highlight! default link uvmReportObjectApi2 Label
highlight! default link uvmSeqItemApi Label
highlight! default link uvmTestDone Global
highlight! default link uvmCtor Function
highlight! default link svCtorCall Function
highlight! default link uvmTypeIdCreate Function
highlight! default link uvmObjectCreate Function
highlight! default link svRandCallback Function
