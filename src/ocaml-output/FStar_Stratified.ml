
open Prims
# 39 "FStar.Stratified.fst"
let module_or_interface_name : FStar_Absyn_Syntax.modul  ->  (Prims.bool * FStar_Absyn_Syntax.lident) = (fun m -> (m.FStar_Absyn_Syntax.is_interface, m.FStar_Absyn_Syntax.name))

# 44 "FStar.Stratified.fst"
let parse : FStar_Parser_DesugarEnv.env  ->  Prims.string  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env fn -> (
# 46 "FStar.Stratified.fst"
let ast = (FStar_Parser_Driver.parse_file fn)
in (FStar_Parser_Desugar.desugar_file env ast)))

# 52 "FStar.Stratified.fst"
let tc_prims : Prims.unit  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun _86_5 -> (match (()) with
| () -> begin
(
# 55 "FStar.Stratified.fst"
let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_ToSMT_Encode.solver
end else begin
FStar_ToSMT_Encode.dummy
end
in (
# 56 "FStar.Stratified.fst"
let env = (FStar_Tc_Env.initial_env solver FStar_Absyn_Const.prims_lid)
in (
# 57 "FStar.Stratified.fst"
let _86_8 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.init env)
in (
# 58 "FStar.Stratified.fst"
let p = (FStar_Options.prims ())
in (
# 59 "FStar.Stratified.fst"
let _86_13 = (let _175_9 = (FStar_Parser_DesugarEnv.empty_env ())
in (parse _175_9 p))
in (match (_86_13) with
| (dsenv, prims_mod) -> begin
(
# 60 "FStar.Stratified.fst"
let _86_16 = (let _175_10 = (FStar_List.hd prims_mod)
in (FStar_Tc_Tc.check_module env _175_10))
in (match (_86_16) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

# 66 "FStar.Stratified.fst"
let tc_one_file : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun dsenv env fn -> (
# 69 "FStar.Stratified.fst"
let _86_22 = (parse dsenv fn)
in (match (_86_22) with
| (dsenv, fmods) -> begin
(
# 70 "FStar.Stratified.fst"
let _86_32 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _86_25 m -> (match (_86_25) with
| (env, all_mods) -> begin
(
# 72 "FStar.Stratified.fst"
let _86_29 = (FStar_Tc_Tc.check_module env m)
in (match (_86_29) with
| (ms, env) -> begin
(env, (FStar_List.append ms all_mods))
end))
end)) (env, [])))
in (match (_86_32) with
| (env, all_mods) -> begin
((FStar_List.rev all_mods), dsenv, env)
end))
end)))

# 79 "FStar.Stratified.fst"
let batch_mode_tc_no_prims : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun dsenv env filenames -> (
# 80 "FStar.Stratified.fst"
let _86_50 = (FStar_All.pipe_right filenames (FStar_List.fold_left (fun _86_39 f -> (match (_86_39) with
| (all_mods, dsenv, env) -> begin
(
# 82 "FStar.Stratified.fst"
let _86_41 = (FStar_Absyn_Util.reset_gensym ())
in (
# 83 "FStar.Stratified.fst"
let _86_46 = (tc_one_file dsenv env f)
in (match (_86_46) with
| (ms, dsenv, env) -> begin
((FStar_List.append all_mods ms), dsenv, env)
end)))
end)) ([], dsenv, env)))
in (match (_86_50) with
| (all_mods, dsenv, env) -> begin
(
# 86 "FStar.Stratified.fst"
let _86_51 = if ((FStar_ST.read FStar_Options.interactive) && ((FStar_Tc_Errors.get_err_count ()) = 0)) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
end else begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.finish ())
end
in (all_mods, dsenv, env))
end)))

# 91 "FStar.Stratified.fst"
let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun filenames -> (
# 92 "FStar.Stratified.fst"
let _86_57 = (tc_prims ())
in (match (_86_57) with
| (prims_mod, dsenv, env) -> begin
(
# 93 "FStar.Stratified.fst"
let _86_60 = (FStar_Dependences.find_deps_if_needed filenames)
in (match (_86_60) with
| (filenames, admit_fsi) -> begin
(
# 94 "FStar.Stratified.fst"
let _86_64 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_86_64) with
| (all_mods, dsenv, env) -> begin
((FStar_List.append prims_mod all_mods), dsenv, env)
end))
end))
end)))

# 100 "FStar.Stratified.fst"
let tc_one_fragment : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string  ->  (FStar_Absyn_Syntax.modul Prims.option * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some ((curmod, dsenv, env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(
# 107 "FStar.Stratified.fst"
let _86_90 = (FStar_Parser_Desugar.desugar_partial_modul curmod dsenv ast_modul)
in (match (_86_90) with
| (dsenv, modul) -> begin
(
# 108 "FStar.Stratified.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (_86_93) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (
# 111 "FStar.Stratified.fst"
let _86_98 = (FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_86_98) with
| (modul, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(
# 115 "FStar.Stratified.fst"
let _86_103 = (FStar_Parser_Desugar.desugar_decls dsenv ast_decls)
in (match (_86_103) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(
# 117 "FStar.Stratified.fst"
let _86_105 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit 1))
end
| Some (modul) -> begin
(
# 119 "FStar.Stratified.fst"
let _86_111 = (FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_86_111) with
| (modul, env) -> begin
Some ((Some (modul), dsenv, env))
end))
end)
end))
end)
end)
with
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(
# 124 "FStar.Stratified.fst"
let _86_76 = (FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Absyn_Syntax.Err (msg) -> begin
(
# 127 "FStar.Stratified.fst"
let _86_80 = (FStar_Tc_Errors.add_errors env (((msg, FStar_Range.dummyRange))::[]))
in None)
end
| e -> begin
(Prims.raise e)
end)

# 135 "FStar.Stratified.fst"
let interactive_tc : ((FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env), FStar_Absyn_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (
# 136 "FStar.Stratified.fst"
let pop = (fun _86_115 msg -> (match (_86_115) with
| (dsenv, env) -> begin
(
# 137 "FStar.Stratified.fst"
let _86_117 = (let _175_43 = (FStar_Parser_DesugarEnv.pop dsenv)
in (FStar_All.pipe_right _175_43 Prims.ignore))
in (
# 138 "FStar.Stratified.fst"
let _86_119 = (let _175_44 = (FStar_Tc_Env.pop env msg)
in (FStar_All.pipe_right _175_44 Prims.ignore))
in (
# 139 "FStar.Stratified.fst"
let _86_121 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _175_45 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _175_45 Prims.ignore)))))
end))
in (
# 142 "FStar.Stratified.fst"
let push = (fun _86_126 msg -> (match (_86_126) with
| (dsenv, env) -> begin
(
# 143 "FStar.Stratified.fst"
let dsenv = (FStar_Parser_DesugarEnv.push dsenv)
in (
# 144 "FStar.Stratified.fst"
let env = (FStar_Tc_Env.push env msg)
in (dsenv, env)))
end))
in (
# 147 "FStar.Stratified.fst"
let mark = (fun _86_133 -> (match (_86_133) with
| (dsenv, env) -> begin
(
# 148 "FStar.Stratified.fst"
let dsenv = (FStar_Parser_DesugarEnv.mark dsenv)
in (
# 149 "FStar.Stratified.fst"
let env = (FStar_Tc_Env.mark env)
in (dsenv, env)))
end))
in (
# 152 "FStar.Stratified.fst"
let reset_mark = (fun _86_139 -> (match (_86_139) with
| (dsenv, env) -> begin
(
# 153 "FStar.Stratified.fst"
let dsenv = (FStar_Parser_DesugarEnv.reset_mark dsenv)
in (
# 154 "FStar.Stratified.fst"
let env = (FStar_Tc_Env.reset_mark env)
in (dsenv, env)))
end))
in (
# 157 "FStar.Stratified.fst"
let commit_mark = (fun _86_145 -> (match (_86_145) with
| (dsenv, env) -> begin
(
# 158 "FStar.Stratified.fst"
let dsenv = (FStar_Parser_DesugarEnv.commit_mark dsenv)
in (
# 159 "FStar.Stratified.fst"
let env = (FStar_Tc_Env.commit_mark env)
in (dsenv, env)))
end))
in (
# 162 "FStar.Stratified.fst"
let check_frag = (fun _86_151 curmod text -> (match (_86_151) with
| (dsenv, env) -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _175_63 = (let _175_62 = (FStar_Tc_Errors.get_err_count ())
in (m, (dsenv, env), _175_62))
in Some (_175_63))
end
| _86_160 -> begin
None
end)
end))
in (
# 168 "FStar.Stratified.fst"
let report_fail = (fun _86_162 -> (match (()) with
| () -> begin
(
# 169 "FStar.Stratified.fst"
let _86_163 = (let _175_66 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _175_66 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_Tc_Errors.num_errs 0))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))




