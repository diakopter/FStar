
open Prims
# 27 "FStar.Extraction.ML.Env.fst"
type binding =
| Ty of (FStar_Absyn_Syntax.btvar * FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
| Bv of (FStar_Absyn_Syntax.bvvar * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)
| Fv of (FStar_Absyn_Syntax.fvvar * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)

# 28 "FStar.Extraction.ML.Env.fst"
let is_Ty = (fun _discr_ -> (match (_discr_) with
| Ty (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.Extraction.ML.Env.fst"
let is_Bv = (fun _discr_ -> (match (_discr_) with
| Bv (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.Extraction.ML.Env.fst"
let is_Fv = (fun _discr_ -> (match (_discr_) with
| Fv (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.Extraction.ML.Env.fst"
let ___Ty____0 = (fun projectee -> (match (projectee) with
| Ty (_70_6) -> begin
_70_6
end))

# 29 "FStar.Extraction.ML.Env.fst"
let ___Bv____0 = (fun projectee -> (match (projectee) with
| Bv (_70_9) -> begin
_70_9
end))

# 30 "FStar.Extraction.ML.Env.fst"
let ___Fv____0 = (fun projectee -> (match (projectee) with
| Fv (_70_12) -> begin
_70_12
end))

# 32 "FStar.Extraction.ML.Env.fst"
type env =
{tcenv : FStar_Tc_Env.env; gamma : binding Prims.list; tydefs : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}

# 32 "FStar.Extraction.ML.Env.fst"
let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 41 "FStar.Extraction.ML.Env.fst"
let debug : env  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun g f -> if (((FStar_ST.read FStar_Options.debug) <> []) && ((let _159_65 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.contains "Prims" _159_65)) || (g.currentModule <> ([], "Prims")))) then begin
(f ())
end else begin
()
end)

# 47 "FStar.Extraction.ML.Env.fst"
let mkFvvar : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Ident.lident, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t = (fun l t -> (let _159_70 = (FStar_Range.mk_range "" 0 0)
in {FStar_Absyn_Syntax.v = l; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _159_70}))

# 55 "FStar.Extraction.ML.Env.fst"
let erasedContent : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.ml_unit_ty

# 57 "FStar.Extraction.ML.Env.fst"
let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> if (t = FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
true
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_70_24, ("FStar"::"Ghost"::[], "erased")) -> begin
true
end
| _70_33 -> begin
false
end)
end)

# 64 "FStar.Extraction.ML.Env.fst"
let unknownType : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Top

# 67 "FStar.Extraction.ML.Env.fst"
let prependTick = (fun _70_36 -> (match (_70_36) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
(x, n)
end else begin
((Prims.strcat "\'A" x), n)
end
end))

# 68 "FStar.Extraction.ML.Env.fst"
let removeTick = (fun _70_39 -> (match (_70_39) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
(let _159_75 = (FStar_Util.substring_from x 1)
in (_159_75, n))
end else begin
(x, n)
end
end))

# 70 "FStar.Extraction.ML.Env.fst"
let convRange : FStar_Range.range  ->  Prims.int = (fun r -> 0)

# 71 "FStar.Extraction.ML.Env.fst"
let convIdent : FStar_Ident.ident  ->  (Prims.string * Prims.int) = (fun id -> (id.FStar_Ident.idText, (convRange id.FStar_Ident.idRange)))

# 86 "FStar.Extraction.ML.Env.fst"
let btvar_as_mltyvar : FStar_Absyn_Syntax.btvar  ->  (Prims.string * Prims.int) = (fun btv -> (prependTick (convIdent btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)))

# 88 "FStar.Extraction.ML.Env.fst"
let btvar_as_mlTermVar : FStar_Absyn_Syntax.btvar  ->  (Prims.string * Prims.int) = (fun btv -> (removeTick (convIdent btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)))

# 90 "FStar.Extraction.ML.Env.fst"
let rec lookup_ty_local : binding Prims.list  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| Ty (bt, mli, mlt)::tl -> begin
if (FStar_Absyn_Util.bvd_eq bt.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v) then begin
mlt
end else begin
(lookup_ty_local tl b)
end
end
| _70_55::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(FStar_All.failwith (Prims.strcat "extraction: unbound type var " b.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Ident.idText))
end))

# 96 "FStar.Extraction.ML.Env.fst"
let tyscheme_of_td = (fun _70_62 -> (match (_70_62) with
| (_70_59, vars, body_opt) -> begin
(match (body_opt) with
| Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some ((vars, t))
end
| _70_67 -> begin
None
end)
end))

# 101 "FStar.Extraction.ML.Env.fst"
let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme Prims.option = (fun env _70_71 -> (match (_70_71) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun _70_74 -> (match (_70_74) with
| (m, tds) -> begin
if (module_name = m) then begin
(FStar_Util.find_map tds (fun td -> (
# 105 "FStar.Extraction.ML.Env.fst"
let _70_81 = td
in (match (_70_81) with
| (n, _70_78, _70_80) -> begin
if (n = ty_name) then begin
(tyscheme_of_td td)
end else begin
None
end
end))))
end else begin
None
end
end)))
end))

# 111 "FStar.Extraction.ML.Env.fst"
let lookup_tyvar : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))

# 113 "FStar.Extraction.ML.Env.fst"
let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g fv -> (
# 114 "FStar.Extraction.ML.Env.fst"
let x = (FStar_Util.find_map g.gamma (fun _70_1 -> (match (_70_1) with
| Fv (fv', path, sc, b) when (FStar_Ident.lid_equals fv fv'.FStar_Absyn_Syntax.v) -> begin
Some ((path, sc, b))
end
| _70_94 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _159_105 = (let _159_104 = (FStar_Absyn_Print.sli fv)
in (FStar_Util.format1 "free Variable %s not found\n" _159_104))
in (FStar_All.failwith _159_105))
end
| Some (y) -> begin
y
end)))

# 122 "FStar.Extraction.ML.Env.fst"
let lookup_fv : env  ->  FStar_Absyn_Syntax.fvvar  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g fv -> (
# 123 "FStar.Extraction.ML.Env.fst"
let x = (FStar_Util.find_map g.gamma (fun _70_2 -> (match (_70_2) with
| Fv (fv', path, sc, b) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v fv'.FStar_Absyn_Syntax.v) -> begin
Some ((path, sc, b))
end
| _70_109 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _159_113 = (let _159_112 = (FStar_Range.string_of_range fv.FStar_Absyn_Syntax.p)
in (let _159_111 = (FStar_Absyn_Print.sli fv.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" _159_112 _159_111)))
in (FStar_All.failwith _159_113))
end
| Some (y) -> begin
y
end)))

# 130 "FStar.Extraction.ML.Env.fst"
let lookup_bv : env  ->  FStar_Absyn_Syntax.bvvar  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g bv -> (
# 131 "FStar.Extraction.ML.Env.fst"
let x = (FStar_Util.find_map g.gamma (fun _70_3 -> (match (_70_3) with
| Bv (bv', id, sc, f) when (FStar_Absyn_Util.bvar_eq bv bv') -> begin
Some ((id, sc, f))
end
| _70_124 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _159_121 = (let _159_120 = (FStar_Range.string_of_range bv.FStar_Absyn_Syntax.p)
in (let _159_119 = (FStar_Absyn_Print.strBvd bv.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" _159_120 _159_119)))
in (FStar_All.failwith _159_121))
end
| Some (y) -> begin
y
end)))

# 139 "FStar.Extraction.ML.Env.fst"
let lookup : env  ->  (FStar_Absyn_Syntax.bvvar, FStar_Absyn_Syntax.fvvar) FStar_Util.either  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g x -> (match (x) with
| FStar_Util.Inl (x) -> begin
(lookup_bv g x)
end
| FStar_Util.Inr (x) -> begin
(lookup_fv g x)
end))

# 144 "FStar.Extraction.ML.Env.fst"
let lookup_var = (fun g e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let _159_128 = (lookup g (FStar_Util.Inl (x)))
in (_159_128, None))
end
| FStar_Absyn_Syntax.Exp_fvar (x, b) -> begin
(let _159_129 = (lookup g (FStar_Util.Inr (x)))
in (_159_129, b))
end
| _70_144 -> begin
(FStar_All.failwith "impossible")
end))

# 158 "FStar.Extraction.ML.Env.fst"
let extend_ty : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty Prims.option  ->  env = (fun g a mapped_to -> (
# 159 "FStar.Extraction.ML.Env.fst"
let ml_a = (btvar_as_mltyvar a)
in (
# 160 "FStar.Extraction.ML.Env.fst"
let mapped_to = (match (mapped_to) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Var (ml_a)
end
| Some (t) -> begin
t
end)
in (
# 163 "FStar.Extraction.ML.Env.fst"
let gamma = (Ty ((a, ml_a, mapped_to)))::g.gamma
in (
# 164 "FStar.Extraction.ML.Env.fst"
let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_typ ((a.FStar_Absyn_Syntax.v, a.FStar_Absyn_Syntax.sort))))
in (
# 165 "FStar.Extraction.ML.Env.fst"
let _70_155 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _70_155.tydefs; currentModule = _70_155.currentModule}))))))

# 167 "FStar.Extraction.ML.Env.fst"
let extend_bv : env  ->  FStar_Absyn_Syntax.bvvar  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec mk_unit -> (
# 168 "FStar.Extraction.ML.Env.fst"
let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _70_167 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (
# 171 "FStar.Extraction.ML.Env.fst"
let mlx = FStar_Extraction_ML_Syntax.MLE_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v))
in (
# 172 "FStar.Extraction.ML.Env.fst"
let mlx = if mk_unit then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App (((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mlx), (FStar_Extraction_ML_Syntax.ml_unit)::[]))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
end
end
in (
# 177 "FStar.Extraction.ML.Env.fst"
let gamma = (Bv ((x, mlx, t_x, is_rec)))::g.gamma
in (
# 178 "FStar.Extraction.ML.Env.fst"
let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))))
in (
# 179 "FStar.Extraction.ML.Env.fst"
let _70_173 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _70_173.tydefs; currentModule = _70_173.currentModule})))))))

# 181 "FStar.Extraction.ML.Env.fst"
let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(let _159_151 = (mltyFvars t1)
in (let _159_150 = (mltyFvars t2)
in (FStar_List.append _159_151 _159_150)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(FStar_List.collect mltyFvars args)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(FStar_List.collect mltyFvars ts)
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
[]
end))

# 189 "FStar.Extraction.ML.Env.fst"
let rec subsetMlidents : FStar_Extraction_ML_Syntax.mlident Prims.list  ->  FStar_Extraction_ML_Syntax.mlident Prims.list  ->  Prims.bool = (fun la lb -> (match (la) with
| h::tla -> begin
((FStar_List.contains h lb) && (subsetMlidents tla lb))
end
| [] -> begin
true
end))

# 194 "FStar.Extraction.ML.Env.fst"
let tySchemeIsClosed : FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool = (fun tys -> (let _159_158 = (mltyFvars (Prims.snd tys))
in (subsetMlidents _159_158 (Prims.fst tys))))

# 197 "FStar.Extraction.ML.Env.fst"
let extend_fv' : env  ->  FStar_Absyn_Syntax.fvvar  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x y t_x add_unit is_rec -> if (tySchemeIsClosed t_x) then begin
(
# 200 "FStar.Extraction.ML.Env.fst"
let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _70_207 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (
# 203 "FStar.Extraction.ML.Env.fst"
let mly = FStar_Extraction_ML_Syntax.MLE_Name (y)
in (
# 204 "FStar.Extraction.ML.Env.fst"
let mly = if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App (((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly), (FStar_Extraction_ML_Syntax.ml_unit)::[]))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end
in (
# 205 "FStar.Extraction.ML.Env.fst"
let gamma = (Fv ((x, mly, t_x, is_rec)))::g.gamma
in (
# 206 "FStar.Extraction.ML.Env.fst"
let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_lid ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))))
in (
# 207 "FStar.Extraction.ML.Env.fst"
let _70_213 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _70_213.tydefs; currentModule = _70_213.currentModule}))))))
end else begin
(FStar_All.failwith "freevars found")
end)

# 211 "FStar.Extraction.ML.Env.fst"
let extend_fv : env  ->  FStar_Absyn_Syntax.fvvar  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec -> (
# 212 "FStar.Extraction.ML.Env.fst"
let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Absyn_Syntax.v)
in (extend_fv' g x mlp t_x add_unit is_rec)))

# 219 "FStar.Extraction.ML.Env.fst"
let extend_lb : env  ->  FStar_Absyn_Syntax.lbname  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g l t t_x add_unit is_rec -> (match (l) with
| FStar_Util.Inl (x) -> begin
(let _159_193 = (extend_bv g (FStar_Absyn_Util.bvd_to_bvar_s x t) t_x add_unit is_rec false)
in (_159_193, (FStar_Extraction_ML_Syntax.as_mlident x)))
end
| FStar_Util.Inr (f) -> begin
(
# 224 "FStar.Extraction.ML.Env.fst"
let _70_233 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f)
in (match (_70_233) with
| (p, y) -> begin
(let _159_194 = (extend_fv' g (FStar_Absyn_Util.fvvar_of_lid f t) (p, y) t_x add_unit is_rec)
in (_159_194, (y, 0)))
end))
end))

# 227 "FStar.Extraction.ML.Env.fst"
let extend_tydef : env  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g td -> (
# 228 "FStar.Extraction.ML.Env.fst"
let m = (FStar_List.append (Prims.fst g.currentModule) (((Prims.snd g.currentModule))::[]))
in (
# 229 "FStar.Extraction.ML.Env.fst"
let _70_237 = g
in {tcenv = _70_237.tcenv; gamma = _70_237.gamma; tydefs = ((m, td))::g.tydefs; currentModule = _70_237.currentModule})))

# 232 "FStar.Extraction.ML.Env.fst"
let emptyMlPath : (Prims.string Prims.list * Prims.string) = ([], "")

# 234 "FStar.Extraction.ML.Env.fst"
let mkContext : FStar_Tc_Env.env  ->  env = (fun e -> (
# 235 "FStar.Extraction.ML.Env.fst"
let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (
# 236 "FStar.Extraction.ML.Env.fst"
let a = ("\'a", (- (1)))
in (
# 237 "FStar.Extraction.ML.Env.fst"
let failwith_ty = ((a)::[], FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.MLTY_Named (([], (("Prims")::[], "string"))), FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.MLTY_Var (a))))
in (let _159_201 = (extend_lb env (FStar_Util.Inr (FStar_Absyn_Const.failwith_lid)) FStar_Absyn_Syntax.tun failwith_ty false false)
in (FStar_All.pipe_right _159_201 Prims.fst))))))




