
open Prims
# 28 "FStar.Syntax.Syntax.fst"
exception Err of (Prims.string)

# 28 "FStar.Syntax.Syntax.fst"
let is_Err = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.Syntax.Syntax.fst"
let ___Err____0 = (fun projectee -> (match (projectee) with
| Err (_33_7) -> begin
_33_7
end))

# 29 "FStar.Syntax.Syntax.fst"
exception Error of ((Prims.string * FStar_Range.range))

# 29 "FStar.Syntax.Syntax.fst"
let is_Error = (fun _discr_ -> (match (_discr_) with
| Error (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.Syntax.Syntax.fst"
let ___Error____0 = (fun projectee -> (match (projectee) with
| Error (_33_9) -> begin
_33_9
end))

# 30 "FStar.Syntax.Syntax.fst"
exception Warning of ((Prims.string * FStar_Range.range))

# 30 "FStar.Syntax.Syntax.fst"
let is_Warning = (fun _discr_ -> (match (_discr_) with
| Warning (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.Syntax.Syntax.fst"
let ___Warning____0 = (fun projectee -> (match (projectee) with
| Warning (_33_11) -> begin
_33_11
end))

# 33 "FStar.Syntax.Syntax.fst"
type ('a, 't) withinfo_t =
{v : 'a; ty : 't; p : FStar_Range.range}

# 33 "FStar.Syntax.Syntax.fst"
let is_Mkwithinfo_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkwithinfo_t"))))

# 40 "FStar.Syntax.Syntax.fst"
type 't var =
(FStar_Ident.lident, 't) withinfo_t

# 41 "FStar.Syntax.Syntax.fst"
type fieldname =
FStar_Ident.lident

# 43 "FStar.Syntax.Syntax.fst"
type sconst =
FStar_Const.sconst

# 45 "FStar.Syntax.Syntax.fst"
type pragma =
| SetOptions of Prims.string
| ResetOptions of Prims.string Prims.option

# 46 "FStar.Syntax.Syntax.fst"
let is_SetOptions = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 47 "FStar.Syntax.Syntax.fst"
let is_ResetOptions = (fun _discr_ -> (match (_discr_) with
| ResetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.Syntax.Syntax.fst"
let ___SetOptions____0 = (fun projectee -> (match (projectee) with
| SetOptions (_33_21) -> begin
_33_21
end))

# 47 "FStar.Syntax.Syntax.fst"
let ___ResetOptions____0 = (fun projectee -> (match (projectee) with
| ResetOptions (_33_24) -> begin
_33_24
end))

# 49 "FStar.Syntax.Syntax.fst"
type 'a memo =
'a Prims.option FStar_ST.ref

# 51 "FStar.Syntax.Syntax.fst"
type arg_qualifier =
| Implicit of Prims.bool
| Equality

# 52 "FStar.Syntax.Syntax.fst"
let is_Implicit = (fun _discr_ -> (match (_discr_) with
| Implicit (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "FStar.Syntax.Syntax.fst"
let is_Equality = (fun _discr_ -> (match (_discr_) with
| Equality (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.Syntax.Syntax.fst"
let ___Implicit____0 = (fun projectee -> (match (projectee) with
| Implicit (_33_28) -> begin
_33_28
end))

# 54 "FStar.Syntax.Syntax.fst"
type aqual =
arg_qualifier Prims.option

# 55 "FStar.Syntax.Syntax.fst"
type universe =
| U_zero
| U_succ of universe
| U_max of universe Prims.list
| U_bvar of Prims.int
| U_name of univ_name
| U_unif of universe Prims.option FStar_Unionfind.uvar
| U_unknown 
 and univ_name =
FStar_Ident.ident

# 56 "FStar.Syntax.Syntax.fst"
let is_U_zero = (fun _discr_ -> (match (_discr_) with
| U_zero (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.Syntax.Syntax.fst"
let is_U_succ = (fun _discr_ -> (match (_discr_) with
| U_succ (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "FStar.Syntax.Syntax.fst"
let is_U_max = (fun _discr_ -> (match (_discr_) with
| U_max (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "FStar.Syntax.Syntax.fst"
let is_U_bvar = (fun _discr_ -> (match (_discr_) with
| U_bvar (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "FStar.Syntax.Syntax.fst"
let is_U_name = (fun _discr_ -> (match (_discr_) with
| U_name (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "FStar.Syntax.Syntax.fst"
let is_U_unif = (fun _discr_ -> (match (_discr_) with
| U_unif (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.Syntax.Syntax.fst"
let is_U_unknown = (fun _discr_ -> (match (_discr_) with
| U_unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.Syntax.Syntax.fst"
let ___U_succ____0 = (fun projectee -> (match (projectee) with
| U_succ (_33_31) -> begin
_33_31
end))

# 58 "FStar.Syntax.Syntax.fst"
let ___U_max____0 = (fun projectee -> (match (projectee) with
| U_max (_33_34) -> begin
_33_34
end))

# 59 "FStar.Syntax.Syntax.fst"
let ___U_bvar____0 = (fun projectee -> (match (projectee) with
| U_bvar (_33_37) -> begin
_33_37
end))

# 60 "FStar.Syntax.Syntax.fst"
let ___U_name____0 = (fun projectee -> (match (projectee) with
| U_name (_33_40) -> begin
_33_40
end))

# 61 "FStar.Syntax.Syntax.fst"
let ___U_unif____0 = (fun projectee -> (match (projectee) with
| U_unif (_33_43) -> begin
_33_43
end))

# 65 "FStar.Syntax.Syntax.fst"
type universe_uvar =
universe Prims.option FStar_Unionfind.uvar

# 66 "FStar.Syntax.Syntax.fst"
type univ_names =
univ_name Prims.list

# 67 "FStar.Syntax.Syntax.fst"
type universes =
universe Prims.list

# 68 "FStar.Syntax.Syntax.fst"
type delta_depth =
| Delta_constant
| Delta_unfoldable of Prims.int
| Delta_equational
| Delta_abstract of delta_depth

# 69 "FStar.Syntax.Syntax.fst"
let is_Delta_constant = (fun _discr_ -> (match (_discr_) with
| Delta_constant (_) -> begin
true
end
| _ -> begin
false
end))

# 70 "FStar.Syntax.Syntax.fst"
let is_Delta_unfoldable = (fun _discr_ -> (match (_discr_) with
| Delta_unfoldable (_) -> begin
true
end
| _ -> begin
false
end))

# 71 "FStar.Syntax.Syntax.fst"
let is_Delta_equational = (fun _discr_ -> (match (_discr_) with
| Delta_equational (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.Syntax.Syntax.fst"
let is_Delta_abstract = (fun _discr_ -> (match (_discr_) with
| Delta_abstract (_) -> begin
true
end
| _ -> begin
false
end))

# 70 "FStar.Syntax.Syntax.fst"
let ___Delta_unfoldable____0 = (fun projectee -> (match (projectee) with
| Delta_unfoldable (_33_46) -> begin
_33_46
end))

# 72 "FStar.Syntax.Syntax.fst"
let ___Delta_abstract____0 = (fun projectee -> (match (projectee) with
| Delta_abstract (_33_49) -> begin
_33_49
end))

# 73 "FStar.Syntax.Syntax.fst"
type term' =
| Tm_bvar of bv
| Tm_name of bv
| Tm_fvar of fv
| Tm_uinst of (term * universes)
| Tm_constant of sconst
| Tm_type of universe
| Tm_abs of (binders * term * (lcomp, FStar_Ident.lident) FStar_Util.either Prims.option)
| Tm_arrow of (binders * comp)
| Tm_refine of (bv * term)
| Tm_app of (term * args)
| Tm_match of (term * branch Prims.list)
| Tm_ascribed of (term * (term, comp) FStar_Util.either * FStar_Ident.lident Prims.option)
| Tm_let of (letbindings * term)
| Tm_uvar of (uvar * term)
| Tm_delayed of (((term * subst_ts), Prims.unit  ->  term) FStar_Util.either * term memo)
| Tm_meta of (term * metadata)
| Tm_unknown 
 and pat' =
| Pat_constant of sconst
| Pat_disj of pat Prims.list
| Pat_cons of (fv * (pat * Prims.bool) Prims.list)
| Pat_var of bv
| Pat_wild of bv
| Pat_dot_term of (bv * term) 
 and letbinding =
{lbname : lbname; lbunivs : univ_name Prims.list; lbtyp : typ; lbeff : FStar_Ident.lident; lbdef : term} 
 and comp_typ =
{effect_name : FStar_Ident.lident; result_typ : typ; effect_args : args; flags : cflags Prims.list} 
 and comp' =
| Total of typ
| GTotal of typ
| Comp of comp_typ 
 and cflags =
| TOTAL
| MLEFFECT
| RETURN
| PARTIAL_RETURN
| SOMETRIVIAL
| LEMMA
| DECREASES of term 
 and metadata =
| Meta_pattern of args Prims.list
| Meta_named of FStar_Ident.lident
| Meta_labeled of (Prims.string * FStar_Range.range * Prims.bool)
| Meta_desugared of meta_source_info 
 and 'a uvar_basis =
| Uvar
| Fixed of 'a 
 and meta_source_info =
| Data_app
| Sequence
| Primop
| Masked_effect
| Meta_smt_pat 
 and fv_qual =
| Data_ctor
| Record_projector of FStar_Ident.lident
| Record_ctor of (FStar_Ident.lident * fieldname Prims.list) 
 and subst_elt =
| DB of (Prims.int * bv)
| NM of (bv * Prims.int)
| NT of (bv * term)
| UN of (Prims.int * universe)
| UD of (univ_name * Prims.int) 
 and ('a, 'b) syntax =
{n : 'a; tk : 'b memo; pos : FStar_Range.range; vars : free_vars memo} 
 and bv =
{ppname : FStar_Ident.ident; index : Prims.int; sort : term} 
 and fv =
{fv_name : term var; fv_delta : delta_depth; fv_qual : fv_qual Prims.option} 
 and free_vars =
{free_names : bv FStar_Util.set; free_uvars : uvars; free_univs : universe_uvar FStar_Util.set} 
 and lcomp =
{eff_name : FStar_Ident.lident; res_typ : typ; cflags : cflags Prims.list; comp : Prims.unit  ->  comp} 
 and branch =
(pat * term Prims.option * term) 
 and term =
(term', term') syntax 
 and typ =
term 
 and pat =
(pat', term') withinfo_t 
 and comp =
(comp', Prims.unit) syntax 
 and arg =
(term * aqual) 
 and args =
arg Prims.list 
 and binder =
(bv * aqual) 
 and binders =
binder Prims.list 
 and uvar =
term uvar_basis FStar_Unionfind.uvar 
 and lbname =
(bv, fv) FStar_Util.either 
 and letbindings =
(Prims.bool * letbinding Prims.list) 
 and subst_ts =
subst_elt Prims.list Prims.list 
 and freenames =
bv FStar_Util.set 
 and uvars =
(uvar * typ) FStar_Util.set

# 74 "FStar.Syntax.Syntax.fst"
let is_Tm_bvar = (fun _discr_ -> (match (_discr_) with
| Tm_bvar (_) -> begin
true
end
| _ -> begin
false
end))

# 75 "FStar.Syntax.Syntax.fst"
let is_Tm_name = (fun _discr_ -> (match (_discr_) with
| Tm_name (_) -> begin
true
end
| _ -> begin
false
end))

# 76 "FStar.Syntax.Syntax.fst"
let is_Tm_fvar = (fun _discr_ -> (match (_discr_) with
| Tm_fvar (_) -> begin
true
end
| _ -> begin
false
end))

# 77 "FStar.Syntax.Syntax.fst"
let is_Tm_uinst = (fun _discr_ -> (match (_discr_) with
| Tm_uinst (_) -> begin
true
end
| _ -> begin
false
end))

# 78 "FStar.Syntax.Syntax.fst"
let is_Tm_constant = (fun _discr_ -> (match (_discr_) with
| Tm_constant (_) -> begin
true
end
| _ -> begin
false
end))

# 79 "FStar.Syntax.Syntax.fst"
let is_Tm_type = (fun _discr_ -> (match (_discr_) with
| Tm_type (_) -> begin
true
end
| _ -> begin
false
end))

# 80 "FStar.Syntax.Syntax.fst"
let is_Tm_abs = (fun _discr_ -> (match (_discr_) with
| Tm_abs (_) -> begin
true
end
| _ -> begin
false
end))

# 81 "FStar.Syntax.Syntax.fst"
let is_Tm_arrow = (fun _discr_ -> (match (_discr_) with
| Tm_arrow (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "FStar.Syntax.Syntax.fst"
let is_Tm_refine = (fun _discr_ -> (match (_discr_) with
| Tm_refine (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "FStar.Syntax.Syntax.fst"
let is_Tm_app = (fun _discr_ -> (match (_discr_) with
| Tm_app (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "FStar.Syntax.Syntax.fst"
let is_Tm_match = (fun _discr_ -> (match (_discr_) with
| Tm_match (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "FStar.Syntax.Syntax.fst"
let is_Tm_ascribed = (fun _discr_ -> (match (_discr_) with
| Tm_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.Syntax.Syntax.fst"
let is_Tm_let = (fun _discr_ -> (match (_discr_) with
| Tm_let (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.Syntax.Syntax.fst"
let is_Tm_uvar = (fun _discr_ -> (match (_discr_) with
| Tm_uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "FStar.Syntax.Syntax.fst"
let is_Tm_delayed = (fun _discr_ -> (match (_discr_) with
| Tm_delayed (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "FStar.Syntax.Syntax.fst"
let is_Tm_meta = (fun _discr_ -> (match (_discr_) with
| Tm_meta (_) -> begin
true
end
| _ -> begin
false
end))

# 91 "FStar.Syntax.Syntax.fst"
let is_Tm_unknown = (fun _discr_ -> (match (_discr_) with
| Tm_unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 94 "FStar.Syntax.Syntax.fst"
let is_Pat_constant = (fun _discr_ -> (match (_discr_) with
| Pat_constant (_) -> begin
true
end
| _ -> begin
false
end))

# 95 "FStar.Syntax.Syntax.fst"
let is_Pat_disj = (fun _discr_ -> (match (_discr_) with
| Pat_disj (_) -> begin
true
end
| _ -> begin
false
end))

# 96 "FStar.Syntax.Syntax.fst"
let is_Pat_cons = (fun _discr_ -> (match (_discr_) with
| Pat_cons (_) -> begin
true
end
| _ -> begin
false
end))

# 97 "FStar.Syntax.Syntax.fst"
let is_Pat_var = (fun _discr_ -> (match (_discr_) with
| Pat_var (_) -> begin
true
end
| _ -> begin
false
end))

# 98 "FStar.Syntax.Syntax.fst"
let is_Pat_wild = (fun _discr_ -> (match (_discr_) with
| Pat_wild (_) -> begin
true
end
| _ -> begin
false
end))

# 99 "FStar.Syntax.Syntax.fst"
let is_Pat_dot_term = (fun _discr_ -> (match (_discr_) with
| Pat_dot_term (_) -> begin
true
end
| _ -> begin
false
end))

# 100 "FStar.Syntax.Syntax.fst"
let is_Mkletbinding : letbinding  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkletbinding"))))

# 107 "FStar.Syntax.Syntax.fst"
let is_Mkcomp_typ : comp_typ  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcomp_typ"))))

# 114 "FStar.Syntax.Syntax.fst"
let is_Total = (fun _discr_ -> (match (_discr_) with
| Total (_) -> begin
true
end
| _ -> begin
false
end))

# 115 "FStar.Syntax.Syntax.fst"
let is_GTotal = (fun _discr_ -> (match (_discr_) with
| GTotal (_) -> begin
true
end
| _ -> begin
false
end))

# 116 "FStar.Syntax.Syntax.fst"
let is_Comp = (fun _discr_ -> (match (_discr_) with
| Comp (_) -> begin
true
end
| _ -> begin
false
end))

# 126 "FStar.Syntax.Syntax.fst"
let is_TOTAL = (fun _discr_ -> (match (_discr_) with
| TOTAL (_) -> begin
true
end
| _ -> begin
false
end))

# 127 "FStar.Syntax.Syntax.fst"
let is_MLEFFECT = (fun _discr_ -> (match (_discr_) with
| MLEFFECT (_) -> begin
true
end
| _ -> begin
false
end))

# 128 "FStar.Syntax.Syntax.fst"
let is_RETURN = (fun _discr_ -> (match (_discr_) with
| RETURN (_) -> begin
true
end
| _ -> begin
false
end))

# 129 "FStar.Syntax.Syntax.fst"
let is_PARTIAL_RETURN = (fun _discr_ -> (match (_discr_) with
| PARTIAL_RETURN (_) -> begin
true
end
| _ -> begin
false
end))

# 130 "FStar.Syntax.Syntax.fst"
let is_SOMETRIVIAL = (fun _discr_ -> (match (_discr_) with
| SOMETRIVIAL (_) -> begin
true
end
| _ -> begin
false
end))

# 131 "FStar.Syntax.Syntax.fst"
let is_LEMMA = (fun _discr_ -> (match (_discr_) with
| LEMMA (_) -> begin
true
end
| _ -> begin
false
end))

# 132 "FStar.Syntax.Syntax.fst"
let is_DECREASES = (fun _discr_ -> (match (_discr_) with
| DECREASES (_) -> begin
true
end
| _ -> begin
false
end))

# 135 "FStar.Syntax.Syntax.fst"
let is_Meta_pattern = (fun _discr_ -> (match (_discr_) with
| Meta_pattern (_) -> begin
true
end
| _ -> begin
false
end))

# 136 "FStar.Syntax.Syntax.fst"
let is_Meta_named = (fun _discr_ -> (match (_discr_) with
| Meta_named (_) -> begin
true
end
| _ -> begin
false
end))

# 137 "FStar.Syntax.Syntax.fst"
let is_Meta_labeled = (fun _discr_ -> (match (_discr_) with
| Meta_labeled (_) -> begin
true
end
| _ -> begin
false
end))

# 138 "FStar.Syntax.Syntax.fst"
let is_Meta_desugared = (fun _discr_ -> (match (_discr_) with
| Meta_desugared (_) -> begin
true
end
| _ -> begin
false
end))

# 140 "FStar.Syntax.Syntax.fst"
let is_Uvar = (fun _ _discr_ -> (match (_discr_) with
| Uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 141 "FStar.Syntax.Syntax.fst"
let is_Fixed = (fun _ _discr_ -> (match (_discr_) with
| Fixed (_) -> begin
true
end
| _ -> begin
false
end))

# 143 "FStar.Syntax.Syntax.fst"
let is_Data_app = (fun _discr_ -> (match (_discr_) with
| Data_app (_) -> begin
true
end
| _ -> begin
false
end))

# 144 "FStar.Syntax.Syntax.fst"
let is_Sequence = (fun _discr_ -> (match (_discr_) with
| Sequence (_) -> begin
true
end
| _ -> begin
false
end))

# 145 "FStar.Syntax.Syntax.fst"
let is_Primop = (fun _discr_ -> (match (_discr_) with
| Primop (_) -> begin
true
end
| _ -> begin
false
end))

# 146 "FStar.Syntax.Syntax.fst"
let is_Masked_effect = (fun _discr_ -> (match (_discr_) with
| Masked_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 147 "FStar.Syntax.Syntax.fst"
let is_Meta_smt_pat = (fun _discr_ -> (match (_discr_) with
| Meta_smt_pat (_) -> begin
true
end
| _ -> begin
false
end))

# 149 "FStar.Syntax.Syntax.fst"
let is_Data_ctor = (fun _discr_ -> (match (_discr_) with
| Data_ctor (_) -> begin
true
end
| _ -> begin
false
end))

# 150 "FStar.Syntax.Syntax.fst"
let is_Record_projector = (fun _discr_ -> (match (_discr_) with
| Record_projector (_) -> begin
true
end
| _ -> begin
false
end))

# 151 "FStar.Syntax.Syntax.fst"
let is_Record_ctor = (fun _discr_ -> (match (_discr_) with
| Record_ctor (_) -> begin
true
end
| _ -> begin
false
end))

# 156 "FStar.Syntax.Syntax.fst"
let is_DB = (fun _discr_ -> (match (_discr_) with
| DB (_) -> begin
true
end
| _ -> begin
false
end))

# 157 "FStar.Syntax.Syntax.fst"
let is_NM = (fun _discr_ -> (match (_discr_) with
| NM (_) -> begin
true
end
| _ -> begin
false
end))

# 158 "FStar.Syntax.Syntax.fst"
let is_NT = (fun _discr_ -> (match (_discr_) with
| NT (_) -> begin
true
end
| _ -> begin
false
end))

# 159 "FStar.Syntax.Syntax.fst"
let is_UN = (fun _discr_ -> (match (_discr_) with
| UN (_) -> begin
true
end
| _ -> begin
false
end))

# 160 "FStar.Syntax.Syntax.fst"
let is_UD = (fun _discr_ -> (match (_discr_) with
| UD (_) -> begin
true
end
| _ -> begin
false
end))

# 163 "FStar.Syntax.Syntax.fst"
let is_Mksyntax = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksyntax"))))

# 169 "FStar.Syntax.Syntax.fst"
let is_Mkbv : bv  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbv"))))

# 174 "FStar.Syntax.Syntax.fst"
let is_Mkfv : fv  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfv"))))

# 179 "FStar.Syntax.Syntax.fst"
let is_Mkfree_vars : free_vars  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfree_vars"))))

# 184 "FStar.Syntax.Syntax.fst"
let is_Mklcomp : lcomp  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklcomp"))))

# 74 "FStar.Syntax.Syntax.fst"
let ___Tm_bvar____0 = (fun projectee -> (match (projectee) with
| Tm_bvar (_33_81) -> begin
_33_81
end))

# 75 "FStar.Syntax.Syntax.fst"
let ___Tm_name____0 = (fun projectee -> (match (projectee) with
| Tm_name (_33_84) -> begin
_33_84
end))

# 76 "FStar.Syntax.Syntax.fst"
let ___Tm_fvar____0 = (fun projectee -> (match (projectee) with
| Tm_fvar (_33_87) -> begin
_33_87
end))

# 77 "FStar.Syntax.Syntax.fst"
let ___Tm_uinst____0 = (fun projectee -> (match (projectee) with
| Tm_uinst (_33_90) -> begin
_33_90
end))

# 78 "FStar.Syntax.Syntax.fst"
let ___Tm_constant____0 = (fun projectee -> (match (projectee) with
| Tm_constant (_33_93) -> begin
_33_93
end))

# 79 "FStar.Syntax.Syntax.fst"
let ___Tm_type____0 = (fun projectee -> (match (projectee) with
| Tm_type (_33_96) -> begin
_33_96
end))

# 80 "FStar.Syntax.Syntax.fst"
let ___Tm_abs____0 = (fun projectee -> (match (projectee) with
| Tm_abs (_33_99) -> begin
_33_99
end))

# 81 "FStar.Syntax.Syntax.fst"
let ___Tm_arrow____0 = (fun projectee -> (match (projectee) with
| Tm_arrow (_33_102) -> begin
_33_102
end))

# 82 "FStar.Syntax.Syntax.fst"
let ___Tm_refine____0 = (fun projectee -> (match (projectee) with
| Tm_refine (_33_105) -> begin
_33_105
end))

# 83 "FStar.Syntax.Syntax.fst"
let ___Tm_app____0 = (fun projectee -> (match (projectee) with
| Tm_app (_33_108) -> begin
_33_108
end))

# 84 "FStar.Syntax.Syntax.fst"
let ___Tm_match____0 = (fun projectee -> (match (projectee) with
| Tm_match (_33_111) -> begin
_33_111
end))

# 85 "FStar.Syntax.Syntax.fst"
let ___Tm_ascribed____0 = (fun projectee -> (match (projectee) with
| Tm_ascribed (_33_114) -> begin
_33_114
end))

# 86 "FStar.Syntax.Syntax.fst"
let ___Tm_let____0 = (fun projectee -> (match (projectee) with
| Tm_let (_33_117) -> begin
_33_117
end))

# 87 "FStar.Syntax.Syntax.fst"
let ___Tm_uvar____0 = (fun projectee -> (match (projectee) with
| Tm_uvar (_33_120) -> begin
_33_120
end))

# 88 "FStar.Syntax.Syntax.fst"
let ___Tm_delayed____0 = (fun projectee -> (match (projectee) with
| Tm_delayed (_33_123) -> begin
_33_123
end))

# 90 "FStar.Syntax.Syntax.fst"
let ___Tm_meta____0 = (fun projectee -> (match (projectee) with
| Tm_meta (_33_126) -> begin
_33_126
end))

# 94 "FStar.Syntax.Syntax.fst"
let ___Pat_constant____0 = (fun projectee -> (match (projectee) with
| Pat_constant (_33_129) -> begin
_33_129
end))

# 95 "FStar.Syntax.Syntax.fst"
let ___Pat_disj____0 = (fun projectee -> (match (projectee) with
| Pat_disj (_33_132) -> begin
_33_132
end))

# 96 "FStar.Syntax.Syntax.fst"
let ___Pat_cons____0 = (fun projectee -> (match (projectee) with
| Pat_cons (_33_135) -> begin
_33_135
end))

# 97 "FStar.Syntax.Syntax.fst"
let ___Pat_var____0 = (fun projectee -> (match (projectee) with
| Pat_var (_33_138) -> begin
_33_138
end))

# 98 "FStar.Syntax.Syntax.fst"
let ___Pat_wild____0 = (fun projectee -> (match (projectee) with
| Pat_wild (_33_141) -> begin
_33_141
end))

# 99 "FStar.Syntax.Syntax.fst"
let ___Pat_dot_term____0 = (fun projectee -> (match (projectee) with
| Pat_dot_term (_33_144) -> begin
_33_144
end))

# 114 "FStar.Syntax.Syntax.fst"
let ___Total____0 = (fun projectee -> (match (projectee) with
| Total (_33_149) -> begin
_33_149
end))

# 115 "FStar.Syntax.Syntax.fst"
let ___GTotal____0 = (fun projectee -> (match (projectee) with
| GTotal (_33_152) -> begin
_33_152
end))

# 116 "FStar.Syntax.Syntax.fst"
let ___Comp____0 = (fun projectee -> (match (projectee) with
| Comp (_33_155) -> begin
_33_155
end))

# 132 "FStar.Syntax.Syntax.fst"
let ___DECREASES____0 = (fun projectee -> (match (projectee) with
| DECREASES (_33_158) -> begin
_33_158
end))

# 135 "FStar.Syntax.Syntax.fst"
let ___Meta_pattern____0 = (fun projectee -> (match (projectee) with
| Meta_pattern (_33_161) -> begin
_33_161
end))

# 136 "FStar.Syntax.Syntax.fst"
let ___Meta_named____0 = (fun projectee -> (match (projectee) with
| Meta_named (_33_164) -> begin
_33_164
end))

# 137 "FStar.Syntax.Syntax.fst"
let ___Meta_labeled____0 = (fun projectee -> (match (projectee) with
| Meta_labeled (_33_167) -> begin
_33_167
end))

# 138 "FStar.Syntax.Syntax.fst"
let ___Meta_desugared____0 = (fun projectee -> (match (projectee) with
| Meta_desugared (_33_170) -> begin
_33_170
end))

# 141 "FStar.Syntax.Syntax.fst"
let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_33_173) -> begin
_33_173
end))

# 150 "FStar.Syntax.Syntax.fst"
let ___Record_projector____0 = (fun projectee -> (match (projectee) with
| Record_projector (_33_176) -> begin
_33_176
end))

# 151 "FStar.Syntax.Syntax.fst"
let ___Record_ctor____0 = (fun projectee -> (match (projectee) with
| Record_ctor (_33_179) -> begin
_33_179
end))

# 156 "FStar.Syntax.Syntax.fst"
let ___DB____0 = (fun projectee -> (match (projectee) with
| DB (_33_182) -> begin
_33_182
end))

# 157 "FStar.Syntax.Syntax.fst"
let ___NM____0 = (fun projectee -> (match (projectee) with
| NM (_33_185) -> begin
_33_185
end))

# 158 "FStar.Syntax.Syntax.fst"
let ___NT____0 = (fun projectee -> (match (projectee) with
| NT (_33_188) -> begin
_33_188
end))

# 159 "FStar.Syntax.Syntax.fst"
let ___UN____0 = (fun projectee -> (match (projectee) with
| UN (_33_191) -> begin
_33_191
end))

# 160 "FStar.Syntax.Syntax.fst"
let ___UD____0 = (fun projectee -> (match (projectee) with
| UD (_33_194) -> begin
_33_194
end))

# 191 "FStar.Syntax.Syntax.fst"
type tscheme =
(univ_name Prims.list * typ)

# 193 "FStar.Syntax.Syntax.fst"
type freenames_l =
bv Prims.list

# 194 "FStar.Syntax.Syntax.fst"
type formula =
typ

# 195 "FStar.Syntax.Syntax.fst"
type formulae =
typ Prims.list

# 196 "FStar.Syntax.Syntax.fst"
type qualifier =
| Assumption
| New
| Private
| Inline
| Unfoldable
| Irreducible
| Abstract
| TotalEffect
| Logic
| Discriminator of FStar_Ident.lident
| Projector of (FStar_Ident.lident * FStar_Ident.ident)
| RecordType of fieldname Prims.list
| RecordConstructor of fieldname Prims.list
| ExceptionConstructor
| HasMaskedEffect
| Effect

# 197 "FStar.Syntax.Syntax.fst"
let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption (_) -> begin
true
end
| _ -> begin
false
end))

# 198 "FStar.Syntax.Syntax.fst"
let is_New = (fun _discr_ -> (match (_discr_) with
| New (_) -> begin
true
end
| _ -> begin
false
end))

# 199 "FStar.Syntax.Syntax.fst"
let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))

# 200 "FStar.Syntax.Syntax.fst"
let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline (_) -> begin
true
end
| _ -> begin
false
end))

# 201 "FStar.Syntax.Syntax.fst"
let is_Unfoldable = (fun _discr_ -> (match (_discr_) with
| Unfoldable (_) -> begin
true
end
| _ -> begin
false
end))

# 202 "FStar.Syntax.Syntax.fst"
let is_Irreducible = (fun _discr_ -> (match (_discr_) with
| Irreducible (_) -> begin
true
end
| _ -> begin
false
end))

# 203 "FStar.Syntax.Syntax.fst"
let is_Abstract = (fun _discr_ -> (match (_discr_) with
| Abstract (_) -> begin
true
end
| _ -> begin
false
end))

# 204 "FStar.Syntax.Syntax.fst"
let is_TotalEffect = (fun _discr_ -> (match (_discr_) with
| TotalEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 206 "FStar.Syntax.Syntax.fst"
let is_Logic = (fun _discr_ -> (match (_discr_) with
| Logic (_) -> begin
true
end
| _ -> begin
false
end))

# 207 "FStar.Syntax.Syntax.fst"
let is_Discriminator = (fun _discr_ -> (match (_discr_) with
| Discriminator (_) -> begin
true
end
| _ -> begin
false
end))

# 208 "FStar.Syntax.Syntax.fst"
let is_Projector = (fun _discr_ -> (match (_discr_) with
| Projector (_) -> begin
true
end
| _ -> begin
false
end))

# 209 "FStar.Syntax.Syntax.fst"
let is_RecordType = (fun _discr_ -> (match (_discr_) with
| RecordType (_) -> begin
true
end
| _ -> begin
false
end))

# 210 "FStar.Syntax.Syntax.fst"
let is_RecordConstructor = (fun _discr_ -> (match (_discr_) with
| RecordConstructor (_) -> begin
true
end
| _ -> begin
false
end))

# 211 "FStar.Syntax.Syntax.fst"
let is_ExceptionConstructor = (fun _discr_ -> (match (_discr_) with
| ExceptionConstructor (_) -> begin
true
end
| _ -> begin
false
end))

# 212 "FStar.Syntax.Syntax.fst"
let is_HasMaskedEffect = (fun _discr_ -> (match (_discr_) with
| HasMaskedEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 213 "FStar.Syntax.Syntax.fst"
let is_Effect = (fun _discr_ -> (match (_discr_) with
| Effect (_) -> begin
true
end
| _ -> begin
false
end))

# 207 "FStar.Syntax.Syntax.fst"
let ___Discriminator____0 = (fun projectee -> (match (projectee) with
| Discriminator (_33_202) -> begin
_33_202
end))

# 208 "FStar.Syntax.Syntax.fst"
let ___Projector____0 = (fun projectee -> (match (projectee) with
| Projector (_33_205) -> begin
_33_205
end))

# 209 "FStar.Syntax.Syntax.fst"
let ___RecordType____0 = (fun projectee -> (match (projectee) with
| RecordType (_33_208) -> begin
_33_208
end))

# 210 "FStar.Syntax.Syntax.fst"
let ___RecordConstructor____0 = (fun projectee -> (match (projectee) with
| RecordConstructor (_33_211) -> begin
_33_211
end))

# 215 "FStar.Syntax.Syntax.fst"
type tycon =
(FStar_Ident.lident * binders * typ)

# 216 "FStar.Syntax.Syntax.fst"
type monad_abbrev =
{mabbrev : FStar_Ident.lident; parms : binders; def : typ}

# 216 "FStar.Syntax.Syntax.fst"
let is_Mkmonad_abbrev : monad_abbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmonad_abbrev"))))

# 221 "FStar.Syntax.Syntax.fst"
type sub_eff =
{source : FStar_Ident.lident; target : FStar_Ident.lident; lift : tscheme}

# 221 "FStar.Syntax.Syntax.fst"
let is_Mksub_eff : sub_eff  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksub_eff"))))

# 226 "FStar.Syntax.Syntax.fst"
type eff_decl =
{qualifiers : qualifier Prims.list; mname : FStar_Ident.lident; univs : univ_names; binders : binders; signature : term; ret : tscheme; bind_wp : tscheme; bind_wlp : tscheme; if_then_else : tscheme; ite_wp : tscheme; ite_wlp : tscheme; wp_binop : tscheme; wp_as_type : tscheme; close_wp : tscheme; assert_p : tscheme; assume_p : tscheme; null_wp : tscheme; trivial : tscheme} 
 and sigelt =
| Sig_inductive_typ of (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident Prims.list * FStar_Ident.lident Prims.list * qualifier Prims.list * FStar_Range.range)
| Sig_bundle of (sigelt Prims.list * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range)
| Sig_datacon of (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range)
| Sig_declare_typ of (FStar_Ident.lident * univ_names * typ * qualifier Prims.list * FStar_Range.range)
| Sig_let of (letbindings * FStar_Range.range * FStar_Ident.lident Prims.list * qualifier Prims.list)
| Sig_main of (term * FStar_Range.range)
| Sig_assume of (FStar_Ident.lident * formula * qualifier Prims.list * FStar_Range.range)
| Sig_new_effect of (eff_decl * FStar_Range.range)
| Sig_new_effect_for_free of (eff_decl * FStar_Range.range)
| Sig_sub_effect of (sub_eff * FStar_Range.range)
| Sig_effect_abbrev of (FStar_Ident.lident * univ_names * binders * comp * qualifier Prims.list * FStar_Range.range)
| Sig_pragma of (pragma * FStar_Range.range)

# 226 "FStar.Syntax.Syntax.fst"
let is_Mkeff_decl : eff_decl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeff_decl"))))

# 247 "FStar.Syntax.Syntax.fst"
let is_Sig_inductive_typ = (fun _discr_ -> (match (_discr_) with
| Sig_inductive_typ (_) -> begin
true
end
| _ -> begin
false
end))

# 260 "FStar.Syntax.Syntax.fst"
let is_Sig_bundle = (fun _discr_ -> (match (_discr_) with
| Sig_bundle (_) -> begin
true
end
| _ -> begin
false
end))

# 264 "FStar.Syntax.Syntax.fst"
let is_Sig_datacon = (fun _discr_ -> (match (_discr_) with
| Sig_datacon (_) -> begin
true
end
| _ -> begin
false
end))

# 272 "FStar.Syntax.Syntax.fst"
let is_Sig_declare_typ = (fun _discr_ -> (match (_discr_) with
| Sig_declare_typ (_) -> begin
true
end
| _ -> begin
false
end))

# 277 "FStar.Syntax.Syntax.fst"
let is_Sig_let = (fun _discr_ -> (match (_discr_) with
| Sig_let (_) -> begin
true
end
| _ -> begin
false
end))

# 281 "FStar.Syntax.Syntax.fst"
let is_Sig_main = (fun _discr_ -> (match (_discr_) with
| Sig_main (_) -> begin
true
end
| _ -> begin
false
end))

# 283 "FStar.Syntax.Syntax.fst"
let is_Sig_assume = (fun _discr_ -> (match (_discr_) with
| Sig_assume (_) -> begin
true
end
| _ -> begin
false
end))

# 287 "FStar.Syntax.Syntax.fst"
let is_Sig_new_effect = (fun _discr_ -> (match (_discr_) with
| Sig_new_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 288 "FStar.Syntax.Syntax.fst"
let is_Sig_new_effect_for_free = (fun _discr_ -> (match (_discr_) with
| Sig_new_effect_for_free (_) -> begin
true
end
| _ -> begin
false
end))

# 290 "FStar.Syntax.Syntax.fst"
let is_Sig_sub_effect = (fun _discr_ -> (match (_discr_) with
| Sig_sub_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 291 "FStar.Syntax.Syntax.fst"
let is_Sig_effect_abbrev = (fun _discr_ -> (match (_discr_) with
| Sig_effect_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 292 "FStar.Syntax.Syntax.fst"
let is_Sig_pragma = (fun _discr_ -> (match (_discr_) with
| Sig_pragma (_) -> begin
true
end
| _ -> begin
false
end))

# 247 "FStar.Syntax.Syntax.fst"
let ___Sig_inductive_typ____0 = (fun projectee -> (match (projectee) with
| Sig_inductive_typ (_33_241) -> begin
_33_241
end))

# 260 "FStar.Syntax.Syntax.fst"
let ___Sig_bundle____0 = (fun projectee -> (match (projectee) with
| Sig_bundle (_33_244) -> begin
_33_244
end))

# 264 "FStar.Syntax.Syntax.fst"
let ___Sig_datacon____0 = (fun projectee -> (match (projectee) with
| Sig_datacon (_33_247) -> begin
_33_247
end))

# 272 "FStar.Syntax.Syntax.fst"
let ___Sig_declare_typ____0 = (fun projectee -> (match (projectee) with
| Sig_declare_typ (_33_250) -> begin
_33_250
end))

# 277 "FStar.Syntax.Syntax.fst"
let ___Sig_let____0 = (fun projectee -> (match (projectee) with
| Sig_let (_33_253) -> begin
_33_253
end))

# 281 "FStar.Syntax.Syntax.fst"
let ___Sig_main____0 = (fun projectee -> (match (projectee) with
| Sig_main (_33_256) -> begin
_33_256
end))

# 283 "FStar.Syntax.Syntax.fst"
let ___Sig_assume____0 = (fun projectee -> (match (projectee) with
| Sig_assume (_33_259) -> begin
_33_259
end))

# 287 "FStar.Syntax.Syntax.fst"
let ___Sig_new_effect____0 = (fun projectee -> (match (projectee) with
| Sig_new_effect (_33_262) -> begin
_33_262
end))

# 288 "FStar.Syntax.Syntax.fst"
let ___Sig_new_effect_for_free____0 = (fun projectee -> (match (projectee) with
| Sig_new_effect_for_free (_33_265) -> begin
_33_265
end))

# 290 "FStar.Syntax.Syntax.fst"
let ___Sig_sub_effect____0 = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_33_268) -> begin
_33_268
end))

# 291 "FStar.Syntax.Syntax.fst"
let ___Sig_effect_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_33_271) -> begin
_33_271
end))

# 292 "FStar.Syntax.Syntax.fst"
let ___Sig_pragma____0 = (fun projectee -> (match (projectee) with
| Sig_pragma (_33_274) -> begin
_33_274
end))

# 293 "FStar.Syntax.Syntax.fst"
type sigelts =
sigelt Prims.list

# 295 "FStar.Syntax.Syntax.fst"
type modul =
{name : FStar_Ident.lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool}

# 295 "FStar.Syntax.Syntax.fst"
let is_Mkmodul : modul  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmodul"))))

# 301 "FStar.Syntax.Syntax.fst"
type path =
Prims.string Prims.list

# 302 "FStar.Syntax.Syntax.fst"
type subst_t =
subst_elt Prims.list

# 303 "FStar.Syntax.Syntax.fst"
type ('a, 'b) mk_t_a =
'b Prims.option  ->  FStar_Range.range  ->  ('a, 'b) syntax

# 304 "FStar.Syntax.Syntax.fst"
type mk_t =
(term', term') mk_t_a

# 368 "FStar.Syntax.Syntax.fst"
let withinfo = (fun v s r -> {v = v; ty = s; p = r})

# 369 "FStar.Syntax.Syntax.fst"
let withsort = (fun v s -> (withinfo v s FStar_Range.dummyRange))

# 371 "FStar.Syntax.Syntax.fst"
let bv_eq : bv  ->  bv  ->  Prims.bool = (fun bv1 bv2 -> ((bv1.ppname.FStar_Ident.idText = bv2.ppname.FStar_Ident.idText) && (bv1.index = bv2.index)))

# 372 "FStar.Syntax.Syntax.fst"
let order_bv : bv  ->  bv  ->  Prims.int = (fun x y -> (
# 373 "FStar.Syntax.Syntax.fst"
let i = (FStar_String.compare x.ppname.FStar_Ident.idText y.ppname.FStar_Ident.idText)
in if (i = 0) then begin
(x.index - y.index)
end else begin
i
end))

# 378 "FStar.Syntax.Syntax.fst"
let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (fv) -> begin
(FStar_Ident.range_of_lid fv.fv_name.v)
end))

# 381 "FStar.Syntax.Syntax.fst"
let range_of_bv : bv  ->  FStar_Range.range = (fun x -> x.ppname.FStar_Ident.idRange)

# 382 "FStar.Syntax.Syntax.fst"
let set_range_of_bv : bv  ->  FStar_Range.range  ->  bv = (fun x r -> (
# 382 "FStar.Syntax.Syntax.fst"
let _33_306 = x
in {ppname = (FStar_Ident.mk_ident (x.ppname.FStar_Ident.idText, r)); index = _33_306.index; sort = _33_306.sort}))

# 389 "FStar.Syntax.Syntax.fst"
let syn = (fun p k f -> (f k p))

# 390 "FStar.Syntax.Syntax.fst"
let mk_fvs = (fun _33_311 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 391 "FStar.Syntax.Syntax.fst"
let mk_uvs = (fun _33_312 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 392 "FStar.Syntax.Syntax.fst"
let new_bv_set : Prims.unit  ->  bv FStar_Util.set = (fun _33_313 -> (match (()) with
| () -> begin
(FStar_Util.new_set order_bv (fun x -> (x.index + (FStar_Util.hashcode x.ppname.FStar_Ident.idText))))
end))

# 393 "FStar.Syntax.Syntax.fst"
let new_uv_set : Prims.unit  ->  uvars = (fun _33_315 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _33_323 _33_327 -> (match ((_33_323, _33_327)) with
| ((x, _33_322), (y, _33_326)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _33_319 -> (match (_33_319) with
| (x, _33_318) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

# 395 "FStar.Syntax.Syntax.fst"
let new_universe_uvar_set : Prims.unit  ->  universe_uvar FStar_Util.set = (fun _33_328 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) (fun x -> (FStar_Unionfind.uvar_id x)))
end))

# 398 "FStar.Syntax.Syntax.fst"
let no_names : bv FStar_Util.set = (new_bv_set ())

# 399 "FStar.Syntax.Syntax.fst"
let no_uvs : uvars = (new_uv_set ())

# 400 "FStar.Syntax.Syntax.fst"
let no_universe_uvars : universe_uvar FStar_Util.set = (new_universe_uvar_set ())

# 401 "FStar.Syntax.Syntax.fst"
let empty_free_vars : free_vars = {free_names = no_names; free_uvars = no_uvs; free_univs = no_universe_uvars}

# 406 "FStar.Syntax.Syntax.fst"
let memo_no_uvs : uvars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_uvs)))

# 407 "FStar.Syntax.Syntax.fst"
let memo_no_names : bv FStar_Util.set Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_names)))

# 408 "FStar.Syntax.Syntax.fst"
let freenames_of_list : bv Prims.list  ->  freenames = (fun l -> (FStar_List.fold_right FStar_Util.set_add l no_names))

# 409 "FStar.Syntax.Syntax.fst"
let list_of_freenames : freenames  ->  bv Prims.list = (fun fvs -> (FStar_Util.set_elements fvs))

# 412 "FStar.Syntax.Syntax.fst"
let mk = (fun t topt r -> (let _122_1219 = (FStar_Util.mk_ref topt)
in (let _122_1218 = (FStar_Util.mk_ref None)
in {n = t; tk = _122_1219; pos = r; vars = _122_1218})))

# 418 "FStar.Syntax.Syntax.fst"
let bv_to_tm : bv  ->  term = (fun bv -> (let _122_1222 = (range_of_bv bv)
in (mk (Tm_bvar (bv)) (Some (bv.sort.n)) _122_1222)))

# 419 "FStar.Syntax.Syntax.fst"
let bv_to_name : bv  ->  term = (fun bv -> (let _122_1225 = (range_of_bv bv)
in (mk (Tm_name (bv)) (Some (bv.sort.n)) _122_1225)))

# 420 "FStar.Syntax.Syntax.fst"
let mk_Tm_app : term  ->  args  ->  mk_t = (fun t1 args k p -> (match (args) with
| [] -> begin
t1
end
| _33_347 -> begin
(mk (Tm_app ((t1, args))) k p)
end))

# 424 "FStar.Syntax.Syntax.fst"
let mk_Tm_uinst : term  ->  universes  ->  term = (fun t _33_1 -> (match (_33_1) with
| [] -> begin
t
end
| us -> begin
(match (t.n) with
| Tm_fvar (_33_353) -> begin
(mk (Tm_uinst ((t, us))) None t.pos)
end
| _33_356 -> begin
(FStar_All.failwith "Unexpected universe instantiation")
end)
end))

# 431 "FStar.Syntax.Syntax.fst"
let extend_app_n : term  ->  args  ->  mk_t = (fun t args' kopt r -> (match (t.n) with
| Tm_app (head, args) -> begin
(mk_Tm_app head (FStar_List.append args args') kopt r)
end
| _33_366 -> begin
(mk_Tm_app t args' kopt r)
end))

# 434 "FStar.Syntax.Syntax.fst"
let extend_app : term  ->  arg  ->  mk_t = (fun t arg kopt r -> (extend_app_n t ((arg)::[]) kopt r))

# 435 "FStar.Syntax.Syntax.fst"
let mk_Tm_delayed : ((term * subst_ts), Prims.unit  ->  term) FStar_Util.either  ->  FStar_Range.range  ->  term = (fun lr pos -> (let _122_1260 = (let _122_1259 = (let _122_1258 = (FStar_Util.mk_ref None)
in (lr, _122_1258))
in Tm_delayed (_122_1259))
in (mk _122_1260 None pos)))

# 436 "FStar.Syntax.Syntax.fst"
let mk_Total : typ  ->  comp = (fun t -> (mk (Total (t)) None t.pos))

# 437 "FStar.Syntax.Syntax.fst"
let mk_GTotal : typ  ->  comp = (fun t -> (mk (GTotal (t)) None t.pos))

# 438 "FStar.Syntax.Syntax.fst"
let mk_Comp : comp_typ  ->  comp = (fun ct -> (mk (Comp (ct)) None ct.result_typ.pos))

# 439 "FStar.Syntax.Syntax.fst"
let mk_lb : (lbname * univ_name Prims.list * FStar_Ident.lident * typ * term)  ->  letbinding = (fun _33_381 -> (match (_33_381) with
| (x, univs, eff, t, e) -> begin
{lbname = x; lbunivs = univs; lbtyp = t; lbeff = eff; lbdef = e}
end))

# 440 "FStar.Syntax.Syntax.fst"
let mk_subst : subst_t  ->  subst_t = (fun s -> s)

# 441 "FStar.Syntax.Syntax.fst"
let extend_subst : subst_elt  ->  subst_elt Prims.list  ->  subst_elt Prims.list = (fun x s -> (x)::s)

# 442 "FStar.Syntax.Syntax.fst"
let argpos : arg  ->  FStar_Range.range = (fun x -> (Prims.fst x).pos)

# 444 "FStar.Syntax.Syntax.fst"
let tun : (term', term') syntax = (mk Tm_unknown None FStar_Range.dummyRange)

# 445 "FStar.Syntax.Syntax.fst"
let teff : (term', term') syntax = (mk (Tm_constant (FStar_Const.Const_effect)) (Some (Tm_unknown)) FStar_Range.dummyRange)

# 446 "FStar.Syntax.Syntax.fst"
let is_teff : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_constant (FStar_Const.Const_effect) -> begin
true
end
| _33_390 -> begin
false
end))

# 449 "FStar.Syntax.Syntax.fst"
let is_type : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_type (_33_393) -> begin
true
end
| _33_396 -> begin
false
end))

# 452 "FStar.Syntax.Syntax.fst"
let null_id : FStar_Ident.ident = (FStar_Ident.mk_ident ("_", FStar_Range.dummyRange))

# 453 "FStar.Syntax.Syntax.fst"
let null_bv : term  ->  bv = (fun k -> {ppname = null_id; index = 0; sort = k})

# 454 "FStar.Syntax.Syntax.fst"
let mk_binder : bv  ->  binder = (fun a -> (a, None))

# 455 "FStar.Syntax.Syntax.fst"
let null_binder : term  ->  binder = (fun t -> (let _122_1287 = (null_bv t)
in (_122_1287, None)))

# 456 "FStar.Syntax.Syntax.fst"
let imp_tag : arg_qualifier = Implicit (false)

# 457 "FStar.Syntax.Syntax.fst"
let iarg : term  ->  arg = (fun t -> (t, Some (imp_tag)))

# 458 "FStar.Syntax.Syntax.fst"
let as_arg : term  ->  arg = (fun t -> (t, None))

# 459 "FStar.Syntax.Syntax.fst"
let is_null_bv : bv  ->  Prims.bool = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))

# 460 "FStar.Syntax.Syntax.fst"
let is_null_binder : binder  ->  Prims.bool = (fun b -> (is_null_bv (Prims.fst b)))

# 462 "FStar.Syntax.Syntax.fst"
let is_top_level : letbinding Prims.list  ->  Prims.bool = (fun _33_2 -> (match (_33_2) with
| {lbname = FStar_Util.Inr (_33_416); lbunivs = _33_414; lbtyp = _33_412; lbeff = _33_410; lbdef = _33_408}::_33_406 -> begin
true
end
| _33_421 -> begin
false
end))

# 466 "FStar.Syntax.Syntax.fst"
let freenames_of_binders : binders  ->  freenames = (fun bs -> (FStar_List.fold_right (fun _33_426 out -> (match (_33_426) with
| (x, _33_425) -> begin
(FStar_Util.set_add x out)
end)) bs no_names))

# 469 "FStar.Syntax.Syntax.fst"
let binders_of_list : bv Prims.list  ->  binders = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

# 470 "FStar.Syntax.Syntax.fst"
let binders_of_freenames : freenames  ->  binders = (fun fvs -> (let _122_1307 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _122_1307 binders_of_list)))

# 471 "FStar.Syntax.Syntax.fst"
let is_implicit : aqual  ->  Prims.bool = (fun _33_3 -> (match (_33_3) with
| Some (Implicit (_33_433)) -> begin
true
end
| _33_437 -> begin
false
end))

# 472 "FStar.Syntax.Syntax.fst"
let as_implicit : Prims.bool  ->  aqual = (fun _33_4 -> (match (_33_4) with
| true -> begin
Some (imp_tag)
end
| _33_441 -> begin
None
end))

# 474 "FStar.Syntax.Syntax.fst"
let pat_bvs : pat  ->  bv Prims.list = (fun p -> (
# 475 "FStar.Syntax.Syntax.fst"
let rec aux = (fun b p -> (match (p.v) with
| (Pat_dot_term (_)) | (Pat_constant (_)) -> begin
b
end
| (Pat_wild (x)) | (Pat_var (x)) -> begin
(x)::b
end
| Pat_cons (_33_456, pats) -> begin
(FStar_List.fold_left (fun b _33_464 -> (match (_33_464) with
| (p, _33_463) -> begin
(aux b p)
end)) b pats)
end
| Pat_disj (p::_33_466) -> begin
(aux b p)
end
| Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (let _122_1320 = (aux [] p)
in (FStar_All.pipe_left FStar_List.rev _122_1320))))

# 486 "FStar.Syntax.Syntax.fst"
let gen_reset : ((Prims.unit  ->  Prims.int) * (Prims.unit  ->  Prims.unit)) = (
# 487 "FStar.Syntax.Syntax.fst"
let x = (FStar_ST.alloc 0)
in (
# 488 "FStar.Syntax.Syntax.fst"
let gen = (fun _33_474 -> (match (()) with
| () -> begin
(
# 488 "FStar.Syntax.Syntax.fst"
let _33_475 = (FStar_Util.incr x)
in (FStar_ST.read x))
end))
in (
# 489 "FStar.Syntax.Syntax.fst"
let reset = (fun _33_478 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals x 0)
end))
in (gen, reset))))

# 491 "FStar.Syntax.Syntax.fst"
let next_id : Prims.unit  ->  Prims.int = (Prims.fst gen_reset)

# 492 "FStar.Syntax.Syntax.fst"
let reset_gensym : Prims.unit  ->  Prims.unit = (Prims.snd gen_reset)

# 493 "FStar.Syntax.Syntax.fst"
let freshen_bv : bv  ->  bv = (fun bv -> (
# 493 "FStar.Syntax.Syntax.fst"
let _33_480 = bv
in (let _122_1339 = (next_id ())
in {ppname = _33_480.ppname; index = _122_1339; sort = _33_480.sort})))

# 494 "FStar.Syntax.Syntax.fst"
let range_of_ropt : FStar_Range.range Prims.option  ->  FStar_Range.range = (fun _33_5 -> (match (_33_5) with
| None -> begin
FStar_Range.dummyRange
end
| Some (r) -> begin
r
end))

# 497 "FStar.Syntax.Syntax.fst"
let gen_bv : Prims.string  ->  FStar_Range.range Prims.option  ->  typ  ->  bv = (fun s r t -> (
# 498 "FStar.Syntax.Syntax.fst"
let id = (FStar_Ident.mk_ident (s, (range_of_ropt r)))
in (let _122_1348 = (next_id ())
in {ppname = id; index = _122_1348; sort = t})))

# 500 "FStar.Syntax.Syntax.fst"
let new_bv : FStar_Range.range Prims.option  ->  typ  ->  bv = (fun ropt t -> (gen_bv FStar_Ident.reserved_prefix ropt t))

# 501 "FStar.Syntax.Syntax.fst"
let new_univ_name : FStar_Range.range Prims.option  ->  univ_name = (fun ropt -> (
# 502 "FStar.Syntax.Syntax.fst"
let id = (next_id ())
in (let _122_1356 = (let _122_1355 = (FStar_Util.string_of_int id)
in (_122_1355, (range_of_ropt ropt)))
in (FStar_Ident.mk_ident _122_1356))))

# 504 "FStar.Syntax.Syntax.fst"
let mkbv : FStar_Ident.ident  ->  Prims.int  ->  term  ->  bv = (fun x y t -> {ppname = x; index = y; sort = t})

# 505 "FStar.Syntax.Syntax.fst"
let lbname_eq : (bv, FStar_Ident.lident) FStar_Util.either  ->  (bv, FStar_Ident.lident) FStar_Util.either  ->  Prims.bool = (fun l1 l2 -> (match ((l1, l2)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bv_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| _33_510 -> begin
false
end))

# 509 "FStar.Syntax.Syntax.fst"
let fv_eq : fv  ->  fv  ->  Prims.bool = (fun fv1 fv2 -> (FStar_Ident.lid_equals fv1.fv_name.v fv2.fv_name.v))

# 510 "FStar.Syntax.Syntax.fst"
let fv_eq_lid : fv  ->  FStar_Ident.lident  ->  Prims.bool = (fun fv lid -> (FStar_Ident.lid_equals fv.fv_name.v lid))

# 511 "FStar.Syntax.Syntax.fst"
let set_bv_range : bv  ->  FStar_Range.range  ->  bv = (fun bv r -> (
# 511 "FStar.Syntax.Syntax.fst"
let _33_517 = bv
in {ppname = (FStar_Ident.mk_ident (bv.ppname.FStar_Ident.idText, r)); index = _33_517.index; sort = _33_517.sort}))

# 512 "FStar.Syntax.Syntax.fst"
let lid_as_fv : FStar_Ident.lident  ->  delta_depth  ->  fv_qual Prims.option  ->  fv = (fun l dd dq -> (let _122_1385 = (withinfo l tun (FStar_Ident.range_of_lid l))
in {fv_name = _122_1385; fv_delta = dd; fv_qual = dq}))

# 517 "FStar.Syntax.Syntax.fst"
let fv_to_tm : fv  ->  term = (fun fv -> (mk (Tm_fvar (fv)) None (FStar_Ident.range_of_lid fv.fv_name.v)))

# 518 "FStar.Syntax.Syntax.fst"
let fvar : FStar_Ident.lident  ->  delta_depth  ->  fv_qual Prims.option  ->  term = (fun l dd dq -> (let _122_1394 = (lid_as_fv l dd dq)
in (fv_to_tm _122_1394)))




