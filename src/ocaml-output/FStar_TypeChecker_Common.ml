
open Prims
# 26 "FStar.TypeChecker.Common.fst"
type rel =
| EQ
| SUB
| SUBINV

# 27 "FStar.TypeChecker.Common.fst"
let is_EQ = (fun _discr_ -> (match (_discr_) with
| EQ (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.TypeChecker.Common.fst"
let is_SUB = (fun _discr_ -> (match (_discr_) with
| SUB (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.TypeChecker.Common.fst"
let is_SUBINV = (fun _discr_ -> (match (_discr_) with
| SUBINV (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "FStar.TypeChecker.Common.fst"
type ('a, 'b) problem =
{pid : Prims.int; lhs : 'a; relation : rel; rhs : 'a; element : 'b Prims.option; logical_guard : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term); scope : FStar_Syntax_Syntax.binders; reason : Prims.string Prims.list; loc : FStar_Range.range; rank : Prims.int Prims.option}

# 31 "FStar.TypeChecker.Common.fst"
let is_Mkproblem = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkproblem"))))

# 44 "FStar.TypeChecker.Common.fst"
type prob =
| TProb of (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) problem
| CProb of (FStar_Syntax_Syntax.comp, Prims.unit) problem

# 45 "FStar.TypeChecker.Common.fst"
let is_TProb = (fun _discr_ -> (match (_discr_) with
| TProb (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.TypeChecker.Common.fst"
let is_CProb = (fun _discr_ -> (match (_discr_) with
| CProb (_) -> begin
true
end
| _ -> begin
false
end))

# 45 "FStar.TypeChecker.Common.fst"
let ___TProb____0 = (fun projectee -> (match (projectee) with
| TProb (_51_17) -> begin
_51_17
end))

# 46 "FStar.TypeChecker.Common.fst"
let ___CProb____0 = (fun projectee -> (match (projectee) with
| CProb (_51_20) -> begin
_51_20
end))

# 48 "FStar.TypeChecker.Common.fst"
type probs =
prob Prims.list

# 50 "FStar.TypeChecker.Common.fst"
type guard_formula =
| Trivial
| NonTrivial of FStar_Syntax_Syntax.formula

# 51 "FStar.TypeChecker.Common.fst"
let is_Trivial = (fun _discr_ -> (match (_discr_) with
| Trivial (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.TypeChecker.Common.fst"
let is_NonTrivial = (fun _discr_ -> (match (_discr_) with
| NonTrivial (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.TypeChecker.Common.fst"
let ___NonTrivial____0 = (fun projectee -> (match (projectee) with
| NonTrivial (_51_23) -> begin
_51_23
end))

# 54 "FStar.TypeChecker.Common.fst"
type deferred =
(Prims.string * prob) Prims.list

# 55 "FStar.TypeChecker.Common.fst"
type univ_ineq =
(FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)

# 60 "FStar.TypeChecker.Common.fst"
let tconst : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun l -> (let _140_83 = (let _140_82 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None)
in FStar_Syntax_Syntax.Tm_fvar (_140_82))
in (FStar_Syntax_Syntax.mk _140_83 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) FStar_Range.dummyRange)))

# 61 "FStar.TypeChecker.Common.fst"
let tabbrev : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun l -> (let _140_87 = (let _140_86 = (FStar_Syntax_Syntax.lid_as_fv l (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in FStar_Syntax_Syntax.Tm_fvar (_140_86))
in (FStar_Syntax_Syntax.mk _140_87 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) FStar_Range.dummyRange)))

# 62 "FStar.TypeChecker.Common.fst"
let t_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.unit_lid)

# 63 "FStar.TypeChecker.Common.fst"
let t_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.bool_lid)

# 64 "FStar.TypeChecker.Common.fst"
let t_int8 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tabbrev FStar_Syntax_Const.int8_lid)

# 65 "FStar.TypeChecker.Common.fst"
let t_uint8 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tabbrev FStar_Syntax_Const.uint8_lid)

# 66 "FStar.TypeChecker.Common.fst"
let t_int16 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tabbrev FStar_Syntax_Const.int16_lid)

# 67 "FStar.TypeChecker.Common.fst"
let t_uint16 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tabbrev FStar_Syntax_Const.uint16_lid)

# 68 "FStar.TypeChecker.Common.fst"
let t_int32 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tabbrev FStar_Syntax_Const.int32_lid)

# 69 "FStar.TypeChecker.Common.fst"
let t_uint32 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tabbrev FStar_Syntax_Const.uint32_lid)

# 70 "FStar.TypeChecker.Common.fst"
let t_int64 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tabbrev FStar_Syntax_Const.int64_lid)

# 71 "FStar.TypeChecker.Common.fst"
let t_uint64 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tabbrev FStar_Syntax_Const.uint64_lid)

# 72 "FStar.TypeChecker.Common.fst"
let t_int : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.int_lid)

# 73 "FStar.TypeChecker.Common.fst"
let t_string : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.string_lid)

# 74 "FStar.TypeChecker.Common.fst"
let t_float : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.float_lid)

# 75 "FStar.TypeChecker.Common.fst"
let t_char : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tabbrev FStar_Syntax_Const.char_lid)

# 76 "FStar.TypeChecker.Common.fst"
let t_range : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tabbrev FStar_Syntax_Const.range_lid)

# 78 "FStar.TypeChecker.Common.fst"
let rec delta_depth_greater_than : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth  ->  Prims.bool = (fun l m -> (match ((l, m)) with
| (FStar_Syntax_Syntax.Delta_constant, _51_30) -> begin
false
end
| (FStar_Syntax_Syntax.Delta_equational, _51_34) -> begin
true
end
| (_51_37, FStar_Syntax_Syntax.Delta_equational) -> begin
false
end
| (FStar_Syntax_Syntax.Delta_unfoldable (i), FStar_Syntax_Syntax.Delta_unfoldable (j)) -> begin
(i > j)
end
| (FStar_Syntax_Syntax.Delta_unfoldable (_51_46), FStar_Syntax_Syntax.Delta_constant) -> begin
true
end
| (FStar_Syntax_Syntax.Delta_abstract (d), _51_53) -> begin
(delta_depth_greater_than d m)
end
| (_51_56, FStar_Syntax_Syntax.Delta_abstract (d)) -> begin
(delta_depth_greater_than l d)
end))

# 87 "FStar.TypeChecker.Common.fst"
let rec decr_delta_depth : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth Prims.option = (fun _51_1 -> (match (_51_1) with
| (FStar_Syntax_Syntax.Delta_constant) | (FStar_Syntax_Syntax.Delta_equational) -> begin
None
end
| FStar_Syntax_Syntax.Delta_unfoldable (1) -> begin
Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Delta_unfoldable (i) -> begin
Some (FStar_Syntax_Syntax.Delta_unfoldable ((i - 1)))
end
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(decr_delta_depth d)
end))




