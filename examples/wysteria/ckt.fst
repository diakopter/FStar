module Circuit

open Prins
open AST
open Semantics

open FStar.IO

open FStar.List

open FStar.OrdMap
open FStar.OrdSet

type wrange = int * int

type binop = | Gt | Eq | Add | Sub

type celt =
  | Input     : prin -> wrange -> celt
  | Output    : prin -> wrange -> celt
  | BinOp     : binop -> wrange -> wrange -> wrange -> celt  //result, arg1, arg2
  | Const_nat : wrange -> nat -> celt
  | Const_bool: wrange -> bool -> celt
  | Mux       : wrange -> wrange -> wrange -> wrange -> celt  //result range, else branch range, then branch range, condition range
  | Copy      : wrange -> wrange -> celt

  | ShInput   : wrange -> celt
  | ShOutput  : wrange -> celt
  
type ckt = list celt

val string_cmp: string -> string -> Tot bool
let string_cmp s1 s2 = if FStar.String.compare s1 s2 < 1 then true else false

val varname_cmp: varname -> varname -> Tot bool
let varname_cmp v1 v2 = string_cmp (name_of_var v1) (name_of_var v2)

assume String_cmp_is_total_order: total_order string string_cmp
assume Varname_cmp_is_total_order: total_order varname varname_cmp

type varset = ordset varname varname_cmp

val fvs: exp -> varset
val fvs_l: list exp -> varset
let rec fvs e = match e with
  | E_box e1 e2            -> union (fvs e1) (fvs e2)
  | E_unbox e'             -> fvs e'
  | E_const _              -> empty
  | E_var x                -> singleton x
  | E_let x e1 e2          -> union (fvs e1) (remove x (fvs e2))
  | E_ffi 'a 'b _ _ _ args _ -> fvs_l args
  | E_cond e e1 e2         -> union (fvs e) (union (fvs e1) (fvs e2))
  | E_mksh e'              -> fvs e'
  | E_combsh e'            -> fvs e'
  | _                      -> failwith "Expression form not supported"

and fvs_l = function
  | []   -> empty
  | a::tl -> union (fvs a) (fvs_l tl)

val is_nat: typ -> Tot bool
let is_nat t = match t with
  | T_cons s _ -> s = "Prims.int"
  | _          -> false

let hd_of_cons (l:list 'a{is_Cons l}) = match l with
  | Cons x y -> x

let tl_of_cons (l:list 'a{is_Cons l}) = match l with
  | Cons x y -> y

val is_int_list: typ -> Tot bool
let is_int_list t = match t with
  | T_cons l _ ->
    l = "Prims.list" && is_Cons (T_cons.args t) && is_nat (hd_of_cons (T_cons.args t))
  | _          -> false

type inputmap = ordmap prin varset p_cmp

(*
 * Currently there is no support for things like boxes of boxes
 *)
val supported_box_content: typ -> Tot bool
let supported_box_content t = match t with
  | T_bool     -> true
  | T_cons _ _ -> is_nat t || is_int_list t
  | _          -> false

val supported_input_type: typ -> Tot bool
let supported_input_type t = match t with
  | T_bool     -> true
  | T_cons _ _ -> is_nat t || is_int_list t
  | T_box t'   -> supported_box_content t'
  | _ -> false

val is_share_var: varname -> Tot bool
let is_share_var (Var _ t) = is_T_sh t

val assign_prin: prins -> v:varname{not (is_share_var v)} -> env -> prin
let assign_prin ps v en =
  let Var s t = v in
  if supported_input_type t then
    match t with
      | T_bool     -> Some.v (choose ps)
      | T_cons _ _ -> Some.v (choose ps)
      | T_box t'  ->
    	let dv_opt = en v in
	if dv_opt = None then failwith "A free variable was not found in environment"
	else
	  let Some (D_v _ v') = dv_opt in
	  let p =
	    match v' with
	      | V_box ps' _ ->
		if subset ps' ps then Some.v (choose ps')
		else failwith "Values boxed for non-ps are not supported"
	      | _ -> failwith "Impossible: T_box for non V_box value!"
	  in
	  p
  else failwith "Input type not supported"

(*
 * we are going to assign each free variable as input of some party
 *)
val assign_inps: prins -> varset -> env -> inputmap
let rec assign_inps ps fvars en =
  if fvars = empty then OrdMap.empty
  else
    let Some v = choose fvars in
    let fvars' = remove v fvars in

    let m = assign_inps ps fvars' en in

    if not (is_share_var v) then
      let p = assign_prin ps v en in
      //print_string "Assigned "; print_string (Print.prin_to_string p); print_string " to "; print_string (name_of_var v); print_string "\n";
      if contains p m then
	let s = Some.v (select p m) in
	update p (union s (singleton v)) m
      else
	update p (singleton v) m
    else m

(* Counter for generating free wire ids *)
let ctr :ref int = alloc 1

let init_ctr (x:unit) = ctr := 1

val alloc_wires: n:int -> ML wrange
let alloc_wires n =
  if n <= 0 then failwith "Alloc wires, non-positive argument"
  else
    let r = (!ctr + 1, !ctr + n) in
    ctr := !ctr + n;
    r

let nil_range = (-1, -1)

type cktenv = string -> Tot (option wrange)

let natsize = 12

let listsize = 96

val size: typ -> (n:int{n > 0})
let rec size t = match t with
  | T_bool     -> 1
  | T_cons _ _ ->
    if is_nat t then natsize
    else if is_int_list t then listsize * natsize
    else failwith "Size does not support non-nat cons type"
  | T_box t'   ->
    if supported_box_content t' then size t'
    else failwith "Unsupported box content type in size function"
  | _          -> failwith "Unsupported type in the size function"

val range_to_string: wrange -> string
let range_to_string r =
  strcat "( " (strcat (string_of_int (fst r)) (strcat ", " (strcat (string_of_int (snd r)) ")")))

(*
 * GMW library needs all inputs of a party to be consecutive
 * so, go over the varset and assign wire ids to the inputs
 * also, populate the circuit env with the assigned ranges
 *)
val alloc_input_wires_for_prin: prin -> varset -> wrange -> cktenv -> (wrange * cktenv)
let rec alloc_input_wires_for_prin p vars r cen =
  if vars = empty then (r, cen)
  else
    let Some v = choose vars in
    let vars' = remove v vars in
    let Var s t = v in
    let r' = alloc_wires (size t) in
    //print_string "Allocated "; print_string (range_to_string r'); print_string " for variable "; print_string (name_of_var v); print_string "\n";
    let cen' = fun s' -> if s' = s then Some r' else cen s' in
    alloc_input_wires_for_prin p vars' (fst r, snd r') cen'

open FStar.IO

(*
 * call per prin input assignment for all the prins
 *)
val alloc_input_wires: eprins -> inputmap -> ckt -> cktenv -> (ckt * cktenv)
let rec alloc_input_wires eps m cs cen =
  if eps = empty then (cs, cen)
  else
    let Some p = choose eps in
    let eps' = remove p eps in
    if contains p m then
      let Some vars = select p m in
      let (r, cen') = alloc_input_wires_for_prin p vars (!ctr + 1, !ctr) cen in
      //print_string "Allocated "; print_string (range_to_string r); print_string " for "; print_string (Print.prin_to_string p); print_string "\n";
      alloc_input_wires eps' m (FStar.List.Tot.append cs [Input p r]) cen'
    else
      alloc_input_wires eps' m cs cen

val alloc_shinput_wires: int -> int -> varset -> ckt -> cktenv -> (ckt * cktenv)
let rec alloc_shinput_wires rbegin rend fvs cs cen =
  if fvs = empty then
    if rbegin = rend then cs, cen
    else
      FStar.List.Tot.append cs [ ShInput (rbegin, rend) ], cen
  else
    let Some v = choose fvs in
    let fvs' = remove v fvs in
    let Var s t = v in
    if is_T_sh t then
      let r = alloc_wires natsize in
      let rbegin = if rbegin = 0 then fst r else rbegin in
      alloc_shinput_wires rbegin (snd r) fvs' cs (fun s' -> if s' = s then Some r else cen s')
    else
      alloc_shinput_wires rbegin rend fvs' cs cen

val const_to_ckt: const -> (ckt * wrange * typ)
let const_to_ckt c = match c with
  | C_bool b       ->
    let r = alloc_wires (size (T_bool)) in
    [Const_bool r b], r, T_bool
  | C_opaque 'a v t ->
    if is_nat t then
      let r = alloc_wires (size t) in
      [Const_nat r (Ffibridge.nat_of_c_opaque c)], r, t
    else failwith "Non-nat opaque constant not supported"
  | _ -> failwith "Constant not supported"

val is_ffi_bin_op: string -> (bool * binop * typ)
let is_ffi_bin_op s =
  if s = "Prims.(>)" then true, Gt, T_bool
  else if s = "Prims.op_Equality" then true, Eq, T_bool
  else if s = "Prims.(+)" then true, Add, T_cons "Prims.int" []
  else if s = "Prims.(-)" then true, Sub, T_cons "Prims.int" []
  else false, Gt, T_bool

val unbox_t: typ -> typ
let unbox_t t = match t with
  | T_box t' -> t'
  | _ -> failwith "Unbox_t with a non T_box"

let rec get_cth_mem (c:nat) (r:wrange) =
  if fst r >= snd r then failwith "exceeded the bound in get_cth_mem"
  else
    if c = 0 then
      if fst r + natsize - 1 <= snd r then (fst r, fst r + natsize - 1)
      else failwith "exceeded the bound in get_cth_mem'"      
    else get_cth_mem (c - 1) (fst r + natsize, snd r)

let f x = failwith "This is a never called function"

let rec mem_exp_to_exp (x:exp{is_E_var x}) (l:exp{is_E_var l}) (c:nat) =
  if c = listsize then E_const (C_bool false)
  else
    let cth = E_ffi 2 "FFI.nth" f  [E_const (C_opaque c (T_cons "Prims.int" [])); l] f in
    let cond = E_ffi 2 "Prims.op_Equality" f [x; cth] f in

    let thenb = E_const (C_bool true) in
    let elseb = mem_exp_to_exp x l (c + 1) in

    E_cond cond thenb elseb

let rec intersect_exp_to_exp (l1:exp{is_E_var l1}) (l2:exp{is_E_var l2}) (c:nat) =
  if c = listsize then E_ffi 0 "FFI.mk_nil" f [] f
  else
    let nth_v = Var "__tmp_n__" (T_cons "Prims.int" []) in

    let mem_v = Var "__tmp__b__" T_bool in

    let rest_v = Var "__tmp__l__" (T_cons "Prims.list" [T_cons "Prims.int" []]) in

    let e2 = E_cond (E_var mem_v)
                    (E_ffi 2 "FFI.mk_cons" f [E_var nth_v; E_var rest_v] f)
                    (E_ffi 2 "FFI.mk_cons" f [E_const (C_opaque 0 (T_cons "Prims.int" [])); E_var rest_v] f) in

    let e2 = E_let rest_v (intersect_exp_to_exp l1 l2 (c + 1)) e2 in

    let e2 = E_let mem_v (mem_exp_to_exp (E_var nth_v) l2 0) e2 in

    E_let nth_v (E_ffi 2 "FFI.nth" f [E_const (C_opaque c (T_cons "Prims.int" [])); l1] f) e2

val exp_to_ckt: cktenv -> exp -> (ckt * wrange * typ)
let rec exp_to_ckt cen e = match e with
  | E_unbox e' ->
    let cs, r, t = exp_to_ckt cen e' in
    cs, r, unbox_t t
  | E_const c -> const_to_ckt c
  | E_var (Var s t) ->
    let r_opt = cen s in
    if is_None r_opt then failwith "Variable not found in cenv"
    else
      [], Some.v r_opt, t
  | E_let x e1 e2 ->
    let cs1, r1, _ = exp_to_ckt cen e1 in
    let cen' = fun s' -> if s' = name_of_var x then Some r1 else cen s' in
    let cs2, r2, t2 = exp_to_ckt cen' e2 in
    cs1 @ cs2, r2, t2
  | E_ffi 'a 'b _ fname _ args _ ->
    let b, op, t = is_ffi_bin_op fname in
    if b then
      let a1 = List.hd args in
      let a2 = List.hd (List.tl args) in
      let cs1, r1, _ = exp_to_ckt cen a1 in
      let cs2, r2, _ = exp_to_ckt cen a2 in
      let r3 = alloc_wires (size t) in
      cs1 @ cs2 @ [BinOp op r3 r1 r2], r3, t
    else if fname = "FFI.mk_nil" then
      [], nil_range, (T_cons "Prims.list" [T_cons ("Prims.int") []])
    else if fname = "FFI.mk_cons" then
      let a1 = List.hd args in
      let a2 = List.hd (List.tl args) in
      let cs1, r1, _ = exp_to_ckt cen a1 in
      let cs2, r2, _ = exp_to_ckt cen a2 in
      if r2 = nil_range then
	cs1 @ cs2, r1 , (T_cons "Prims.list" [T_cons ("Prims.int") []])
      else
	let n2 = snd r2 - fst r2 + 1 in
	let n1 = snd r1 - fst r1 + 1 in
	//admitP (n1 > 0 /\ n2 > 0);
	let r1' = alloc_wires n1 in
        let r2' = alloc_wires n2 in

        cs1 @ cs2 @ [Copy r1' r1; Copy r2' r2], (fst r1', snd r2'), (T_cons "Prims.list" [T_cons ("Prims.int") []])

    else if fname = "FFI.nth" then
      let a1 = List.hd args in
      let a2 = List.hd (List.tl args) in
      let cs2, r2, _ = exp_to_ckt cen a2 in
      if is_E_const a1 && is_C_opaque (E_const.c a1) then
        let c = Ffibridge.nat_of_c_opaque (E_const.c a1) in
	//FStar.IO.print_string "get_cth_mem with c: "; FStar.IO.print_string (string_of_int c); FStar.IO.print_string ", with range: "; FStar.IO.print_string (range_to_string r2); FStar.IO.print_string "\n";
	cs2, get_cth_mem c r2, T_cons "Prims.int" []
      else failwith "FFI.nth expects a constant argument"

    else if fname = "FFI.list_mem" then
      let a1 = List.hd args in
      let a2 = List.hd (List.tl args) in
      if is_E_var a1 && is_E_var a2 then
        let e' = mem_exp_to_exp a1 a2 0 in
	//FStar.IO.print_string (Print.exp_to_string e');
	exp_to_ckt cen e'
      else failwith "FFI.list_mem is supported only on variable expressions"

    else if fname = "FFI.list_intersect" then
      let a1 = List.hd args in
      let a2 = List.hd (List.tl args) in
      if is_E_var a1 && is_E_var a2 then
	let e' = intersect_exp_to_exp a1 a2 0 in
	exp_to_ckt cen e'
      else failwith "FFI.list_intersect is supported only for variable expressions"

    else failwith "FFI name not supported"
  | E_cond e1 e2 e3 ->
    let cs1, r1, _ = exp_to_ckt cen e1 in
    let cs2, r2, t2 = exp_to_ckt cen e2 in
    let cs3, r3, t3 = exp_to_ckt cen e3 in
    //let _ = admitP (b2t (snd r2 - fst r2 + 1 > 0)) in
    let r = alloc_wires (snd r2 - fst r2 + 1) in
    cs1 @ cs2 @ cs3 @ [Mux r r3 r2 r1], r, t2

  | E_mksh e' ->
    let cs, r, t = exp_to_ckt cen e' in
    cs, r, T_sh

  | E_combsh e' ->
    let cs, r, t = exp_to_ckt cen e' in
    cs, r, T_cons "Prims.int" []

  | _ -> failwith "Expression to circuit not supported"

val op_to_string : binop -> Tot string
let op_to_string = function
  | Gt  -> "Gt"
  | Eq  -> "Eq"
  | Add -> "Add"
  | Sub -> "Sub"

val celt_to_string: celt -> string
let celt_to_string = function
  | Input p r ->
    strcat "Input " (strcat (Print.prin_to_string p) (strcat " " (range_to_string r)))
  | Output p r ->
    strcat "Output " (strcat (Print.prin_to_string p) (strcat " " (range_to_string r)))
  | BinOp op r3 r1 r2 ->
    strcat "Binop " (strcat (op_to_string op) (strcat (range_to_string r3) (strcat " " (strcat (range_to_string r1) (strcat " " (range_to_string r2))))))
  | Const_nat r n ->
    strcat "Const_nat " (strcat (range_to_string r) (strcat " " (string_of_int n)))
  | Const_bool r n ->
    strcat "Const_bool " (strcat (range_to_string r) (strcat " " (string_of_bool n)))
  | Mux r r3 r2 r1 ->
    strcat "Mux " (strcat (range_to_string r) (strcat " " (strcat (range_to_string r3) (strcat " " (strcat (range_to_string r2) (strcat " " (range_to_string r1)))))))
  | Copy r1 r2 ->
    strcat "Copy " (strcat (range_to_string r1) (strcat " " (range_to_string r2)))

  | ShInput r ->
    strcat "ShInput " (range_to_string r)
  | ShOutput r ->
    strcat "ShOutput " (range_to_string r)

val ckt_to_string: ckt -> string
let ckt_to_string l =
  List.fold_left (fun s celt -> strcat s (strcat "\n" (celt_to_string celt))) "" l

type booleancelt =
  | AND: int -> int -> int -> booleancelt
  | XOR: int -> int -> int -> booleancelt
  | INPUT: prin -> wrange -> booleancelt
  | OUTPUT: prin -> wrange -> booleancelt

  | SHINPUT: wrange -> booleancelt
  | SHOUTPUT: wrange -> booleancelt

type bckt = list booleancelt

val booleancelt_to_string: booleancelt -> string
let booleancelt_to_string = function
  | AND i1 i2 i3 ->
    strcat "AND " (strcat (string_of_int i1) (strcat " " (strcat (string_of_int i2) (strcat " " (string_of_int i3)))))
  | XOR i1 i2 i3 ->
    strcat "XOR " (strcat (string_of_int i1) (strcat " " (strcat (string_of_int i2) (strcat " " (string_of_int i3)))))
  | INPUT p r ->
    strcat "INPUT " (strcat (Print.prin_to_string p) (strcat " " (range_to_string r)))
  | OUTPUT p r ->
    strcat "OUTPUT " (strcat (Print.prin_to_string p) (strcat " " (range_to_string r)))

  | SHINPUT r ->
    strcat "SHINPUT " (range_to_string r)
  | SHOUTPUT r ->
    strcat "SHOUTPUT " (range_to_string r)

val bckt_to_string: bckt -> string
let bckt_to_string l =
  fold_left (fun s belt -> strcat s (strcat "\n" (booleancelt_to_string belt))) "" l

val flatten_range: wrange -> list int
let flatten_range r =
  let rec helper k l =
    if k = fst r then k::l
    else helper (k - 1) (k::l)
  in
  helper (snd r) []

(* i <- j *)
val copy: int -> int -> booleancelt
let copy i j = XOR i j 0

val nat_to_bin: nat -> list int
let nat_to_bin n =
  let rec helper n =
    if n / 2 = 0 then
      [n]
    else
      (n % 2)::(helper (n / 2))
  in
  let rec pad l =
    if List.length l > natsize then
      failwith "natsize not sufficient"
    else if List.length l = natsize then
      l
    else
      pad (l @ [0])
  in
  pad (helper n)

val int_list_to_bin: list nat -> list int
let rec int_list_to_bin l =
  if l = [] then []
  else
    let l' = nat_to_bin (hd_of_cons l) in
    let l'' = int_list_to_bin (tl_of_cons l) in
    l' @ l''

val celt_to_booleancelt: celt -> bckt
let celt_to_booleancelt celt = match celt with
  | Input p r -> [ INPUT p r ]
  | Output p r -> [ OUTPUT p r ]
  | Mux r3 r1 r2 r4 -> 
    let l1 = flatten_range r1 in
    let l2 = flatten_range r2 in
    let l3 = flatten_range r3 in

    let f (c, out) b1 b2 =
      let t1 = 1 in
      let (t2, _) = alloc_wires 1 in
      let g1 = XOR t2 t1 (fst r4) in
      let (t3, _) = alloc_wires 1 in
      let g2 = XOR t3 b1 b2 in
      let (t4, _) = alloc_wires 1 in
      let g3 = AND t4 t2 t3 in
      let (t5, _) = alloc_wires 1 in
      let g4 = XOR t5 t4 b2 in
      g4::g3::g2::g1::c, t5::out
    in

    let (rbckt, rout) = fold_left2 f ([], []) l1 l2 in
    let (bckt, out) = rev_append rbckt [], rev_append rout [] in
      
    let f ckt b1 b2 = (copy b1 b2)::ckt in
    rev_append (fold_left2 f bckt l3 out) []
  | BinOp op r3 r1 r2 ->
    if op = Gt then
      let l1 = flatten_range r1 in
      let l2 = flatten_range r2 in

      let f (ckt, c) b1 b2 =
	let (t1, _) = alloc_wires 1 in
	let g1 = XOR t1 b1 c in
	let (t2, _) = alloc_wires 1 in
	let g2 = XOR t2 b2 c in
	let (t3, _) = alloc_wires 1 in
	let g3 = AND t3 t1 t2 in
	let (c1, _) = alloc_wires 1 in
	let g4 = XOR c1 t3 b1 in
	g4::g3::g2::g1::ckt, c1
      in
      
      let (rbckt, c) = fold_left2 f ([], 0) l1 l2 in
      rev_append ((copy (fst r3) c)::rbckt) []
    else if op = Eq then
      let l1 = flatten_range r1 in
      let l2 = flatten_range r2 in

      let f (ckt, c) b1 b2 =
	let (t1, _) = alloc_wires 1 in
	let g1 = XOR t1 b1 b2 in
	let (t2, _) = alloc_wires 1 in
	let g2 = copy t2 1 in
	let (t3, _) = alloc_wires 1 in
	let g3 = XOR t3 t1 t2 in
	let (c1, _) = alloc_wires 1 in
	let g4 = AND c1 t3 c in
	g4::g3::g2::g1::ckt, c1
      in
      let (rbckt, c) = fold_left2 f ([], 1) l1 l2 in
      rev_append ((copy (fst r3) c)::rbckt) []
    else if op = Add then
      let l1 = flatten_range r1 in
      let l2 = flatten_range r2 in
      let l3 = flatten_range r3 in

      let f (ckt, out, c) b1 b2 =
	let (t1, _) = alloc_wires 1 in
        let g1 = XOR t1 b1 c in
        let (t2, _) = alloc_wires 1 in
        let g2 = XOR t2 b2 c in
        let (t3, _) = alloc_wires 1 in
        let g3 = AND t3 t1 t2 in
        let (c1, _) = alloc_wires 1 in
        let g4 = XOR c1 t3 c in
        let (t4, _) = alloc_wires 1 in
        let g5 = XOR t4 b1 b2 in
        let (s, _) = alloc_wires 1 in
        let g6 = XOR s t4 c in
        g6::g5::g4::g3::g2::g1::ckt, s::out, c1
      in

      let (rbckt, rout, _) = fold_left2 f ([], [], 0) l1 l2 in	
      let (bckt, out) = rev_append rbckt [], rev_append rout [] in
    
      let f ckt b1 b2 = (copy b1 b2)::ckt in
      let l = rev_append (fold_left2 f bckt l3 out) [] in
      l
    else if op = Sub then
      let l1 = flatten_range r1 in
      let l2 = flatten_range r2 in
      let l3 = flatten_range r3 in

      let f (ckt, out, c) b1 b2 =
	let (t1, _) = alloc_wires 1 in
	let g1 = XOR t1 b1 c in
	let (t2, _) = alloc_wires 1 in
	let g2 = XOR t2 b2 c in
	let (t3, _) = alloc_wires 1 in
	let g3 = AND t3 t1 t2 in
	let (c1, _) = alloc_wires 1 in
	let g4 = XOR c1 t3 b1 in
	let (t4, _) = alloc_wires 1 in
	let g5 = XOR t4 b1 b2 in
	let (t5, _) = alloc_wires 1 in
	let g6 = XOR t5 t4 c in
	let (s, _) = alloc_wires 1 in
	let g7 = XOR s t5 1 in
	g7::g6::g5::g4::g3::g2::g1::ckt, s::out, c1
      in

      let (rbckt, rout, _) = fold_left2 f ([], [], 1) l1 l2 in
      let bckt, out = rev_append rbckt [], rev_append rout [] in

      let f ckt b1 b2 = (copy b1 b2)::ckt in
      rev_append (fold_left2 f bckt l3 out) []
    else []
  | Const_nat r n ->
    let l1 = flatten_range r in
    let l2 = nat_to_bin n in
    rev_append (fold_left2 (fun c i1 i2 -> (copy i1 i2)::c) [] l1 l2) []
  | Const_bool r b ->
    let l1 = flatten_range r in
    let l2 = if b then [1] else [0] in
    rev_append (fold_left2 (fun c i1 i2 -> (copy i1 i2)::c) [] l1 l2) []
  | Copy r1 r2 ->
    let l1 = flatten_range r1 in
    let l2 = flatten_range r2 in
      (*List.fold_left2 (fun c i1 i2 -> c @ [copy i1 i2]) [] l1 l2*)
    List.rev_append (List.fold_left2 (fun c i1 i2 -> (copy i1 i2)::c) [] l1 l2) []

  | ShInput r -> [ SHINPUT r ]
  | ShOutput r -> [ SHOUTPUT r ]

val assign_out: eprins -> wrange -> typ -> ckt
let rec assign_out eps r t =
  if t = T_sh then [ ShOutput r ]
  else
    if r = nil_range then []
    else
      if eps = empty then []
      else
	let Some p = choose eps in
	let eps' = remove p eps in
	(Output p r)::(assign_out eps' r t)

val prin_to_id: prin -> nat
let prin_to_id p = match p with
  | Alice -> 0
  | Bob -> 1
  | Charlie -> 2
  | Dave -> 3
  | Evelyn -> 4
  | Fred -> 5

val int_cmp: int -> int -> Tot bool
let int_cmp n1 n2 = n1 <= n2

type aux_info = Hashtable.t int (list int)

val calc_auxinf: bckt -> aux_info
let calc_auxinf bckt =
  List.fold_left (fun m belt ->
    match belt with
      | AND x y z
      | XOR x y z ->
	let ym =
	  if Hashtable.mem m y then Hashtable.find m y
	  else []
	in
	let zm =
	  if Hashtable.mem m z then Hashtable.find m z
	  else []
	in
	Hashtable.add (Hashtable.add m z (x::zm)) y (x::ym) 
      | _ -> m
  ) (Hashtable.create int (list int) (List.length bckt)) bckt

val dump_gmw: prins -> bckt -> fd_write -> unit
let dump_gmw prs bckt fd =
  let ps s = write_string fd s in
  let psi i = write_string fd (string_of_int i) in

  let inps = filter (fun bcelt -> is_INPUT bcelt || is_SHINPUT bcelt) bckt in
  //print_string "done1";
  let outs = filter (fun bcelt -> is_OUTPUT bcelt || is_SHOUTPUT bcelt) bckt in
  //print_string "done2";
  let ands = filter (fun bcelt -> is_AND bcelt) bckt in
  //print_string "done3";
  let xors = filter (fun bcelt -> is_XOR bcelt) bckt in
  let aux = calc_auxinf bckt in
  //print_string "done4";

  let last_inp_id = List.fold_left (fun id belt ->
    match belt with
      | INPUT _ (_, j) -> if id < j then j else id
      | SHINPUT (_, j) -> if id < j then j else id
      | _ -> failwith "Ah, wish it was refined to not have this case"
  ) 0 inps in
  //print_string "done5";

  ps "n "; psi (OrdSet.size prs); ps "\n"; //num of parties
  ps "d "; psi (!ctr + 1); ps " "; psi (last_inp_id + 1); ps " "; psi (List.length xors); ps "\n";

  List.iter (fun belt ->
    match belt with
      | INPUT p (i, j) ->
	ps "i "; psi (prin_to_id p); ps " "; psi i; ps " "; psi j; ps "\n"

      | SHINPUT (i, j) ->
	ps "s "; psi i; ps " "; psi j; ps "\n"
      | _ -> failwith "Ah, wish it was refined to not have this case"
  ) inps;
  //print_string "done6";
  List.iter (fun belt ->
    match belt with
      | OUTPUT p (i, j) ->
	ps "o "; psi (prin_to_id p); ps " "; psi i; ps " "; psi j; ps "\n"

      | SHOUTPUT (i, j) ->
	ps "t "; psi i; ps " "; psi j; ps "\n"
      | _ -> failwith "Ah, wish it was refined to not have this case"
  ) outs;
  // this is mysterious, why ?
  List.iter (fun belt ->
    match belt with
      | INPUT p _ ->
	ps "v "; psi (prin_to_id p); ps " 1"; ps "\n"
      | SHINPUT _ -> ()
      | _ -> failwith "Ah, wish it was refined to not have this case"
  ) inps;

  //print_string "done7";
  ps "g 0 0 -1 -1 ";
  let l0 = if Hashtable.mem aux 0 then Hashtable.find aux 0 else [] in
  psi (List.length l0);
  List.iter (fun i -> ps " "; psi i) l0; ps "\n";

  ps "g 1 0 -1 -1 ";
  let l1 = if Hashtable.mem aux 1 then Hashtable.find aux 1 else [] in
  psi (List.length l1);
  List.iter (fun i -> ps " "; psi i) l1; ps "\n";

  //print_string "done8";
  List.iter (fun belt ->
    //let _ = print_string "elt" in
    match belt with
      | INPUT _ r ->
	let l = flatten_range r in
	List.iter (fun i ->
	  ps "g "; psi i; ps " 0 -1 -1 ";
	  let l' = if Hashtable.mem aux i then Hashtable.find aux i else [] in
	  psi (List.length l');
	  List.iter (fun i' -> ps " "; psi i') l'; ps "\n"
	) l
      | SHINPUT r ->
	let l = flatten_range r in
	List.iter (fun i ->
	  ps "g "; psi i; ps " 0 -1 -1 ";
	  let l' = if Hashtable.mem aux i then Hashtable.find aux i else [] in
	  psi (List.length l');
	  List.iter (fun i' -> ps " "; psi i') l'; ps "\n"
	) l
      | AND x y z ->
	ps "g "; psi x; ps " 1 "; psi y; ps " "; psi z; ps " ";
	let l = if Hashtable.mem aux x then Hashtable.find aux x else [] in
	psi (List.length l);
	List.iter (fun i -> ps " "; psi i) l;
	ps "\n"
      | XOR x y z ->
	ps "g "; psi x; ps " 2 "; psi y; ps " "; psi z; ps " ";
	let l = if Hashtable.mem aux x then Hashtable.find aux x else [] in
	psi (List.length l);
	List.iter (fun i -> ps " "; psi i) l;
	ps "\n"
      | _ -> ()
  ) bckt;
  ()

val dump_val: #meta:v_meta -> v:value meta -> typ -> fd_write -> unit
let rec dump_val #meta v t fd = match v with
  | V_box _ v'           -> dump_val v' (unbox_t t) fd
  | V_opaque 'a _ _ _ _ _ ->
    if is_nat t then
      let n = Ffibridge.nat_of_v_opaque v in
      let l = nat_to_bin n in
      List.iter (fun b -> write_string fd (string_of_int b); write_string fd " ") l
    else if is_int_list t then
      let l = Ffibridge.int_list_of_v_opaque v in
      if length l = listsize then
        let l' = int_list_to_bin l in
	List.iter (fun b -> write_string fd (string_of_int b); write_string fd " ") l'
      else failwith "listsize is not constant size that we expect"
  | V_bool b             -> if b then write_string fd "1 " else write_string fd "0 "
  | _ -> failwith "Dumping of this value is not supported"

val dump_inps: varset -> env -> fd_write -> unit
let rec dump_inps vars en fd =
  if vars = empty then ()
  else
    //TODO: check that value type is nat or bool?
    let Some v = choose vars in
    let vars' = remove v vars in
    let Var _ t = v in
    if is_T_sh t then dump_inps vars' en fd
    else
      if supported_input_type t then
	let dv_opt = en v in
	if is_None dv_opt then failwith "Input is not mapped in the env"
	else
	  let Some (D_v _ v) = dv_opt in
	  dump_val v t fd;
	  dump_inps vars' en fd
      else failwith "Dumpinps input type not supported"

val is_v_sh: #meta:v_meta -> v:value meta -> Tot bool
let is_v_sh #meta v = match v with
  | V_sh _ _ _ -> true
  | _          -> false

val dump_shinps: varset -> env -> fd_write -> unit
let rec dump_shinps vars en fd =
  if vars = empty then ()
  else
    let Some v = choose vars in
    let vars' = remove v vars in
    let Var _ t = v in
    if not (is_T_sh t) then dump_shinps vars' en fd
    else
      let dv_opt = en v in
      if is_None dv_opt then failwith "Sh input not mapped in the env"
      else
	let Some (D_v _ v) = dv_opt in
	if is_v_sh v then
	  let V_sh _ _ b = v in
	  let s = Runtime.string_of_bytes b in
	  write_string fd s;
	  dump_shinps vars' en fd
	else failwith "Sh input mapped to non V_sh"

(* GMW lib needs total input size for the party *)
val get_inp_size: prin -> bckt -> int
let rec get_inp_size p = function
  | [] -> 0
  | belt::tl ->
    let n =
      match belt with
	| INPUT p' r -> if p' = p then (snd r - fst r + 1) else 0
	| _ -> 0
    in
    if n = 0 then get_inp_size p tl else n

val ckt_fname: prin -> string
let ckt_fname p =
  let s = Print.prin_to_string p in
  let s' = FStar.String.substring s 0 1 in
  strcat "circuit_" (strcat s' ".txt")

val inp_fname: prin -> string
let inp_fname p =
  let s = Print.prin_to_string p in
  let s' = FStar.String.substring s 0 1 in
  strcat "input_" (strcat s' ".txt")

val out_fname: prin -> string
let out_fname p =
  let s = Print.prin_to_string p in
  let s' = FStar.String.substring s 0 1 in
  strcat "output_" (strcat s' ".txt")

val shinp_fname: prin -> string
let shinp_fname p =
  let s = Print.prin_to_string p in
  let s' = FStar.String.substring s 0 1 in
  strcat "shinput_" (strcat s' ".txt")

val shout_fname: prin -> string
let shout_fname p =
  let s = Print.prin_to_string p in
  let s' = FStar.String.substring s 0 1 in
  strcat "shoutput_" (strcat s' ".txt")

val conf_fname: prin -> string
let conf_fname p =
  let s = Print.prin_to_string p in
  let s' = FStar.String.substring s 0 1 in
  strcat "config" (strcat s' ".txt")

val dump_conf: prin -> int -> fd_write -> unit
let dump_conf p n fd =
  let ps = write_string fd in
  ps "load-circuit "; ps (ckt_fname p); ps "\n";
  ps "input "; ps (inp_fname p); ps "\n";
  ps "output "; ps (out_fname p); ps "\n";
  ps "shinput "; ps (shinp_fname p); ps "\n";
  ps "shoutput "; ps (shout_fname p); ps "\n";
  ps "num_input "; ps (string_of_int n); ps "\n"

val prin_to_gmwport: prin -> int
let prin_to_gmwport p = match p with
  | Alice -> 9000
  | Bob -> 9001
  | Charlie -> 9002
  | _ -> failwith "Sorry, I don't know you!"

val supported_output_type: typ -> Tot bool
let supported_output_type t = match t with
  | T_bool     -> true
  | T_cons _ _ -> is_nat t || is_int_list t
  | T_sh       -> true
  | _          -> false

let const_meta (u:unit) = Meta empty Can_b empty Can_w

let rec get_natsize_elt (l:list 'a) (n:nat) =
  if n = natsize then [], l
  else
    let l', l'' = get_natsize_elt (FStar.List.tl l) (n + 1) in
    (FStar.List.hd l)::l', l''

let parse_int (l:list string) = Runtime.list_to_int l

let rec parse_int_list (l:list string) =
  if length l = 0 then []
  else
    let l', l'' = get_natsize_elt l 0 in
    let n = parse_int l' in
    n::(parse_int_list l'')

open Platform.Bytes

val parse_output: list string -> bytes -> typ -> prins -> dvalue
let parse_output l b t ps = match t with
  | T_bool     ->
    if l = ["0"] then D_v (const_meta ()) (V_bool false)
    else if l = ["1"] then D_v (const_meta ()) (V_bool true)
    else failwith "Unexpected GMW output for boolean type"

  | T_cons _ _ ->
    if is_nat t then
      let n = parse_int l in
      D_v (const_meta ()) (V_opaque n (const_meta ()) slice_const compose_const slice_const_sps)
    else if is_int_list t then
      let l' = parse_int_list l in
      D_v (const_meta ()) (V_opaque l' (const_meta ()) slice_const compose_const slice_const_sps)

    else failwith "Unsupported output cons (should have been checked earlier)"

  | T_sh -> D_v (Meta empty Can_b empty Cannot_w) (V_sh ps V_emp b)

  | _ -> failwith "Unsupported output type (should have been checked earlier)"

val typ_to_string: typ -> string
val typ_l_to_string: list typ -> string
let rec typ_to_string t = match t with
  | T_prin -> "T_prin"
  | T_eprins -> "T_eprins"
  | T_unit -> "T_unit"
  | T_bool -> "T_bool"
  | T_cons s args -> strcat "T_cons " (strcat s (strcat " [" (strcat (typ_l_to_string args) " ]")))
  | T_box t' -> strcat "T_box " (typ_to_string t')
  | T_wire t' -> strcat "T_wire " (typ_to_string t')
  | T_fun t1 t2 -> strcat "T_fun " (strcat (typ_to_string t1) (strcat " " (typ_to_string t2)))
  | T_sh -> "T_sh"
  | T_unknown -> "T_unknown"

and typ_l_to_string l = fold_left (fun s t -> strcat s (strcat "; " (typ_to_string t))) "" l

val rungmw: prin -> prins -> env -> cktenv -> exp -> dvalue
let rungmw p ps en cen e =
  init_ctr ();

  let freevs = fvs e in
  let m = assign_inps ps freevs en in
  let cs_inp, cen = alloc_input_wires ps m [] cen in
  let cs_shinps, cen = alloc_shinput_wires 0 0 freevs [] cen in

  let cs_e, r, t = exp_to_ckt cen e in
  let cs_out = assign_out ps r t in

  let _ =
    if supported_output_type t then ()
    else
      failwith (strcat "Output type not supported: " (typ_to_string t))
  in

  let final_ckt = cs_inp @ cs_shinps @ cs_e @ cs_out in
  //print_string (ckt_to_string final_ckt);
  (*print_string "created high level circuit";*)
  //print_string "\n";
  let bckt = flatten (map (fun celt -> celt_to_booleancelt celt) final_ckt) in
  //print_string (bckt_to_string bckt);
  (*print_string "created boolean circuit";
  print_string "\n";*)

  let conf_fname = conf_fname p in
  let ckt_fname = ckt_fname p in
  let inp_fname = inp_fname p in
  let shinp_fname = shinp_fname p in

  (*print_string "Dumping GMW:\n";*)
  let fd = open_write_file ckt_fname in
  dump_gmw ps bckt fd;
  close_write_file fd;

  (*print_string "Dumping inputs:\n";*)
  let fd = open_write_file inp_fname in
  let _ =
    if contains p m then dump_inps (Some.v (select p m)) en fd
    else ()
  in
  close_write_file fd;

  let fd = open_write_file shinp_fname in
  dump_shinps freevs en fd;
  close_write_file fd;

  (*print_string "Dumping config:\n";*)
  let fd = open_write_file conf_fname in
  dump_conf p (get_inp_size p bckt) fd;
  close_write_file fd;

  let port = prin_to_gmwport p in
  let (out_l, sh_bytes) = Runtime.rungmw conf_fname (out_fname p) (shout_fname p) port in
  parse_output out_l sh_bytes t ps
