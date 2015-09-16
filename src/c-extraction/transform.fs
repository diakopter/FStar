module FStar.Extraction.C.Transform

open FStar
open FStar.Absyn
open FStar.Util
open FStar.Absyn.Syntax
open FStar.Absyn.Util

#light "off"

(* 
    TODO : 
        - specialization of functions declared in other functions' bodies
        - ...
*)

// Temporary information for the transformation
type context = 
    { 
        // Represent polymorphic types
        poly_types : list<sigelt>;
        
        // Polymorphic data constructors Sig_datacon(lid, typ, tycon...)
        // lid is the constructor name, (fun id,_,_ -> id) is the typ name
        poly_datacon : list<sigelt>;
        poly_funs : list<lident * list<option<btvar>>>;

        // TODO : remove these
        ftvs : list<btvar>;
        new_types : list<typ>; 

        // Map for calls to polymorphic functions/datacons
        // First lident is the polymorphic function
        // It maps to a map of its callee with the type arguments passed
        data: Map<lident, Map<lident, list<list<option<typ>>>>>;

        // Temporary information
        current: option<lident * list<option<btvar>>>;
    }

let empty_context() = 
    { poly_types = [];
      poly_datacon = [];
      poly_funs = [];
      ftvs = [];
      new_types = [];
      data = Map.empty;
      current = None }

let add_ptype_to_context context lid = {context with poly_types=lid::context.poly_types}

let add_pfun_to_context context pfun li = { context with poly_funs=(pfun, li)::context.poly_funs }

let add_call_to_context context callee typ_args = 
    match context.current with
    | Some(caller_id, bvars) ->
        let data = context.data in
        let caller = caller_id in
        let existing_calls = match Map.tryFind caller data with | Some d -> d | None -> Map.empty in
        let existing_typs = match Map.tryFind callee existing_calls with | Some d -> d | None -> [] in
        let existing_typs = typ_args::existing_typs in
        let existing_calls = Map.add callee existing_typs existing_calls in
        let data = Map.add caller existing_calls data in
        { context with data=data } 
    | _ ->
//        print_string "Could not get the caller's id\n";
        context

let contains_kind binders =
    List.fold (fun b binder -> match binder with | Inl _, _ -> true | _ -> b || false) false binders

let contains_typ binders =
    List.fold (fun b binder -> match binder with | Inl _, _ -> true | _ -> b || false) false binders

let contains_lid (lid:lident) (li:lident list) : bool =
    List.fold (fun b id -> b || lid_equals lid id) false li 

let get_typ_con typ = 
    match typ.n with
    | Typ_btvar _ -> "btvar"
    | Typ_const _ -> "const"
    | Typ_fun _ -> "fun"
    | Typ_refine _ -> "refine"
    | Typ_app _ -> "app"
    | Typ_lam _ -> "lam"
    | Typ_ascribed _ -> "ascribed"
    | Typ_meta _ -> "meta"
    | Typ_uvar _ -> "uvar"
    | Typ_delayed _ -> "delayed"
    | Typ_unknown -> "unknown"

let get_exp_con exp =
    match exp.n with
    | Exp_bvar _ -> "bvar"
    | Exp_fvar _ -> "fvar"
    | Exp_constant _ -> "constant"
    | Exp_abs _ -> "abs"
    | Exp_app _ -> "app"
    | Exp_match _ -> "match"
    | Exp_ascribed _ -> "ascribed"
    | Exp_let _ -> "let"
    | Exp_uvar _ -> "uvar"
    | Exp_delayed _ -> "delayed"
    | Exp_meta _ -> "meta"

let arg_is_typ arg =
    match fst arg with | Inl _ -> true | _ -> false

let arg_is_exp arg = not(arg_is_typ arg)

let rec is_fully_applied (typ:typ) : bool =
    match typ.n with
    | Typ_const k -> true
    | Typ_refine(x, t) -> is_fully_applied t
    | Typ_ascribed(t, k) -> is_fully_applied t
    | Typ_app(t, args) -> 
        let check_arg = fun a -> match a with | Inl t' -> is_fully_applied t' | _ -> false in
        List.fold (fun b arg -> b && check_arg (fst arg)) true args
    | Typ_btvar _ -> false
    | _ -> false

let get_type (exp:exp) : typ =
    let t' = exp.tk.contents in
    match t' with
    | None -> FStar.Tc.Recheck.recompute_typ exp
    | Some t -> t

// F* ~> Low* per module transformation
let get_sigelt_lid s =
    match s with
    | Sig_tycon(lid, _, _, _, _, _, _) -> lid
    | Sig_datacon(lid, _, _, _, _, _) -> lid
    | _ -> failwith ""

let rec find_call_in_typ env context typ : context = 
    match typ.n with
    | Typ_app(t, args) -> 
//        Printf.printf "Type application : %s | %s \n" (Print.typ_to_string typ) (Print.typ_to_string t);
        let context = List.fold (find_call_in_arg env) context args in
        context
    | Typ_ascribed(t, knd) -> find_call_in_typ env context t
    | Typ_meta(meta) -> 
        begin
        match meta with
        | Meta_pattern(t, args) -> 
            let context = find_call_in_typ env context t in
            List.fold (find_call_in_arg env) context args
        | Meta_named(t, _) -> find_call_in_typ env context t
        | _ -> context
        end
    | Typ_refine(_, t) -> find_call_in_typ env context t
    | Typ_lam(binders, t) -> find_call_in_typ env context t
    | Typ_fun(binders, comp) ->
        begin
        match comp.n with
        | Total t -> find_call_in_typ env context t 
        | Comp c -> find_call_in_typ env context c.result_typ
        end
    | _ -> 
        context

and find_call_in_exp env context exp : context =
    match exp.n with
    | Exp_abs(binders, e) -> find_call_in_exp env context e
    | Exp_app(e, args) -> 
        let fv, qual = match e.n with | Exp_fvar(fv, qual) -> fv, qual | _ -> failwith "expected fvar exp" in
        let lid = fv.v in
        let t = fv.sort in
        let is_datacon = match qual with | Some Data_ctor -> true | _ -> false in
        
        let typ_args = List.map (fun x -> match fst x with | Inl t -> Some t | _ -> None) args in
        let has_typ_args = List.fold (fun b x -> match x with | Some _ -> true | _ -> b) false typ_args in
        let context = if has_typ_args then add_call_to_context context lid typ_args
        else context in
            
        let context = find_call_in_exp env context e in
        List.fold (find_call_in_arg env) context args
    | Exp_match(e, li) ->
        let context = find_call_in_exp env context e in
        let exp_list = List.map (fun (_,_,x) -> x) li in
        List.fold (find_call_in_exp env) context exp_list
    | Exp_ascribed(e, t, li) ->
//        Printf.printf "%s \n" (Print.exp_to_string exp);
        let context = 
            match e.n, t.n with
            | Exp_abs(exp_bds, e'), Typ_fun(typ_bds, comp) ->
                context
            | _ -> context
            in
        let context = find_call_in_exp env context e in
        find_call_in_typ env context t
    | Exp_let(lbs, e) ->
        let context = find_call_in_lbs env context lbs in
        find_call_in_exp env context e
    | Exp_uvar(uv, t) -> find_call_in_typ env context t
    | Exp_meta(meta) ->
        (match meta with | Meta_desugared(e, msi) -> find_call_in_exp env context e)
    | _ -> context
 
and find_call_in_arg env context arg =
    match fst arg with
    | Inl t -> find_call_in_typ env context t
    | Inr e -> find_call_in_exp env context e

and find_call_in_lbs env context lbs =
    List.fold (find_call_in_lb env) context (snd lbs)
    
and find_call_in_lb env (context:context) lb : context  =
    let typ = lb.lbtyp in
    let exp = lb.lbdef in
    match typ.n, lb.lbname with
    | Typ_fun _, Inr lid -> 
        let prev_current = context.current in
        let context = { context with current = Some (lid, [])} in
        let context = find_call_in_typ env context typ in
        let context = find_call_in_exp env context exp in
        { context with current = prev_current}
    | _ ->
        let context = find_call_in_typ env context typ in
        find_call_in_exp env context exp

let rec get_poly_args (f:exp) =
    match f.n with
    | Exp_ascribed(e, t, eff) -> get_poly_args e
    | Exp_abs(bds, e) -> 
        let discriminate_binder (b:binder) =
            match fst b with
            | Inl btv -> Some btv
            | Inr bvv -> None in
        let args = List.map discriminate_binder bds in
        let has_poly = List.fold (fun b x -> match x with | Some _ -> true | _ -> b) false args in
        if has_poly then args
        else []
    | _ -> []

let process_fun env context lb =
    let lid = match lb.lbname with | Inl id -> failwith "issue in get_poly_fun" | Inr id -> id  in
    let e = lb.lbdef in
    let l = get_poly_args e in
    let context = if List.isEmpty l then context
    else add_pfun_to_context context lid l in
    find_call_in_lb env { context with current = Some (lid, l) } lb

let rec process_poly' env context sigelt =
    let sigelt = FStar.Tc.Normalize.norm_sigelt env sigelt in
    match sigelt with
    | Sig_let(lbs, r, lids, quals) -> 
        // lids contains the lid associated to each lb in lbs
//        print_string "\nLet bindings\n";
//        List.iter (fun x -> Printf.printf "%s " (get_exp_con x.lbdef)) (snd lbs);
//        print_string "\n";
        let context = List.fold (process_fun env) context (snd lbs) in
        { context with current = None }
    | Sig_val_decl(lid, t, quals, r) -> find_call_in_typ env context t
    | Sig_main(e, r) -> find_call_in_exp env context e
    | Sig_assume(lid, t, quals, r) -> find_call_in_typ env context t
    | Sig_tycon(lid, bds, knd, lids, lids2, quals, r) -> 
        if contains_kind bds then 
            add_ptype_to_context context sigelt
        else context
    | Sig_bundle(sigs, quals, lids, r) -> List.fold (process_poly' env) context sigs
    | Sig_datacon(lid, typ, tycon, quals, lids, r) -> 
        let datacon_typ = (fun (id, _, _) -> id) tycon in
        let poly_tycon = List.map (fun s -> match s with | Sig_tycon(lid,_,_,_,_,_,_) -> lid | _ -> failwith "Bad") context.poly_types in
        if contains_lid datacon_typ poly_tycon then
            { context with poly_datacon = sigelt::context.poly_datacon}
        else context
    | Sig_new_effect _   (* Something to be done for effects ? *)
    | Sig_sub_effect _ 
    | Sig_effect_abbrev _ 
    | Sig_kind_abbrev _ (* TODO : something to do ? *)
    | Sig_typ_abbrev _ (* TODO : something to do ? *)
    | Sig_pragma _ -> context

let process_poly (env:FStar.Tc.Env.env) (context:context) m =
    if m.name.str = "Prims" then context else
    List.fold (process_poly' env) context m.declarations

let mk_new_fun_lid (lid:lident) (typs:list<lident>) : string = "Not implemented yet\n"

let is_poly_fun context (lid:lident) : bool =
    let poly_ids = List.append (List.map get_sigelt_lid context.poly_datacon) (List.map fst context.poly_funs) in
    List.contains lid poly_ids

let is_mono_fun context lid : bool = not(is_poly_fun context lid)

let get_mono_funs (context:context) : list<lident> =
    let caller_ids = List.map fst (Map.toList context.data) in
    let entry_points = List.fold (fun l x -> if is_mono_fun context x then x::l else l) [] caller_ids in
    entry_points

let rec get_typ_args_from_typ (t:typ) =
    match t.n with
    | Typ_ascribed(t', k) -> get_typ_args_from_typ t'
    | Typ_fun(bds, comp) ->
        let discriminate_binder (b:binder) =
            match fst b with
            | Inl btv -> Some btv
            | Inr bvv -> None in
        let args = List.map discriminate_binder bds in
        let has_poly = List.fold (fun b x -> match x with | Some _ -> true | _ -> b) false args in
        if has_poly then args
        else []
    | Typ_app(ty, args) ->
        // TODO : FIXME !
        []
    | _ -> failwith ("Unexpected typ' at get typ args : " + (get_typ_con t) + " " + (Print.typ_to_string t))

let rec get_tbinders_from_typ (t:typ) =
    match t.n with
    | Typ_ascribed(t', k) -> get_tbinders_from_typ t'
    | Typ_fun(bds, comp) ->
        let discriminate_binder (b:binder) =
            match fst b with
            | Inl btv -> Some b
            | Inr bvv -> None in
        let args = List.map discriminate_binder bds in
        let has_poly = List.fold (fun b x -> match x with | Some _ -> true | _ -> b) false args in
        if has_poly then args
        else []
    | Typ_app(ty, args) -> 
        // TODO : FIXME !
        []
    | _ -> failwith ("Unexpected typ' at get tbinders : " + (get_typ_con t) + " " + (Print.typ_to_string t))

let lid_typs_from_datacon (f:sigelt) =
    match f with
    | Sig_datacon(lid, t, tc, quals, lids, r) ->
        let typ_args = get_typ_args_from_typ t in
        if List.isEmpty typ_args then () (* Printf.printf "Polymorphic datacon should have typ vars" *)
        else ();
        (lid, typ_args)
    | _ -> failwith "Expected datacon"

let rec eq_typ_args (a1:list<option<typ>>) (a2:list<option<typ>>) =
    match a1, a2 with
    | [], [] -> true
    | None::t1, None::t2 -> eq_typ_args t1 t2
    | (Some h1)::t1, (Some h2)::t2 -> if Print.typ_to_string h1 = Print.typ_to_string h2 then eq_typ_args t1 t2
                                      else false
    | _ -> false

let subst_with_new_types caller_binders (caller_types:list<option<typ>>) current_types =
    let subst = List.fold2 (fun m x y -> match x with | Some x -> Map.add (x.v.ppname.idText) y m | None -> m) 
                           Map.empty
                           caller_binders
                           caller_types in

//    Printf.printf "Contains 'a' ? : %s\n" (if Map.containsKey "a" subst then "true" else "false");
//    Printf.printf "subst : %s\n" (List.fold (fun s x -> match x with | Some y -> s + (Print.typ_to_string y) + " " | None -> s + "_ ") "" (List.map snd (Map.toList subst)));
//    Printf.printf "\t : %s\n" (List.fold (fun s x -> s + x + " ") "" (List.map fst (Map.toList subst)));
//    Printf.printf "orig : %s\n" (List.fold (fun s x -> match x with | Some y -> s + (Print.typ_to_string y) + " " | None -> s +  "_ ") "" current_types);

    List.map (fun x -> match x with | None -> x
                                    | Some x' -> 
                                        //print_string (if Map.containsKey (Print.typ_to_string x') subst then "true " else "false ");
                                        match Map.tryFind (Print.typ_to_string x') subst with 
                                        | Some y -> y 
                                        | None -> x)
              current_types

let process_new_call context (lid:lident) (calls:list<list<option<typ>>>) =
    let poly_funs = context.poly_funs in
    let poly_datacons = List.map lid_typs_from_datacon context.poly_datacon in
    let binders =   match List.find (fun x -> lid_equals lid (fst x)) (List.append poly_funs poly_datacons) with
                    | Some bds -> bds | None -> failwith "Could not find this polymorphic function or datacon" in
    let data = Map.toList context.data in
    let callees = match List.tryFind (fun x -> lid_equals lid (fst x)) data with | Some c -> snd c | _ -> Map.empty in

    let callees = Map.toList callees in
    let subst_typ_in_callee_1 ctyp (callee:list<list<option<typ>>>) = List.map (fun x -> subst_with_new_types (snd binders) ctyp x) callee in
    let subst_typ_in_callee_2 ctyps (callee:list<list<option<typ>>>) = List.fold (fun l x -> (subst_typ_in_callee_1 x callee)@l) [] calls in
    let l = List.fold (fun l x -> (fst x, subst_typ_in_callee_2 calls (snd x))::l) [] callees in

    l

let process_new_calls context new_calls =
    let current_calls = Map.toList new_calls in
    let add_new_typs fun_map fresh_fun_typs = List.fold (fun m x -> Map.add (fst x) (snd x) m) fun_map fresh_fun_typs in
    let updated_calls = List.fold (fun m x -> add_new_typs m (process_new_call context (fst x) (snd x))) new_calls current_calls in
    updated_calls

let remove_doubles l =
    let l' = [] in
    let print_typ t = List.fold (fun s x -> match x with | None -> s + "_ " | Some y -> s + (Print.typ_to_string y) + " ") "" t in
    let test x y = (print_typ x = print_typ y) in
    List.fold (fun l x -> if List.exists (test x) l then l else x::l) [] l

let calls_size m =
    let m = Map.toList m in
    List.fold (fun ctr x -> List.length (snd x) + ctr) 0 m

let merge_by_lid m =
    Map.fold    (fun m k v ->   let key = Map.tryFindKey (fun k' v' -> k.str = k'.str) m in
                                let k', v' = match key with | None -> k, [] | Some k'' -> k'', Map.find k'' m in
                                let v' = List.append v v' in
                                Map.add k' v' m)
                Map.empty
                m

let process_calls (context:context) =
    let entry_points = get_mono_funs context in
    
//    print_string "List of entry points : \n";
//    List.iter (fun x -> Printf.printf "%s " (Print.sli x)) entry_points;
//    print_string "\n";

    let calls_from_entry_points = List.fold (fun l x -> if List.contains (fst x) entry_points then (snd x)::l else l) [] (Map.toList context.data) in
    let calls_from_entry_points = List.fold (fun l x -> (Map.toList x)@l) [] calls_from_entry_points in

    let new_calls = Map.empty in

    let rec add_new_call m (lid:lident) (typ_args_list:list<list<option<typ>>>) = 
        match typ_args_list with
        | [] -> m
        | typ_args::tl -> 
            let key = Map.tryFindKey (fun k v -> lid.str = k.str) m in
            let calls = match key with | None -> [] | Some k -> Map.find k m in
            let calls = if List.exists (eq_typ_args typ_args) calls then calls else typ_args::calls in
            let m = Map.add lid calls m in
            add_new_call m lid tl in
    
    let new_calls = List.fold (fun m (lid, typ_args) -> add_new_call m lid typ_args) new_calls calls_from_entry_points in

    let rec all_calls context new_calls =
        let init_size = calls_size new_calls in
        let new_calls = process_new_calls context new_calls in
        let new_calls = merge_by_lid new_calls in
        let new_calls = Map.map (fun k v -> remove_doubles v) new_calls in
        let final_size = calls_size new_calls in
        if init_size = final_size then new_calls
        else all_calls context new_calls in

    //let _ = process_new_calls context new_calls in
    all_calls context new_calls

let print_new_id lid typs =
    List.fold (fun s x -> match x with | Some y -> s + "_" + (Print.typ_to_string y) | None -> s) (Print.sli lid) typs

let rec mk_new_typ (typ:typ) (old_typs:list<option<btvar>>) (new_typs:list<option<typ>>) =
    match typ.n with
    | Typ_ascribed(t', k) -> mk_new_typ t' old_typs new_typs
    | Typ_fun(bds, comp) ->
        let filter_binder (b:binder) =
            match fst b with
            | Inl btv -> Some btv
            | Inr bvv -> None in
        let args = List.fold (fun l x -> match filter_binder x with | Some y -> l | None -> x::l) bds in

        ()
    | _ -> failwith ("Unexpected typ' : " + (get_typ_con typ))

let mk_new_lid lid new_typs =
    let new_id = mk_ident (print_new_id lid new_typs, lid.ident.idRange) in
    lid_of_ids (lid.ns@[new_id])

let filter l = List.fold (fun l x -> match x with | None -> l | Some y -> l@[y]) [] l
    
let rec compress (t:typ) =
    let t = 
    match t.n with
    | Typ_fun(bds, comp) ->
        let c = comp.n in
        let c' = match c with | Total t -> Total (compress t) | Comp co -> Comp { co with result_typ = compress co.result_typ} in
        { t with n = Typ_fun(bds, { comp with n = c' }) }
    | Typ_refine(b, t') -> { t with n = Typ_refine(b, compress t') }
    | Typ_app(ty, args) -> { t with n = Typ_app(compress ty, args)}
    | Typ_lam(bds, ty) -> { t with n = Typ_lam(bds, compress ty)}
    | Typ_ascribed(ty, knd) -> { t with n = Typ_ascribed(compress ty, knd)}
    | Typ_meta(meta) -> let m = match meta with
                        | Meta_pattern(ty, args) -> Meta_pattern(compress ty, args)
                        | Meta_named(ty, lid) -> Meta_named(compress ty, lid)
                        | Meta_labeled(ty, s, r, b) -> Meta_labeled(compress ty, s, r, b)
                        | Meta_refresh_label(ty, b, r) -> Meta_refresh_label(compress ty, b, r)
                        | Meta_slack_formula(ty, ty', b) -> Meta_slack_formula(compress ty, ty', b) in
                        { t with n = Typ_meta(m)}
    | _ -> t
    in compress_typ t

let eq_bvd bvd1 bvd2 = bvd1.ppname.idText=bvd2.ppname.idText

let rec substitute_typ (subst:subst) typ = 
    match typ.n with
    | Typ_btvar(btvar) -> 
        begin
            let s = Util.find_map subst (function Inl (b, t) when (eq_bvd btvar.v b) -> Some t | _ -> None) in
            match s with
            | Some t -> 
                begin
//                    Printf.printf "Did a substitution : %s ~> %s\n" btvar.v.ppname.idText (Print.typ_to_string t);
                    substitute_typ subst t
                end
            | _ -> typ
        end
    | Typ_fun(bds, c) ->
        begin
            let new_bds = List.map (substitute_binder subst) bds in
            let new_bds = filter new_bds in
            let new_comp = substitute_comp subst c in
            { typ with n = Typ_fun(new_bds, new_comp) } 
        end
    | Typ_refine(bv, t) -> 
        let new_t = substitute_typ subst t in
        let new_bv = { bv with sort = substitute_typ subst bv.sort} in
        { typ with n = Typ_refine(new_bv, new_t) }
    | Typ_app(t, args) -> 
        let new_t = substitute_typ subst t in
        let new_args = List.map (substitute_arg subst) args in
        { typ with n = Typ_app(new_t, new_args) }
    | Typ_lam(bds, t) -> 
        begin
            let new_bds = List.map (substitute_binder subst) bds in
            let new_bds = filter new_bds in
            { typ with n = Typ_lam(new_bds, substitute_typ subst t) }
        end
    | Typ_ascribed (t, knd) -> { typ with n = Typ_ascribed(substitute_typ subst t, knd) }
    | Typ_meta(meta) ->
        begin
            let new_meta = match meta with
            | Meta_pattern(t, args) -> Meta_pattern(substitute_typ subst t, List.map (substitute_arg subst) args)
            | Meta_named(t, lident) -> Meta_named(substitute_typ subst t, lident)
            | Meta_labeled(t, s, r, b) -> Meta_labeled(substitute_typ subst t, s, r, b)
            | Meta_refresh_label(t, ob, r) -> Meta_refresh_label(substitute_typ subst t, ob, r)
            | Meta_slack_formula(t, t', r) -> Meta_slack_formula(substitute_typ subst t, substitute_typ subst t', r) in
            { typ with n = Typ_meta(new_meta)}
        end
    | Typ_delayed(e, m) -> 
        begin
            match e with
            | Inl(t, subst_t) -> let t' = compress_typ t in substitute_typ subst t'
            | Inr(mk_t) -> 
                let t = mk_t() in
                m := Some t;
                substitute_typ subst t
        end
    | Typ_uvar  _
    | Typ_const _ 
    | Typ_unknown  -> typ 

and substitute_comp (subst:subst) (comp:comp) =
    let c  = match comp.n with
    | Total t -> Total (substitute_typ subst t)
    | Comp ct -> Comp { ct with result_typ = substitute_typ subst ct.result_typ } in
    { comp with n = c }

and substitute_binder (subst:subst) binder =
    match binder with
    | Inr bv, quals -> 
        begin
            let new_bv = { bv with sort = substitute_typ subst bv.sort } in
            Some (Inr new_bv, quals)
        end
    | _ -> None

and substitute_arg (subst:subst) (arg:arg) =
    match arg with
    | Inl t, qual -> Inl (substitute_typ subst t), qual
    | Inr e, qual -> Inr (substitute_exp subst e), qual

and substitute_exp subst e =
    match e.n with
    | Exp_bvar(bv) -> e
    | Exp_fvar(fv, qual) -> e

//        let lid = fv.v in
//        let ty = fv.sort in
//        let ty_binders = filter (get_tbinders_from_typ ty) in
//        Printf.printf "Binders for fvar : %s\n" (Print.binders_to_string " " ty_binders);
//        let ty_binders = List.map (fun x -> match x with | Inl v, qual -> v | _ -> failwith "impossible") ty_binders in
//        let ty_args = List.map (fun b -> match  List.tryFind 
//                                                (fun s -> match s with | Inl(v,t) -> eq_bvd b.v v | _ -> failwith "impossible") 
//                                                subst 
//                                         with 
//                                        | Some (Inl(v,t)) -> Some t | _ -> None) ty_binders in
//        let new_lid = mk_new_lid lid ty_args in
//        
//        let new_typ = substitute_typ subst ty in
//        { e with n = Exp_fvar({fv with sort = new_typ; v = new_lid}, qual)}

    | Exp_constant _ -> e
    | Exp_abs(bds, e') -> 
        let new_bds = List.map (substitute_binder subst) bds in
        let new_bds = filter new_bds in
        let new_e = substitute_exp subst e' in
        { e with n = Exp_abs(new_bds, new_e)}
    | Exp_app(e', args) ->
        
//        let lid = fv.v in
//        let ty = fv.sort in
//        let ty_binders = filter (get_tbinders_from_typ ty) in
//        Printf.printf "Binders for fvar : %s\n" (Print.binders_to_string " " ty_binders);
//        let ty_binders = List.map (fun x -> match x with | Inl v, qual -> v | _ -> failwith "impossible") ty_binders in
//        let ty_args = List.map (fun b -> match  List.tryFind 
//                                                (fun s -> match s with | Inl(v,t) -> eq_bvd b.v v | _ -> failwith "impossible") 
//                                                subst 
//                                         with 
//                                        | Some (Inl(v,t)) -> Some t | _ -> None) ty_binders in
//        let new_lid = mk_new_lid lid ty_args in
//        
//        let new_typ = substitute_typ subst ty in
//        { e with n = Exp_fvar({fv with sort = new_typ; v = new_lid}, qual)}
        let fv, qual = match e'.n with | Exp_fvar(f, q) -> f, q | _ -> failwith "impossible" in
        let lid = fv.v in
        let ty = fv.sort in
        let typ_args = filter (List.map (fun x -> match fst x with | Inl t -> Some t | _ -> None) args) in

//        Printf.printf "Types : %s\n" (List.fold (fun s x -> s + " " + (Print.typ_to_string x)) "" typ_args);

        let norm_typ_args = List.map (FStar.Tc.Normalize.normalize PrettyPrint.empty_env) typ_args in

//        Printf.printf "Norms : %s\n" (List.fold (fun s x -> s + " " + (Print.typ_to_string x)) "" norm_typ_args);
//        Printf.printf "Bla : %s\n" (List.fold (fun s x -> s + " " + (Print.tag_of_typ x)) "" norm_typ_args);
//        Printf.printf "Substitution :\n"; 
//        List.iter   (fun s ->   let v,t = match s with | Inl(v,t) -> v,t | _ -> failwith "" in
//                                Printf.printf "%s ~> %s\n" v.ppname.idText (Print.typ_to_string t))
//                    subst;

        let subs_ty ty (subst:subst) = 
            match ty.n with
            | Typ_btvar(btv) -> 
                let v = List.tryFind (fun x -> eq_bvd (fst x) btv.v) (List.map (fun x -> match x with | Inl v -> v | _ -> failwith "impossible") subst) in
                ( match v with 
                | Some (v,t) -> Some t
                | None -> None )
            | Typ_const(c) -> Some ty
            | _ -> None in
        let new_typs = List.map (fun x -> subs_ty x subst) norm_typ_args in
        let new_lid = mk_new_lid lid new_typs in
        Printf.printf "New id : %s\n" (Print.sli new_lid);
        let new_e' = substitute_exp subst e' in
        let new_e' = { new_e' with n = Exp_fvar({ fv with v = new_lid }, qual) } in
        let new_args = List.map (substitute_arg subst) args in

        { e with n = Exp_app(new_e', new_args) }
    | Exp_match(e', li) ->
        { e with n = Exp_match(substitute_exp subst e', li) }
    | Exp_ascribed(e', t', li) ->
        let new_e = substitute_exp subst e' in
        let new_t = substitute_typ subst t' in
        { e with n = Exp_ascribed(new_e, new_t, li) }
    | Exp_let(lbs, e') ->
        let new_lbs = fst lbs, List.map (substitute_lb subst) (snd lbs) in
        let new_e = substitute_exp subst e' in
        { e with n = Exp_let(new_lbs, new_e) }
    | Exp_uvar(uv, t') -> { e with n = Exp_uvar(uv, substitute_typ subst t') }   
    | Exp_delayed(e', subst_e, m) ->
        begin
            let new_e = List.fold (fun v s -> substitute_exp s v) e' subst_e in
            let new_e = substitute_exp subst new_e in
            m := Some new_e;
            new_e   
        end
    | Exp_meta(Meta_desugared(e', msi)) -> 
        { e with n = Exp_meta(Meta_desugared(substitute_exp subst e', msi))}

and substitute_lb (subst:subst) (lb:letbinding) = { lb with lbtyp = substitute_typ subst lb.lbtyp; lbdef = substitute_exp subst lb.lbdef }

let rec mk_new_sigelt (env:FStar.Tc.Env.env) (context:context) (old_sigelt:sigelt) (typs:list<option<typ>>) =
    match old_sigelt with
    | Sig_bundle(sigelts, quals, lids, r) ->
        let new_sigelts = List.map (fun x -> mk_new_sigelt env context x typs) sigelts in
        let new_lids = List.map get_sigelt_lid new_sigelts in
        Sig_bundle(new_sigelts, quals, new_lids, r)
    | Sig_datacon(lid, typ, tycon, quals, lids, r) ->
        let is_poly = List.exists (fun x -> (get_sigelt_lid x).str = lid.str) context.poly_datacon in

        let new_lid = mk_new_lid lid typs in
        let old_typs = filter (get_tbinders_from_typ typ) in
        (* let new_typs = mk_new_typ typ old_typs new_typs in *)
        //let old_typs = List.map (fun x -> (Inl x, Some Equality)) (filter old_typs) in
        let new_typs = filter typs in
        
        let subst = if is_poly && List.length new_typs = List.length old_typs then 
            let new_typs = List.map2 (fun x y -> (Inl x, snd y)) (filter typs) old_typs in
            subst_of_list old_typs new_typs 
        else (print_string "\nWARNING : polymorphic call remaining, skipping substitution for it\n"; []) in

        // Print substitution for debugging
//        print_string "\nBinders to be substituted with : \n";
//        let print_subst_elt se = match se with | Inl(bt, t) -> bt.ppname.idText + "/" + bt.realname.idText + " ~> " + (Print.typ_to_string t) + " " + (tag_of_typ t) | _ -> "" in
//        let print_subst_list sl = List.fold (fun s x -> s + print_subst_elt x + "\n") "" sl in
//        print_string (print_subst_list subst);
//        print_string "\n";

        let new_typ = substitute_typ subst typ in

        // Print substituted type :
        Printf.printf "Type before subst : %s and after : %s\n" (Print.typ_to_string typ) (Print.typ_to_string new_typ);

        let new_tycon = 
            let tycon_id, bds, knd = tycon in
            (mk_new_lid tycon_id typs), (List.map (subst_binder subst) bds), subst_kind subst knd in
        let s = Sig_datacon(new_lid, new_typ, new_tycon, quals, lids, r) in
        s
    | Sig_let(lbs, r, lids, quals) -> 
        let subst_lb (lb:letbinding) = 
            let lid, t, e = lb.lbname, lb.lbtyp, lb.lbdef in
            let lid = match lid with | Inr id -> id | Inl _ -> failwith "Unexpected bvvdef" in
            if List.exists (fun x -> (fst x).str = lid.str) context.poly_funs then
                let new_lid = mk_new_lid lid typs in
                let old_typs = get_typ_args_from_typ t in
//                Printf.printf "Now inspecting : %s (%s)\n" (Print.sli lid) (Print.sli new_lid);
                let old_typs = List.map (fun x -> (Inl x, None)) (filter old_typs) in
                let new_typs = List.map (fun x -> (Inl x, None)) (filter typs) in
//                Printf.printf "Old types : %s and new types : %s \n" (Print.binders_to_string " " old_typs) (Print.args_to_string new_typs);
                let subst = if List.length old_typs = List.length new_typs then subst_of_list old_typs new_typs
                            else (print_string "\nWARNING : polymorphic call remaining, skipping substitution for it\n"; []) in
                
                // Print substitution for debugging
//                print_string "\nBinders to be substituted with : \n";
//                let print_subst_elt se = match se with | Inl(bt, t) -> bt.ppname.idText + "/" + bt.realname.idText + " ~> " + (Print.typ_to_string t) + " " + (tag_of_typ t)| _ -> "" in
//                let print_subst_list sl = List.fold (fun s x -> s + print_subst_elt x + "\n") "" sl in
//                print_string (print_subst_list subst);
//                print_string ">\n";

                let new_typ = substitute_typ subst t in                

//                Printf.printf "old type : %s \n" (Print.typ_to_string t);
//                Printf.printf "new type : %s \n" (Print.typ_to_string new_typ);

                let new_exp = substitute_exp subst e in

//                Printf.printf "old exp : %s \n" (Print.exp_to_string e);
//                Printf.printf "new exp : %s \n" (Print.exp_to_string new_exp);

                {lb with lbtyp = new_typ; lbname = Inr new_lid; lbdef = new_exp }
            else 
                { lb with lbdef = substitute_exp [] lb.lbdef; lbtyp = substitute_typ [] lb.lbtyp }
            in
        let new_lbs = (fst lbs, List.map subst_lb (snd lbs)) in
        Sig_let(new_lbs, r, lids, quals)
    | _ -> old_sigelt

// F* ~> Low* transformation
let transform fmods (env:FStar.Tc.Env.env) = 
    //List.iter (fun m -> Printf.printf "Module \n\n %s" (Print.modul_to_string m)) fmods;
    
    // Collect polymorphic types, datacons and functions information
    let context = List.fold (process_poly env) (empty_context()) fmods in
//
//    print_string "\nPolymorphic types : \n";
//    List.iter (fun x -> Printf.printf "%s\n" (Print.sigelt_to_string x)) context.poly_types;
//    print_string "\nPolymorphic datacon : \n";
//    List.iter (fun x -> Printf.printf "%s\n" (Print.sigelt_to_string x)) context.poly_datacon;
//    print_string "\nPolymorphic functions : \n";
//    List.iter (fun x -> Printf.printf "%s\n " (fst x).str) context.poly_funs;
//    print_string "\nNew functions and datacons to create : \n";
//    let data = context.data in
//    let data = Map.toList data in
//    for caller in data do
//        Printf.printf "For caller %s the following callees : \n" (Print.sli (fst caller));
//        let caller = Map.toList (snd caller) in
//        for callee in caller do
//            Printf.printf "\tcallee %s with types : \n" (Print.sli (fst callee));
//            for typ in snd callee do
//                let str = List.fold (fun s t -> match t with | Some t' -> s + "_" + (Print.typ_to_string t') | _ -> s) 
//                                    (Print.sli (fst callee))
//                                    typ in
//                Printf.printf "\t\t%s\n" str;
//            done;
//        done;
//    done;

    let all_calls = process_calls context in

    print_string "All calls : \n" ;
    for caller in Map.toList all_calls do
        Printf.printf "For function : %s the following types : \n" (fst caller).str;
        for typs in snd caller do
            Printf.printf "\t%s\n" (print_new_id (fst caller) typs);
        done;
        print_string "\n";
    done;
    print_string "\n";

    let ctrans_mod = match List.find (fun x -> x.name.str.Contains "C_Trans") fmods with
                    | Some k -> k | _ -> failwith "" in

//    for call in Map.toList all_calls do
//
//        for sigelt in ctrans_mod.declarations do
//            match sigelt with
//            | Sig_bundle(sigli, quals, lids, r) -> ()
//            | Sig_datacon _ ->  
//                begin
//                    let datacon = List.tryFind (fun x -> (get_sigelt_lid x).str = (get_sigelt_lid sigelt).str)
//                                                context.poly_datacon in
//                    match datacon with
//                    | Some datacon -> 
//                        begin
//                            for typs in snd call do
//                                let new_sigelt = mk_new_sigelt env context sigelt typs in
////                                let new_sigelt = FStar.Tc.Normalize.norm_sigelt env new_sigelt in
//                                Printf.printf "New sig elt : \n%s\n" (Print.sigelt_to_string new_sigelt);
//                                ()
//                            done;
//                        end
//                    | None -> ()
//                end
//            | Sig_let(lbs, r, lids, quals) -> 
//                begin
//                    let let_id = match (List.head (snd lbs)).lbname with
//                                | Inr lid -> lid | _ -> failwith "Bad id" in
//                    if let_id.str = (fst call).str then 
//                        for typs in snd call do
//                            Printf.printf "\nOld sig elt : \n%s\n" (Print.sigelt_to_string sigelt);
//                            let new_sigelt = mk_new_sigelt env context sigelt typs in
//                            let new_sigelt = FStar.Tc.Normalize.norm_sigelt env new_sigelt in
//                            Printf.printf "New sig elt : \n%s\n" (Print.sigelt_to_string new_sigelt);
//                            ()   
//                        done
//                    else ()
//                end
//            | _ -> ()
//        done;
//        
//    done;

    let rec mono_sigelt_1 env context sigelt call =
        match sigelt with
        | Sig_bundle(sig_list, quals, lidents, r) ->
            let datacon_lids = List.map get_sigelt_lid sig_list in
            if List.exists (fun x -> (fst call).str = x.str) datacon_lids then
            List.fold (fun l x -> (mk_new_sigelt env context sigelt x)::l) [] (snd call)
            else []

//        | Sig_datacon _ ->  
//            begin
//                let datacon_id = get_sigelt_lid sigelt in
//                if List.exists (fun x -> (get_sigelt_lid x).str = datacon_id.str) context.poly_datacon then
//                    if datacon_id.str = (fst call).str then
//                        List.fold (fun l x -> (mk_new_sigelt env context sigelt x)::l) [] (snd call)
//                    else []
//                else []
//            end

        | Sig_let(lbs, r, lids, quals) -> 
            begin
                let let_id = match (List.head (snd lbs)).lbname with
                            | Inr lid -> lid | _ -> failwith "Bad id" in
                if List.exists (fun x -> (fst x).str = let_id.str) context.poly_funs then
                    if let_id.str = (fst call).str then
                        List.fold (fun l x -> (mk_new_sigelt env context sigelt x)::l) [] (snd call)
                    else []
                else []
            end
        | _ -> [] in

    let mono_sigelt_2 env context sigelt calls = 
        print_string ">mono_sigelt_2 \n";
        List.fold (fun l x -> (mono_sigelt_1 env context sigelt x)@l) [] (Map.toList all_calls) in

    let mono_decl env context decl = 
        print_string ">mono_decl \n";
        List.fold 
        (fun l x -> 
            match x with
            | Sig_bundle(sigelts, quals, lids, r) ->
                let datacon_lids = List.map get_sigelt_lid sigelts in
                let is_poly = List.fold (fun b x -> b || List.exists (fun y -> y.str = (fst x).str) datacon_lids) false (Map.toList all_calls) in
                if is_poly then l@(mono_sigelt_2 env context x all_calls)
                else l@[x]

            | Sig_datacon _ -> let datacon_id = get_sigelt_lid x in
                               if List.exists (fun x -> (get_sigelt_lid x).str = datacon_id.str) context.poly_datacon then
                                    l@(mono_sigelt_2 env context x all_calls)
                                else l@[x]
            | Sig_let(lbs, r, lids, quals) ->
                let b = List.fold (fun b x' -> let lid = match x'.lbname with | Inr a -> a | _ -> failwith "impossible" in
                                        if List.exists (fun y -> (fst y).str = lid.str) context.poly_funs then true
                                        else b) false (snd lbs) in
                if b then l@(mono_sigelt_2 env context x all_calls) else l@[mk_new_sigelt env context x []]
            | _ -> l@[x])
        []
        decl in

    let mods = List.map (fun m -> if m.name.str.Contains "C_"  then { m with declarations = mono_decl env context m.declarations} 
                                                                else m) fmods in

    print_string "\n============================\n\n";
    let normalized_mod m = { m with declarations = List.map (FStar.Tc.Normalize.norm_sigelt !PrettyPrint.env) m.declarations } in
    List.iter (fun m -> if m.name.str.Contains "C_" then print_string (Print.modul_to_string (normalized_mod m)) else ()) mods;

    //let (env', context'), siglets' = Util.fold_map find_replace_ptypes (env, context) fmods in
    //print_string "New types to build : \n";
    //List.iter (fun typ -> Printf.printf "%s\n" (Print.typ_to_string typ)) context'.new_types;
    //let env', fmods' = Util.fold_map (transform_mod context) env fmods

    mods, env
