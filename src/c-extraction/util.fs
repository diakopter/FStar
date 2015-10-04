module FStar.Extraction.C.Util

open FStar
open FStar.Util
open FStar.Absyn
open FStar.Absyn.Syntax

#light "off"

let filter li =
    List.fold (fun l x -> match x with | Some t -> l@[t] | _ -> l) [] li

let contains_lid lid li =
    List.exists (fun x -> lid.str = x.str) li

let mk_type_kind () =
     { n = Kind_type; tk = ref None; pos = dummyRange; fvs = ref None; uvs = ref None }

let mk_unit_lid () =
    let prims_id = mk_ident("Prims", dummyRange) in
    let unit_id = mk_ident("unit", dummyRange) in
    lid_of_ids [prims_id; unit_id]

let mk_unit_typ () =
    let lid = mk_unit_lid () in
    let sort = mk_type_kind () in
    mk_Typ_const { v = lid; sort = sort; p = dummyRange } (Some (mk_type_kind())) dummyRange

let mk_unit_val () =
    let t = mk_unit_typ () in
    mk_Exp_constant Const_unit (Some t) dummyRange

let lids_from_toplet sigelt =
    match sigelt with
    | Sig_let(lbs, r, lids, quals) ->
        List.map (fun x -> match x.lbname with | Inr lid -> lid | _ -> failwith "Expected only ids") (snd lbs)
    | _ -> failwith "Expected a Sig_let"

(* Analyses a type to determine whether or not it should be erased.
    Returns "true" if the type is erasable, false otherwise.
 *)

//let has_btvars_typ (t:typ) =
//    match t.n with
//    | 


(* Looks for bound type variables in the type. If some are found, the related associated function or type declaration
    is not printed since it means that some polymortphism remains *)
let rec has_btvars_typ (t:typ) =
    let t = FStar.Absyn.Util.compress_typ t in
    match t.n with
    | Typ_btvar _ -> 
        begin
            Printf.printf "Found the following bound type var : %s, object will be ignored.\n" (Print.typ_to_string t);
            true
        end
    | Typ_const _ -> false
    | Typ_fun(binders, comp) ->
        let b1 = List.fold (fun b x -> has_btvars_binder x ||b) false binders in
        let b2 = has_btvars_comp comp in
        b1 ||b2
    | Typ_refine(bv, t') ->
        has_btvars_typ t'
    | Typ_app(t', args) ->
        List.fold (fun b x -> has_btvars_arg x || b) false args
    | Typ_lam(binders, t') -> 
        // TODO : check if correct
        has_btvars_typ t'
    | Typ_ascribed(t', knd) ->
        has_btvars_typ t'
    | Typ_meta(meta) -> 
        // TODO : check if correct
        begin
            match meta with 
            | Meta_pattern(t', args) -> has_btvars_typ t'
            | _ -> false
        end
    | Typ_uvar(uvar, knd) ->
        // TODO : implement
        false
    | Typ_delayed(t', _) ->
        // TODO : implement
        begin
            match t' with
            | Inl(ty, subst) -> 
                // Can this case happen while compress_typ has been called ?
                let ty = List.fold (fun t s -> FStar.Absyn.Util.subst_typ s t) ty subst in
                has_btvars_typ ty
            | Inr(ft) -> has_btvars_typ (ft())
        end
    | Typ_unknown -> 
        // TODO : failwith ?
        false

and has_btvars_binder (binder:binder) =
    // TODO : implement
    match binder with
    | Inl btv, _ -> false
    | Inr bvv, _ -> 
        let t = bvv.sort in
        has_btvars_typ t

and has_btvars_arg (arg:arg) =
    match arg with
    | Inl t, _ -> has_btvars_typ t
    | Inr e, _ -> false

and has_btvars_comp (c:comp) =
    match c.n with
    | Total t -> has_btvars_typ t
    | Comp c' -> has_btvars_typ c'.result_typ


let is_erasable_typ ty =
    match ty.n with
    | Typ_fun(binders, c) -> 
        begin
        if (Print.binders_to_string " " binders).Contains "projectee" then true else
        match c.n with
        | Total t -> 
            begin
            match t.n with
            | Typ_const v -> 
//                        Printf.printf "res type : %s \n" (Print.tag_of_typ t);
                if v.v.str = "Prims.unit" then true // 'a -> Tot unit functions are erased
                else false
            | _ -> false
            end
        | Comp c -> 
            let t = c.result_typ in
            let effect = c.effect_name in
            match t.n with
            | Typ_const v -> 
//                        Printf.printf "Full effect name : %s\n" effect.str;
                // GTot functions, lemmas and 'a -> Tot unit funtions are to be erased
                if List.contains effect.str ["Prims.GTot"; "Prims.Lemma"] || effect.str = "Prims.Tot" && v.v.str = "Prims.unit" 
                then true
                else false
            | _ -> false
        end
    
    // TODO : complete with other types to erase. E.g. : Typ_ascribed
    | _ -> false

(* Checks if the expression if a the application of a dataconstructor *)
let is_datactor e =
    match e.n with
    | Exp_app(e', args) ->
        begin
        match e'.n with
        | Exp_fvar(fv, quals) ->
            begin
                match quals with
                | Some Data_ctor -> true
                | _ -> false
            end
        | _ -> false
        end
    | _ -> false