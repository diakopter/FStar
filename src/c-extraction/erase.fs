module FStar.Extraction.C.Erasure

open FStar
open FStar.Util
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Extraction.C.Util

#light "off"

// Functions to be ignored
// TODO : extend, complete ...
let erase_default = ["Prims.erase"; "Prims.admit"; "Prims.cut"; "Prims.admitP"; "Prims.assert"; "Prims._assert"]

// Effects to be erased
let effects_to_erase = ["Prims.GTot"; "Prims.Lemma"]

type erasure_context = {
    erased_fun:list<lident>;
    erased_binders:list<string>;
}

let mk_erasure_context () = { erased_fun = []; erased_binders = []}

let add_erased_fun_to_context ctx lid = 
    let erased_fun = ctx.erased_fun in
    if List.exists (fun x -> x.str = lid.str) erased_fun then ctx
    else { ctx with erased_fun = lid::ctx.erased_fun }
let add_erased_binder_to_context ctx str = 
    let erased_binders = ctx.erased_binders in
    if List.contains str erased_binders then ctx
    else { ctx with erased_binders = str::ctx.erased_binders }

(* Erase part of an expression based on previously collected erasable values *)
let rec erase_exp (context:erasure_context) (e:exp) =
    let previous_context = context in
    let exp_opt =
        match e.n with
        | Exp_bvar bv -> 
            // Check if the bound var should be removed
            if List.contains bv.v.realname.idText context.erased_binders 
            then None
            else Some e
        | Exp_app(e', args) ->
            begin
                match erase_exp context e' with
                | None -> None
                | Some v -> 
                    let new_args = List.map (erase_arg context) args in
                    let new_args = List.map (fun x -> match x with | None -> Inr (mk_unit_val()), None | Some t -> t) new_args in
                    Some ({ e with n = Exp_app(v, new_args) })
            end
        // TODO : complete with other possible expressions, e.g. : Exp_let
        | _ -> Some e in
    exp_opt

(* Erases the irrelevant arguments *)
and erase_arg (context:erasure_context) (arg:arg) =
    match arg with 
    | Inl t, qual -> 
        begin
            match erase_typ context t with
            | Some v -> Some (Inl v, qual)
            | None -> None 
        end
    | Inr e, qual ->
        begin
            match erase_exp context e with
            | Some v -> Some (Inr v, qual)
            | None -> None
        end

(* Erases the irrelevant types *)
and erase_typ (context:erasure_context) (t:typ) =
    match t.n with
    | _ -> Some t

(* Erases the irrelevant letbindings *)
let erase_letbinding (context:erasure_context) (lb:letbinding) =
    let effect = lb.lbeff in

    if List.contains effect.str effects_to_erase || is_erasable_typ lb.lbtyp
    then 
        match lb.lbname with
        | Inl bvd -> 
            let name = bvd.realname.idText in
            let context = add_erased_binder_to_context context name in
            context, None
        | Inr id ->
            let context = add_erased_fun_to_context context id in
            context, None
    else
        match lb.lbname with
        | Inl bvd -> 
            begin
                let def = erase_exp context lb.lbdef in
                match def with
                | Some d -> context, Some { lb with lbdef = d }
                | _ -> context, None
            end
        | Inr id -> 
            if List.exists (fun x -> id.str = x.str) context.erased_fun then context, None
            else 
                let def = erase_exp context lb.lbdef in
                match def with
                | Some d -> context, Some { lb with lbdef = d }
                | _ -> context, None

(* Analyses and erases sigelts depending on their type *)
let erase_sigelt (context:erasure_context) (sigelt:sigelt) =
    match sigelt with
    | Sig_val_decl(lid, ty, quals, r) -> 
        Printf.printf "type of %s is %s\n" lid.str (Print.typ_to_string ty);
        if is_erasable_typ ty then
            let context = add_erased_fun_to_context context lid in
            context, None
        else context, Some sigelt
    | Sig_let(lbs, r, lids, quals) -> 
        begin 
            if List.contains Logic quals then 
                let ids = lids_from_toplet sigelt in
                let context = List.fold add_erased_fun_to_context context ids in
                context, None
            else (
                Printf.printf "Sigelt : %s\n" (Print.sigelt_to_string_short sigelt);
                Printf.printf "Letbindings : %s\n" (List.fold (fun s x -> s + " " + (Print.lbname_to_string x.lbname)) "" (snd lbs));
                Printf.printf "Lids : %s\n" (List.fold (fun s x -> s + " " + (Print.sli x)) "" lids);
                Printf.printf "Quals : %s\n" (Print.quals_to_string quals);
                let context, lbs_opt = Util.fold_map erase_letbinding context (snd lbs) in
                let lbs_opt = List.map2 (fun x y -> if contains_lid x context.erased_fun then None else y) 
                                        lids
                                        lbs_opt in
                let lids_opt = List.map2 (fun x y -> match x with | None -> None | _ -> Some y) lbs_opt lids in
                let new_lbs = filter lbs_opt in
                let new_lids = filter lids_opt in
                match new_lbs with
                | [] -> 
                    let context = List.fold (add_erased_fun_to_context) context lids in
                    context, None
                | _ -> context, Some (Sig_let((fst lbs, new_lbs), r, new_lids, quals)) )
        end
    | _ -> context, Some sigelt


(* Simple erasing procedure to remove declarations which are considered irrelevant for the C backend *)
let erase_declarations (context:erasure_context) (m:modul) =
    let context, decls = Util.fold_map (fun ctx s -> erase_sigelt ctx s) context m.declarations in
    let decls = List.fold (fun l x -> match x with | Some t -> l@[t] | _ -> l) [] decls in
    context, { m with declarations = decls }

