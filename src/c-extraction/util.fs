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