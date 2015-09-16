(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
module FStar.Extraction.C.ExtractTyp
open Prims
open FStar.Absyn
open FStar.Util
open FStar.Tc.Env
open FStar.Absyn.Syntax
open FStar
open FStar.Tc.Normalize
open FStar.Absyn.Print


let rec extractSigElt (* (c:context) *)  (s:sigelt) : string (* context * list<mlmodule1> *) =
    match s with
    | Sig_typ_abbrev (l,bs,_,t,_,_) ->

        // C pretty printing
        let str = "" in
        let str = str + "Sig_typ_abbrev printed : \n" in
        let str = str + Print.sigelt_to_string s + "\n" in
        print_string str;
        str


    | Sig_bundle(sigs, [ExceptionConstructor], _, _) -> 
        
        // C pretty printing
        let str = "" in
        let str = str + "Sig_bundle exception printed : \n" in
        let str = str + Print.sigelt_to_string s + "\n" in
        print_string str;
        str


    | Sig_bundle (sigs, _, _ ,_) -> 
        //let xxxx = List.map (fun se -> fprint1 "%s\n" (Util.format1 "sig bundle: : %s\n" (Print.sigelt_to_string se))) sigs in
//        let (typ_map: Map<string, (string * (string * string) list) list> ref) = ref Map.empty in
//
//        let str = ref "" in
//
//        let handle_binder is_arrow (binder:Syntax.binder) =
//            match binder with
//            | Inl a, imp -> if is_null_binder binder
//                    then ("/!\ no binder", Print.kind_to_string a.sort)
//                    else if not is_arrow then ("/!\ no binder", imp_to_string (strBvd a.v) imp) // ==> may need a pointer
//                    else (Print.strBvd a.v , Print.kind_to_string a.sort)
//            | Inr x, imp -> if is_null_binder binder
//                    then ("/!\ no binder", typ_to_string x.sort)
//                    else if not is_arrow then ("/!\ no binder", imp_to_string (strBvd x.v) imp)
//                    else ((strBvd x.v) ,(PrettyPrint.pp_typ x.sort)) in
//
//        let handle_binders is_arrow binders =
//            List.map (handle_binder is_arrow) binders in
//
//        let handle_data_con dcon =
//            match dcon with 
//            | Sig_datacon(lid, t, _, _, _, _) -> 
//                begin
//                    let id = lid.str in
//                    let typ = Util.compress_typ t in
//                    match typ.n with
//                    | Typ_fun(binders, c) ->
//                        (
//                        match c.n with
//                        | Total t' ->
//                            Some (PrettyPrint.pp_typ t', (id, handle_binders true binders))
//                        | Comp c' -> 
//                            Printf.printf "\nComp type : %s \n" (PrettyPrint.pp_typ c'.result_typ);
//                            None
//                        )
//                    | Typ_const v -> 
//                        Some (PrettyPrint.pp_typ t, (id, ["NULL", "void"]))
//                    | Typ_delayed _ -> print_string "Type_delayed\n"; None
//                    | Typ_meta(Meta_named(_, l)) -> print_string "Typ_meta\n"; None
//                    | Typ_meta meta ->  print_string "Typ_meta\n"; None
//                    | Typ_btvar btv ->print_string "Typ_btvar\n"; None
//                    | Typ_refine(xt, f) ->print_string "Typ_refine\n"; None
//                    | Typ_app(_, []) -> failwith "Empty args!"
//                    | Typ_app(t, args) -> print_string "Typ_app\n"; None
//                    | Typ_lam(binders, t2) ->  print_string "Typ_lam\n"; None
//                    | Typ_ascribed(t, k) ->print_string "Typ_ascribed\n"; None
//                    | _ -> None
//                end
//            | _ -> None in
//
//        let rec handle_bundle s res =
//            match s with
//            | [] -> res
//            | x::tl ->
//                match x with
//                | Sig_datacon(_,_,_,_,_,_) -> 
//                    begin
//                        match handle_data_con x with
//                        | Some v -> 
//                            if Map.containsKey (fst v) !typ_map
//                            then
//                                let old_val = Map.find (fst v) !typ_map in 
//                                typ_map := Map.add (fst v) (old_val@[snd v]) !typ_map
//                            else
//                                typ_map := Map.add (fst v) ([snd v]) !typ_map;
//                            handle_bundle tl res
//                        | None -> 
//                            handle_bundle tl res
//                    end
//                | _ -> 
//                    Printf.printf "\n/!\\%s\n" (sigelt_to_string x);
//                    handle_bundle tl res in
//
//        let sig_bundle = handle_bundle sigs [] in
//
//        let union_list = ref [] in
//        let struct_list = ref [] in
//        for top, typ_list in Map.toList !typ_map do
//            if List.length typ_list > 1 
//            then 
//                begin
//                    let s = Util.format1 "union %s;\n" top in
//                    str := !str + s;
//                    print_string s;
//                    union_list := top::!union_list;
//                end
//            else 
//                begin
//                    let s = Util.format1 "struct %s;\n" top in
//                    str := !str + s;
//                    print_string s;
//                    struct_list := top::!struct_list;
//                end 
//        done;
//
//        for top, typ_list in Map.toList !typ_map do
//            if List.length typ_list > 1 
//            then 
//                begin
//                    for (id, types) in typ_list do
//                        let s = Util.format1 "\nstruct %s {\n" (id.Replace('.', '_')) in
//                        str := !str + s;
//                        print_string s;
//                        let var_list = ref [] in
//                        for binder,typ in types do
//                            if typ = "Type" then var_list := binder::!var_list
//                            else 
////                                 let ty = (typ.Split [|' '|]).[0] in
////                                if List.mem ty !var_list then Printf.printf"\t%s %s;\n" "void*" binder
//
//                                // Check for a pointer type
//                                if String.length typ >= 5 && typ.Substring(0,5) = "(ptr " then (
//                                    let typ = typ.Replace("(ptr ", "(") + "*" in
//                                    let s = Util.format2 "\t%s %s;\n" typ binder in
//                                    str := !str + s;
//                                    print_string s;
//                                )
//                                else if List.mem typ !union_list then begin 
//                                    let s = Util.format2 "\tunion %s %s;\n" typ binder in
//                                    str := !str + s;
//                                    print_string s; end
//                                else if List.mem typ !struct_list then begin
//                                    let s = Util.format2 "\tstruct %s %s;\n" typ binder in
//                                    str := !str + s;
//                                    print_string s end
//                                else begin
//                                    let s = Util.format2 "\t%s %s;\n" typ binder in
//                                    str := !str + s;
//                                    print_string s end
//                        done;
//                        let s = "};\n\n" in
//                        str := ! str + s;
//                        print_string s;
//                    done;   
//                end
//        done;
//
//        for top, typ_list in Map.toList !typ_map do
//            if List.length typ_list > 1 
//            then 
//                begin
//                    let s = Util.format1 "union %s{\n" top in
//                    str := !str + s;
//                    print_string s;
//                    for (id, types) in typ_list do
//                        let short_id = let v = id.Split [|'.'|] in v.[Array.length v - 1] in
//                        let s = Util.format2 "\tstruct %s %s;\n" (id.Replace('.', '_')) short_id in
//                        str := !str + s;
//                        print_string s;
//                    done;   
//                    let s = "};\n\n" in
//                    str := !str + s;
//                    print_string s;
//            end
//            else 
//                begin
//                    let s = Util.format1 "struct %s{\n" top in
//                    str := !str + s;
//                    print_string s;
//                    for (id, types) in typ_list do
//                        let var_list = ref [] in
//                        for binder,typ in types do
//                            if typ = "Type" then var_list := binder::!var_list
//                            else 
//                                // Check for a pointer type
//                                if String.length typ >= 5 && typ.Substring(0,5) = "(ptr " then (
//                                    let typ = typ.Replace("(ptr ", "(") + "*" in
//                                    let s = Util.format2 "\t%s %s;\n" typ binder in
//                                    str := !str + s;
//                                    print_string s;
//                                )
//                                else if List.mem typ !union_list then begin
//                                    let s = Util.format2 "\tunion %s %s;\n" typ binder in
//                                    str := !str + s;
//                                    print_string s; end
//                                else if List.mem typ !struct_list then begin
//                                    let s = Util.format2 "\tstruct %s %s;\n" typ binder in
//                                    str := !str + s;
//                                    print_string s; end
//                                else begin
//                                    let s = Util.format2 "\t%s %s;\n" typ binder in
//                                    str := !str + s;
//                                    print_string s; end
//                        done;
//                    done;   
//                    let s = "};\n\n" in
//                    str := !str + s;
//                    print_string s;
//                end
//        done;
        let str = PrettyPrint.pp_bundle sigs in
        str

    | Sig_tycon (l, binders, _, _, _, quals, _) -> 
        
        // C pretty printing
        let info = "" in
        let info = info + "Sig_tycon printed : \n" in
        let info = info + Print.sigelt_to_string s + "\n" in
       
        print_string (info);
        ""

    | _ -> 
                
        // C pretty printing
        let info = "" in
        let info = info + "Sig_? printed : \n" in
        let info = info + Print.sigelt_to_string s + "\n" in
        ""
