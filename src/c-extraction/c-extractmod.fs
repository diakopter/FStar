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
module FStar.Extraction.C.ExtractMod
open FStar
open FStar.Util
open FStar.Absyn
open FStar.Absyn.Syntax

let rec extract_sig (* (g:env) *) (se:sigelt) : string (* env * list<mlmodule1> *) =

    let se = try FStar.Tc.Normalize.norm_sigelt !PrettyPrint.env se 
            with | ex -> 
                    Printf.printf "BACKEND WARNING :    Caught the following exception when normalizing : %s" (ex.ToString());
                    se in
     match se with
        | Sig_datacon _
        | Sig_bundle _
        | Sig_tycon _
        | Sig_typ_abbrev _ ->
            FStar.Extraction.C.ExtractTyp.extractSigElt se

        | Sig_let (lbs, r, _, quals) ->


          let elet = mk_Exp_let(lbs, Const.exp_false_bool) None r in

          let extracted_sig = PrettyPrint.pp_top_let elet quals in
            
          Printf.printf "\n%s\n" extracted_sig;
          extracted_sig


       | Sig_val_decl(lid, t, quals, r) ->

            let str = PrettyPrint.pp_fun_decl lid t + ";\n" in
            Printf.printf "%s\n" str;
            str

       | Sig_main(e, _) -> 
            (* TODO : implement this *)
            "int main(int argc, char *argv[]){\n\treturn 0;\n}\n\n"

       | Sig_kind_abbrev _ //not needed; we expand kind abbreviations while translating types
       | Sig_assume _ //not needed; purely logical

       | Sig_new_effect _
       | Sig_sub_effect  _
       | Sig_effect_abbrev _  //effects are all primitive; so these are not extracted; this may change as we add user-defined non-primitive effects
       | Sig_pragma _ -> //pragmas are currently not relevant for codegen; they may be in the future
            ""


let rec extract (* (g:env) *) (m:modul) : list<lident * string> (* env * list<mllib> *) =

    Util.reset_gensym();

    let name = m.name.str in
    Printf.printf "\nEntering module : %s\n" m.name.str;

    if List.contains m.name.str PrettyPrint.default_modules
    || m.is_interface
    || List.contains m.name.str !Options.admit_fsi
    then 
        []

    else 
        [m.name, List.fold (fun s x -> s + extract_sig x) "" m.declarations]

let format (m:lident * string) =
    let id = fst m in
    let name = id.ident.idText in
    let modul = snd m in
    (name, FSharp.Format.text modul)