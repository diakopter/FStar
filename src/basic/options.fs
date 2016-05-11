(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

// (c) Microsoft Corporation. All rights reserved
module FStar.Options
open FStar
open FStar.Util
open FStar.Getopt
open FStar.Version

type debug_level_t =
    | Low
    | Medium
    | High
    | Extreme
    | Other of string

let show_signatures : ref<list<string>> = Util.mk_ref []
let norm_then_print = Util.mk_ref true
let z3_exe = Util.mk_ref (Platform.exe "z3")
let silent=Util.mk_ref false
let debug : ref<list<string>> = Util.mk_ref []
let debug_level : ref<list<debug_level_t>> = Util.mk_ref []
let dlevel = function
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq l1 l2 = match l1 with
    | Other _
    | Low -> l1 = l2
    | Medium -> (l2 = Low || l2 = Medium)
    | High -> (l2 = Low || l2 = Medium || l2 = High)
    | Extreme -> (l2 = Low || l2 = Medium || l2 = High || l2 = Extreme)
let debug_level_geq l2 = !debug_level |> Util.for_some (fun l1 -> one_debug_level_geq l1 l2)
let log_types = Util.mk_ref false
let print_effect_args=Util.mk_ref false
let print_real_names = Util.mk_ref false
let detail_errors = Util.mk_ref false
let dump_module : ref<option<string>> = Util.mk_ref None
let should_dump l = match !dump_module with
    | None -> false
    | Some m -> m=l
let __test_norm_all = Util.mk_ref false
let logQueries = Util.mk_ref false
let z3exe = Util.mk_ref true
let outputDir = Util.mk_ref (Some ".")
let fstar_home_opt : ref<option<string>> = Util.mk_ref None
let _fstar_home = Util.mk_ref ""
let prims_ref : ref<option<string>> = Util.mk_ref None
let z3timeout = Util.mk_ref 5
let admit_smt_queries = Util.mk_ref false
let pretype = Util.mk_ref true
let codegen : ref<option<string>> = Util.mk_ref None
let no_extract : ref<list<string>> = Util.mk_ref []
let no_location_info = Util.mk_ref false
let codegen_libs : ref<list<list<string>>> = Util.mk_ref []
let trace_error = Util.mk_ref false
let verify = Util.mk_ref true
let full_context_dependency = Util.mk_ref true
let ml_ish = Util.mk_ref false
let print_implicits = Util.mk_ref false
let print_bound_var_types = Util.mk_ref false
let print_universes = Util.mk_ref false
let hide_uvar_nums = Util.mk_ref false
let hide_genident_nums = Util.mk_ref false
let serialize_mods = Util.mk_ref false
let initial_fuel = Util.mk_ref 2
let initial_ifuel = Util.mk_ref 1
let max_fuel = Util.mk_ref 8
let min_fuel = Util.mk_ref 1
let max_ifuel = Util.mk_ref 2
let warn_top_level_effects = Util.mk_ref false
let no_slack = Util.mk_ref false
let eager_inference = Util.mk_ref false
let universes = Util.mk_ref false
let unthrottle_inductives = Util.mk_ref false
let use_eq_at_higher_order = Util.mk_ref false
let use_native_int = Util.mk_ref false
let fs_typ_app = Util.mk_ref false
let n_cores = Util.mk_ref 1
let verify_module : ref<list<string>> = Util.mk_ref [] // all normalized to lowercase
let __temp_no_proj : ref<list<string>> = Util.mk_ref []
let interactive = Util.mk_ref false
let split_cases = Util.mk_ref 0
let _include_path : ref<list<string>> = Util.mk_ref []
let no_default_includes = Util.mk_ref false
let interactive_fsi = Util.mk_ref false
let print_fuels = Util.mk_ref false
let cardinality = Util.mk_ref "off"
let timing = Util.mk_ref false
let inline_arith = Util.mk_ref false
let warn_cardinality () = match !cardinality with
    | "warn" -> true
    | _ -> false
let check_cardinality () = match !cardinality with
    | "check" -> true
    | _ -> false
let dep : ref<option<string>> = Util.mk_ref None
let explicit_deps = Util.mk_ref false
let init_options () =
    show_signatures := [];
    norm_then_print := true;
    z3_exe := Platform.exe "z3";
    silent := false;
    debug := [];
    debug_level  := [];
    log_types  := false;
    print_effect_args := false;
    print_real_names  := false;
    dump_module  := None;
    logQueries  := false;
    z3exe  := true;
    outputDir  := Some ".";
    fstar_home_opt  := None;
    _fstar_home  := "";
    prims_ref  := None;
    z3timeout  := 5;
    admit_smt_queries := false;
    pretype  := true;
    codegen  := None;
    codegen_libs := [];
    no_extract  := [];
    trace_error  := false;
    verify  := true;
    full_context_dependency  := true;
    print_implicits  := false;
    print_bound_var_types := false;
    print_universes := false;
    hide_uvar_nums  := false;
    hide_genident_nums  := false;
    serialize_mods  := false;
    initial_fuel  := 2;
    initial_ifuel  := 1;
    max_fuel  := 8;
    min_fuel  := 1;
    max_ifuel  := 2;
    warn_top_level_effects  := false;
    no_slack  := false;
    eager_inference  := false;
    unthrottle_inductives  := false;
    use_eq_at_higher_order  := false;
    fs_typ_app  := false;
    n_cores  := 1;
    split_cases := 0;
    verify_module := [];
    __temp_no_proj := [];
    _include_path := [];
    no_default_includes := false;
    print_fuels := false;
    use_native_int := false;
    explicit_deps := false;
    dep := None;
    timing := false;
    inline_arith := false;
    detail_errors := false;
    ml_ish := false

let set_fstar_home () =
  let fh = match !fstar_home_opt with
    | None ->
      let x = Util.get_exec_dir () in
      let x = x ^ "/.." in
      _fstar_home := x;
      fstar_home_opt := Some x;
      x
    | Some x -> _fstar_home := x; x in
  fh
let get_fstar_home () = match !fstar_home_opt with
    | None -> ignore <| set_fstar_home(); !_fstar_home
    | Some x -> x

let include_path_base_dirs = 
  ["/lib"; "/lib/fstar"; "/stdlib" ; "/stdlib/fstar"]

let universe_include_path_base_dirs = 
  ["/ulib"]

let get_include_path () =
  (* Allows running fstar either from the source repository, or after
   * installation (into /usr/local for instance) *)
  if !no_default_includes then
    !_include_path
  else
  let h = get_fstar_home () in
  let defs = if !universes then universe_include_path_base_dirs else include_path_base_dirs in
  (defs |> List.map (fun x -> h ^ x) |> List.filter file_exists) @ !_include_path @ [ "." ]

let find_file filename =
    let search_path = get_include_path () in
    try
      Util.map_option
        Util.normalize_file_path
        (if Util.is_path_absolute filename then
          if Util.file_exists filename then
            Some filename
          else
            None
        else
          Util.find_map
            search_path
            (fun p ->
              let path = Util.join_paths p filename in
              if Util.file_exists path then
                Some path
              else
                None))
    with _ ->
      None

let prims () = match !prims_ref with
  | None ->
    (let filen = "prims.fst" in
    match find_file filen with
    | Some result ->
      result
    | None ->
      raise (Util.Failure (Util.format1 "unable to find required file \"%s\" in the module search path.\n" filen)))
  | Some x -> x

let prependOutputDir fname = match !outputDir with
  | None -> fname
  | Some x -> x ^ "/" ^ fname

let display_version () =
  Util.print_string (Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n"
                                  version platform compiler date commit)

let display_usage specs =
  Util.print_string "fstar [option] file...\n";
  List.iter
    (fun (_, flag, p, doc) ->
       match p with
         | ZeroArgs ig ->
             if doc = "" then Util.print_string (Util.format1 "  --%s\n" (Util.colorize_bold flag))
             else Util.print_string (Util.format2 "  --%s  %s\n" (Util.colorize_bold flag) doc)
         | OneArg (_, argname) ->
             if doc = "" then Util.print_string (Util.format2 "  --%s %s\n" (Util.colorize_bold flag) (Util.colorize_bold argname))
             else Util.print_string (Util.format3 "  --%s %s  %s\n" (Util.colorize_bold flag) (Util.colorize_bold argname) doc))
    specs

let rec specs () : list<Getopt.opt> =
  let specs =
    [( noshort, "admit_smt_queries", OneArg ((fun s -> admit_smt_queries := (if s="true" then true else if s="false" then false else failwith("Invalid argument to --admit_smt_queries"))), "true|false"), "Admit SMT queries (UNSAFE! But, useful during development); default: 'false'");
     ( noshort, "cardinality", OneArg ((fun x -> cardinality := validate_cardinality x), "off|warn|check"), "Check cardinality constraints on inductive data types (default 'off')");
     ( noshort, "codegen", OneArg ((fun s -> codegen := parse_codegen s), "OCaml|FSharp"), "Generate code for execution");
     ( noshort, "codegen-lib", OneArg ((fun s -> codegen_libs := (Util.split s ".")::!codegen_libs), "namespace"), "External runtime library library");
     ( noshort, "debug", OneArg ((fun x -> debug := x::!debug), "module name"), "Print LOTS of debugging information while checking module [arg]");
     ( noshort, "debug_level", OneArg ((fun x -> debug_level := dlevel x::!debug_level), "Low|Medium|High|Extreme"), "Control the verbosity of debugging info");
     ( noshort, "dep", OneArg ((fun x -> dep := Some x), "make"), "Output the transitive closure of the dependency graph in a format suitable for the given tool");
     ( noshort, "detail_errors", ZeroArgs (fun () -> detail_errors := true; n_cores := 1),  "Emit a detailed error report by asking the SMT solver many queries; will take longer; implies n_cores=1; requires --universes");
     ( noshort, "dump_module", OneArg ((fun x -> dump_module := Some x), "module name"), "");
     ( noshort, "eager_inference", ZeroArgs (fun () -> eager_inference := true), "Solve all type-inference constraints eagerly; more efficient but at the cost of generality");
     ( noshort, "explicit_deps", ZeroArgs (fun () -> explicit_deps := true), "tell FStar to not find dependencies automatically because the user provides them on the command-line");
     ( noshort, "fs_typ_app", ZeroArgs (fun () -> fs_typ_app := true), "Allow the use of t<t1,...,tn> syntax for type applications; brittle since it clashes with the integer less-than operator");
     ( noshort, "fsi", ZeroArgs (fun () -> set_interactive_fsi ()), "fsi flag; A flag to indicate if type checking a fsi in the interactive mode");
     ( noshort, "fstar_home", OneArg ((fun x -> fstar_home_opt := Some x), "dir"), "Set the FSTAR_HOME variable to dir");
     ( noshort, "hide_genident_nums", ZeroArgs(fun () -> hide_genident_nums := true), "Don't print generated identifier numbers");
     ( noshort, "hide_uvar_nums", ZeroArgs(fun () -> hide_uvar_nums := true), "Don't print unification variable numbers");
     ( noshort, "in", ZeroArgs (fun () -> interactive := true), "Interactive mode; reads input from stdin");
     ( noshort, "include", OneArg ((fun s -> _include_path := !_include_path @ [s]), "path"), "A directory in which to search for files included on the command line");
     ( noshort, "initial_fuel", OneArg((fun x -> initial_fuel := int_of_string x), "non-negative integer"), "Number of unrolling of recursive functions to try initially (default 2)");
     ( noshort, "initial_ifuel", OneArg((fun x -> initial_ifuel := int_of_string x), "non-negative integer"), "Number of unrolling of inductive datatypes to try at first (default 1)");
     ( noshort, "inline_arith", ZeroArgs(fun () -> inline_arith := true), "Inline definitions of arithmetic functions in the SMT encoding");
     ( noshort, "lax", ZeroArgs (fun () -> pretype := true; verify := false), "Run the lax-type checker only (admit all verification conditions)");
     ( noshort, "log_types", ZeroArgs (fun () -> log_types := true), "Print types computed for data/val/let-bindings");
     ( noshort, "log_queries", ZeroArgs (fun () -> logQueries := true), "Log the Z3 queries in queries.smt2");
     ( noshort, "max_fuel", OneArg((fun x -> max_fuel := int_of_string x), "non-negative integer"), "Number of unrolling of recursive functions to try at most (default 8)");
     ( noshort, "max_ifuel", OneArg((fun x -> max_ifuel := int_of_string x), "non-negative integer"), "Number of unrolling of inductive datatypes to try at most (default 2)");
     ( noshort, "min_fuel", OneArg((fun x -> min_fuel := int_of_string x), "non-negative integer"), "Minimum number of unrolling of recursive functions to try (default 1)");
     ( noshort, "MLish", ZeroArgs(fun () -> ml_ish := true; full_context_dependency := false), "Introduce unification variables that are only dependent on the type variables in the context");
     ( noshort, "n_cores", OneArg ((fun x -> n_cores := int_of_string x; detail_errors := false), "positive integer"), "Maximum number of cores to use for the solver (default 1); implied detail_errors = false");
     ( noshort, "no_default_includes", ZeroArgs (fun () -> no_default_includes := true), "Ignore the default module search paths");
     ( noshort, "no_extract", OneArg ((fun x -> no_extract := x::!no_extract), "module name"), "Do not extract code from this module");
     ( noshort, "no_location_info", ZeroArgs (fun () -> no_location_info := true), "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)");
     ( noshort, "odir", OneArg ((fun x -> outputDir := Some x), "dir"), "Place output in directory dir");
     ( noshort, "prims", OneArg ((fun x -> prims_ref := Some x), "file"), "");
     ( noshort, "print_before_norm", ZeroArgs(fun () -> norm_then_print := false), "Do not normalize types before printing (for debugging)");
     ( noshort, "print_bound_var_types", ZeroArgs(fun () -> print_bound_var_types := true), "Print the types of bound variables");
     ( noshort, "print_effect_args", ZeroArgs (fun () -> print_effect_args := true), "Print inferred predicate transformers for all computation types");
     ( noshort, "print_fuels", ZeroArgs (fun () -> print_fuels := true), "Print the fuel amounts used for each successful query");
     ( noshort, "print_implicits", ZeroArgs(fun () -> print_implicits := true), "Print implicit arguments");
     ( noshort, "print_universes", ZeroArgs(fun () -> print_universes := true), "Print universes");
     ( noshort, "prn", ZeroArgs (fun () -> print_real_names := true), "Print real names---you may want to use this in conjunction with log_queries");
     ( noshort, "show_signatures", OneArg((fun x -> show_signatures := x::!show_signatures), "module name"), "Show the checked signatures for all top-level symbols in the module");
     ( noshort, "silent", ZeroArgs (fun () -> silent := true), " ");
     ( noshort, "smt", OneArg ((fun x -> z3_exe := x), "path"), "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)");
     ( noshort, "split_cases", OneArg ((fun n -> split_cases := int_of_string n), "t"), "Partition VC of a match into groups of n cases");
     ( noshort, "timing", ZeroArgs (fun () -> timing := true), "Print the time it takes to verify each top-level definition");
     ( noshort, "trace_error", ZeroArgs (fun () -> trace_error := true), "Don't print an error message; show an exception trace instead");
     ( noshort, "universes", ZeroArgs (fun () -> universes := true), "Use the (experimental) support for universes");
     ( noshort, "unthrottle_inductives", ZeroArgs (fun () -> unthrottle_inductives := true), "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)");
     ( noshort, "use_eq_at_higher_order", ZeroArgs (fun () -> use_eq_at_higher_order := true), "Use equality constraints when comparing higher-order types; temporary");
     ( noshort, "use_native_int", ZeroArgs (fun () -> use_native_int := true), "Extract the 'int' type to platform-specific native int; you will need to link the generated code with the appropriate version of the prims library");
     ( noshort, "verify_module", OneArg ((fun x -> verify_module := (String.lowercase x)::!verify_module), "string"), "Name of the module to verify");
     ( noshort, "__temp_no_proj", OneArg ((fun x -> __temp_no_proj := x::!__temp_no_proj), "string"), "Don't generate projectors for this module");
     ( 'v',     "version", ZeroArgs (fun _ -> display_version(); exit 0), "Display version number");
     ( noshort, "warn_top_level_effects", ZeroArgs (fun () -> warn_top_level_effects := true), "Top-level effects are ignored, by default; turn this flag on to be warned when this happens");
     ( noshort, "z3timeout", OneArg ((fun s -> z3timeout := int_of_string s), "t"), "Set the Z3 per-query (soft) timeout to t seconds (default 5)");
  ] in
     ( 'h', "help", ZeroArgs (fun x -> display_usage specs; exit 0), "Display this information")::specs
and parse_codegen s =
  match s with
  | "OCaml"
  | "FSharp" -> Some s
  | _ ->
     (Util.print_string "Wrong argument to codegen flag\n";
      display_usage (specs ()); exit 1)

and validate_cardinality x = match x with
    | "warn"
    | "check"
    | "off" -> x
    | _ ->   (Util.print_string "Wrong argument to cardinality flag\n";
              display_usage (specs ()); exit 1)

and set_interactive_fsi _ =
    if !interactive then interactive_fsi := true
    else (Util.print_string "Set interactive flag first before setting interactive fsi flag\n";
          display_usage (specs ()); exit 1)

let should_verify m =
  if !verify
  then match !verify_module with
    | [] -> true //the verify_module flag was not set, so verify everything
    | l -> List.contains (String.lowercase m) l //otherwise, look in the list to see if it is explicitly mentioned
  else false

let dont_gen_projectors m = List.contains m (!__temp_no_proj)

let should_print_message m =
    if should_verify m
    then m <> "Prims"
    else false

type options = 
    | Set
    | Reset
    | Restore

let set_options =
    //Several options can only be set at the time the process is created, and not controlled interactively via pragmas
    //Additionaly, the --smt option is a security concern
    let settable = function
      | "admit_smt_queries"
      | "cardinality"
      | "debug"
      | "debug_level"
      | "detail_errors"
      | "eager_inference"
      | "hide_genident_nums"
      | "hide_uvar_nums"
      | "initial_fuel"
      | "initial_ifuel"
      | "inline_arith"
      | "lax"
      | "log_types"
      | "log_queries"
      | "max_fuel"
      | "max_ifuel"
      | "min_fuel"
      | "print_before_norm"
      | "print_bound_var_types"
      | "print_effect_args"
      | "print_fuels"
      | "print_implicits"
      | "print_universes"
      | "prn"
      | "show_signatures"
      | "silent"
      | "split_cases"
      | "timing"
      | "trace_error"
      | "unthrottle_inductives"
      | "use_eq_at_higher_order"
      | "__temp_no_proj"
      | "warn_top_level_effects" -> true
      | _ -> false in
    let resettable s = settable s || s="z3timeout" in
    let all_specs = specs () in
    let settable_specs = all_specs |> List.filter (fun (_, x, _, _) -> settable x) in
    let resettable_specs = all_specs |> List.filter (fun (_, x, _, _) -> resettable x) in
    fun o s -> 
        let specs = match o with 
            | Set -> settable_specs
            | Reset -> resettable_specs
            | Restore -> all_specs in
        Getopt.parse_string specs (fun _ -> ()) s

let restore_cmd_line_options () =
    (* Some options must be preserved because they can't be reset via #pragrams.
     * Add them here as needed. *)
    let old_verify_module = !verify_module in
    init_options();
    let r = Getopt.parse_cmdline (specs()) (fun x -> ()) in
    verify_module := old_verify_module;
    r
