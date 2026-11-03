(* Regression tests for the arity check between a type declaration and one use of it.

   Charon lifts each associated type named by a declaration's bounds into an extra type
   parameter ([Clause0_Output] and the like), so a use of that declaration has to carry one
   argument per parameter. A use can carry only the arguments the type itself declared -- one
   read from another crate's metadata is not lifted. The two lists then differ in length, and
   since [Charon.Substitute.make_subst_from_generics] zips them, [List.combine] raised
   [Invalid_argument("List.combine")] and one such use aborted the whole crate's extraction.

   The contract: the disagreement is reported, naming both lengths and what they describe,
   instead of reaching the zip. A declaration and a use that agree report nothing, so the
   check does not turn into a blanket error.

   Run with `dune build @runtest` from src/. *)

open Aeneas
open Types

let failures = ref 0

let report name = function
  | Ok note -> Printf.printf "PASS  %-52s %s\n" name note
  | Error note ->
      incr failures;
      Printf.printf "FAIL  %-52s %s\n" name note

let substring_at (haystack : string) (needle : string) (i : int) =
  String.length haystack - i >= String.length needle
  && String.sub haystack i (String.length needle) = needle

let contains (haystack : string) (needle : string) =
  let n = String.length haystack and m = String.length needle in
  let rec loop i = i + m <= n && (substring_at haystack needle i || loop (i + 1)) in
  m = 0 || loop 0

let ty_param (i : int) : Types.type_param =
  { index = TypeVarId.of_int i; name = "T" ^ string_of_int i; variance = Invariant }

let region_param (i : int) : Types.region_param =
  {
    index = RegionId.of_int i;
    name = Some ("'a" ^ string_of_int i);
    variance = Invariant;
    mutability = LtShared;
    late_bound = false;
  }

let const_generic_param (i : int) : Types.const_generic_param =
  {
    index = ConstGenericVarId.of_int i;
    name = "N" ^ string_of_int i;
    ty = TScalar (TInteger (Unsigned Usize));
  }

let no_regions : Types.generic_params =
  { regions = []; types = []; const_generics = []; trait_clauses = []; outlives = []; trait_type_constraints = [] }

let params_with_types (n : int) : Types.generic_params =
  { no_regions with types = List.init n ty_param }

let no_args : Types.generic_args =
  { regions = []; types = []; const_generics = []; trait_refs = [] }

let args_with_types (n : int) : Types.generic_args =
  let scalar = TScalar (TInteger (Signed Isize)) in
  { no_args with types = List.init n (fun _ -> scalar) }

let describe (mismatches : string list) =
  match mismatches with
  | [] -> "(none)"
  | _ -> String.concat "; " mismatches

let expect name (mismatches : string list) (check : string -> bool) (want : string) =
  if check (describe mismatches) then report name (Ok (describe mismatches))
  else report name (Error ("reported " ^ describe mismatches ^ ", expected " ^ want))

let has (s : string) (needle : string) = contains s needle

let () =
  (* The case that crashed: two declared type parameters, one argument. *)
  let lifted = TypesAnalysis.instantiation_arity_mismatches (params_with_types 2) (args_with_types 1) in
  expect "a lifted parameter the use does not supply" lifted
    (fun d -> has d "type parameters" && has d "declared 2" && has d "instantiated with 1")
    "type parameters: declared 2, instantiated with 1";

  (* The other direction is just as unzippable, and says so. *)
  expect "an argument the declaration does not have"
    (TypesAnalysis.instantiation_arity_mismatches (params_with_types 1) (args_with_types 2))
    (fun d -> has d "declared 1" && has d "instantiated with 2")
    "type parameters: declared 1, instantiated with 2";

  (* Agreement is not an error: the substitution is built as before. *)
  expect "matching parameters report nothing"
    (TypesAnalysis.instantiation_arity_mismatches (params_with_types 2) (args_with_types 2))
    (fun d -> d = "(none)") "(none)";

  (* Every list the substitution zips is checked, not only the type parameters. *)
  let regions = { no_regions with regions = List.init 2 region_param } in
  let regions_one_arg : Types.generic_args = { no_args with regions = [ RErased ] } in
  expect "...region parameters too"
    (TypesAnalysis.instantiation_arity_mismatches regions regions_one_arg)
    (fun d -> has d "region parameters" && has d "declared 2" && has d "instantiated with 1")
    "region parameters: declared 2, instantiated with 1";
  let cgs = { no_regions with const_generics = [ const_generic_param 0 ] } in
  expect "...const generic parameters too"
    (TypesAnalysis.instantiation_arity_mismatches cgs no_args)
    (fun d -> has d "const generic parameters" && has d "declared 1" && has d "instantiated with 0")
    "const generic parameters: declared 1, instantiated with 0";

  if !failures = 0 then (
    Printf.printf "\ninstantiation arity: all contracts hold\n";
    exit 0)
  else (
    Printf.printf "\ninstantiation arity: %d contract(s) broken\n" !failures;
    exit 1)
