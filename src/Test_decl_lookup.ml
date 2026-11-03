(* A lookup of a translated declaration that misses must name what it wanted.

   A declaration map is keyed by an id the LLBC hands us, and the entry may be
   absent: the item can be outside the extracted set, or dropped because its own
   translation failed. `Decl_lookup.decl_lookup` is the seam those lookups go
   through, so a miss has to be a reported failure *naming the declaration*
   rather than a `Not_found` that aborts the file and names nothing.

   These cases pin the message and the three answers, so an edit cannot quietly
   restore a blind `Map.find` behind the helper.

   Run with `dune build @runtest` from src/. *)

let failures = ref 0

open Aeneas

let expect (what : string) (expected : string) (actual : string) =
  if expected <> actual then begin
    incr failures;
    Printf.printf "FAIL  %-52s expected %S got %S\n" what expected actual
  end
  else Printf.printf "PASS  %-52s %s\n" what actual

(* A declaration map, stood in for by an association list: the helpers take the
   lookup itself, so a case needs no crate behind it. *)
let decls = [ (7, "seven") ]
let lookup id = List.assoc_opt id decls

let what = "the type declaration of"
let name = "a.B"

let () =
  (* 1. A declaration the map does carry is returned unchanged. *)
  expect "a present declaration is returned" "seven"
    (Decl_lookup.decl_lookup "t.ml" 1 None ~what ~name lookup 7);

  (* 2. A missing declaration is reported, and the report names it. This is the
     case that used to escape as a bare [Not_found]. *)
  let raised =
    try
      ignore
        (Decl_lookup.decl_lookup "t.ml" 1 None ~what ~name lookup 9);
      "<no exception>"
    with
    | Errors.CFailure e -> e.msg
    | Not_found -> "<Not_found>"
    | e -> "<" ^ Printexc.to_string e ^ ">"
  in
  expect "a missing declaration is a reported failure"
    (Decl_lookup.msg ~what ~name)
    raised;
  expect "the report says what could not be found"
    "the type declaration of 'a.B' is not part of the translation"
    raised;

  (* 3. The construct's span travels with the failure, so the report points at
     the code that wanted the declaration rather than at the helper. *)
  let span =
    {
      Meta.data =
        {
          file =
            {
              Meta.name = Local "t.rs";
              crate_name = "t";
              contents = None;
            };
          beg_loc = { line = 3; col = 1 };
          end_loc = { line = 4; col = 2 };
        };
      generated_from_span = None;
    }
  in
  let span_of_failure =
    try
      ignore
        (Decl_lookup.decl_lookup "t.ml" 1 (Some span) ~what ~name lookup 9);
      "no span"
    with Errors.CFailure e -> (
      match e.span with
      | Some s when s = span -> "the construct's span"
      | Some _ -> "some other span"
      | None -> "no span")
  in
  expect "the failure carries the construct's span" "the construct's span"
    span_of_failure;

  (* 4. A name test answers without the declaration: an absent callee is not the
     function being looked for, and that is a sound answer rather than a guess.
     Pinned alongside case 2 so a later "fix" cannot make this one raise. *)
  let is_box_new = [ (3, true) ] in
  expect "default: an absent declaration answers the fallback" "false"
    (string_of_bool
       (Decl_lookup.default false (fun id -> List.assoc_opt id is_box_new) 9));
  expect "default: a present declaration answers itself" "true"
    (string_of_bool
       (Decl_lookup.default false (fun id -> List.assoc_opt id is_box_new) 3));

  if !failures > 0 then begin
    Printf.printf "%d failure(s)\n" !failures;
    exit 1
  end
  else print_endline "all Decl_lookup cases passed"
