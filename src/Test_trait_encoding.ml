(* Shape decisions for recursive trait-declaration groups.

   A group is cyclic when at least one of its traits mentions another in a field
   type -- in Lean terms, when a declaration needs a name that a later
   declaration provides. Lean has no forward references, and the [mutual]
   workaround is unavailable here because its members cannot share a parameter
   list (their parameter counts follow their associated types). So the emitter
   has to change the representation instead: sister dictionary TYPES become
   parameters, which removes the reference and with it the cycle.

   These cases pin the decision on its own, with no LLBC fixture and no
   formatter: which shape a group gets, and exactly which parameters each member
   then carries. Emission is a separate, later step that consumes this plan.

   Run with `dune build @runtest` from src/. *)

let failures = ref 0

open Aeneas

let check (what : string) (ok : bool) (detail : string) =
  if not ok then begin
    incr failures;
    Printf.printf "FAIL  %-58s %s\n" what detail
  end
  else Printf.printf "PASS  %-58s\n" what

let show_plan (p : Trait_encoding.plan) : string =
  match p with
  | Plain -> "Plain"
  | Parameterized groups ->
      "Parameterized ["
      ^ String.concat "; "
          (List.map
             (fun (name, ps) ->
               name ^ " (" ^ String.concat ", " ps ^ ")")
             groups)
      ^ "]"

let is_plain (p : Trait_encoding.plan) : bool = p = Trait_encoding.Plain

let params_of (p : Trait_encoding.plan) (name : string) : string list option =
  match p with
  | Plain -> None
  | Parameterized groups -> List.assoc_opt name groups

let member name siblings = Trait_encoding.{ name; siblings }

let case what expected members =
  let got = Trait_encoding.plan_of_group members in
  let ok, detail =
    match expected with
    | `Plain -> (is_plain got, show_plan got)
    | `Params (name, ps) ->
        (match params_of got name with
        | Some actual -> (actual = ps, name ^ " got (" ^ String.concat ", " actual ^ ")")
        | None -> (false, "no parameters for " ^ name ^ " in " ^ show_plan got))
  in
  check what ok detail

let () =
  (* 1. Independent traits in one group carry no extra parameters and need no
        [mutual] block: nothing refers to anything. *)
  case "independent members stay plain" `Plain
    [ member "serde_core.ser.Error" []; member "serde_core.de.Error" [] ];

  (* 2. One member naming another is the smallest cycle and must produce a
        parameter for exactly that reference. *)
  case "one reference yields one parameter"
    (`Params ("serde_core.ser.Serialize", [ "serde_core.ser.Serializer" ]))
    [
      member "serde_core.ser.Serialize" [ "serde_core.ser.Serializer" ];
      member "serde_core.ser.Serializer" [];
    ];

  (* 3. A member naming two others carries both, in the order the references
        appear, because the emitted binder order must be stable across runs. *)
  case "references keep their order"
    (`Params ("serde_core.ser.Serializer", [ "serde_core.ser.SerializeSeq"; "serde_core.ser.SerializeMap" ]))
    [
      member "serde_core.ser.Serializer"
        [ "serde_core.ser.SerializeSeq"; "serde_core.ser.SerializeMap" ];
      member "serde_core.ser.SerializeSeq" [];
      member "serde_core.ser.SerializeMap" [];
    ];

  (* 4. A trait that names itself is a cycle of length one and still needs its
        own parameter: without it the declaration is a forward reference. *)
  case "self reference still parameterizes"
    (`Params ("aeneas_list.List", [ "aeneas_list.List" ]))
    [ member "aeneas_list.List" [ "aeneas_list.List" ] ];

  (* 5. A name repeated in several fields is one parameter, not several: the
        binder list is a set of types, and duplicates would make Lean reject
        the declaration for shadowing. *)
  case "repeated reference is deduplicated"
    (`Params ("aeneas_list.List", [ "aeneas_list.List" ]))
    [ member "aeneas_list.List" [ "aeneas_list.List"; "aeneas_list.List" ] ];

  (* 6. Members that reference nothing still appear in the plan of a cyclic
        group, with no parameters, so the emitter can walk the group in one
        pass instead of special-casing the plain members. *)
  case "non-referencing members appear with no parameters"
    (`Params ("serde_core.ser.Serialize", [ "serde_core.ser.Serializer" ]))
    [
      member "serde_core.ser.Serialize" [ "serde_core.ser.Serializer" ];
      member "serde_core.ser.Serializer" [];
      member "serde_core.ser.Error" [];
    ];

  if !failures = 0 then print_endline "ALL PASS"
  else Printf.printf "%d FAILED\n" !failures
