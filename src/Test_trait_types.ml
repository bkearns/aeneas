(* Type traversal and group assembly for cyclic trait-declaration groups.

   A trait is only "cyclic" because some type somewhere names it, so the analysis
   over types decides the whole encoding. It runs on [Pure], the translated model
   the printer prints -- pointers, arrays, slices and function types are already
   erased or lowered by then, so the case list here is the whole case list.

   These cases pin one representative per [Pure.ty] variant plus the nested
   carriers, using hand-built types rather than an LLBC fixture so the shape under
   test is visible in the test itself.

   Run with `dune build @runtest` from src/. *)

let failures = ref 0

open Aeneas

let check (what : string) (ok : bool) (detail : string) =
  if not ok then begin
    incr failures;
    Printf.printf "FAIL  %-58s %s\n" what detail
  end
  else Printf.printf "PASS  %-58s\n" what

let show_ids (ids : Pure.trait_decl_id list) : string =
  "[" ^ String.concat ", " (List.map Pure.TraitDeclId.to_string ids) ^ "]"

let check_traits (what : string) (expected : int list) (ty : Pure.ty) =
  let got = Trait_encoding.traits_in_ty ty in
  let expected = List.map Pure.TraitDeclId.of_int expected in
  check what (got = expected)
    (Printf.sprintf "expected %s got %s" (show_ids expected) (show_ids got))

(* --- fixtures ------------------------------------------------------------- *)

let no_args : Pure.generic_args =
  { types = []; const_generics = []; trait_refs = [] }

let no_params : Pure.generic_params =
  { types = []; const_generics = []; trait_clauses = [] }

let tref (id : int) : Pure.trait_ref =
  {
    trait_id = Pure.Self;
    trait_decl_ref =
      { trait_decl_id = Pure.TraitDeclId.of_int id; decl_generics = no_args };
  }

(* A parent-clause instance: the reference is to [id], projected from a parent
   whose own declaration is [parent]. *)
let parent_ref (parent : int) (id : int) : Pure.trait_ref =
  {
    trait_id =
      Pure.ParentClause (Pure.Self, Pure.TraitDeclId.of_int parent, Charon.Types.TraitClauseId.of_int 0);
    trait_decl_ref =
      { trait_decl_id = Pure.TraitDeclId.of_int id; decl_generics = no_args };
  }

let impl_ref (impl : int) (id : int) : Pure.trait_ref =
  {
    trait_id = Pure.TraitImpl (Charon.Types.TraitImplId.of_int impl, no_args);
    trait_decl_ref =
      { trait_decl_id = Pure.TraitDeclId.of_int id; decl_generics = no_args };
  }

let args_with_types (types : Pure.ty list) : Pure.generic_args =
  { no_args with types }

let args_with_refs (refs : Pure.trait_ref list) : Pure.generic_args =
  { no_args with trait_refs = refs }

let clause (id : int) : Pure.trait_param =
  {
    clause_id = Charon.Types.TraitClauseId.of_int 0;
    trait_id = Pure.TraitDeclId.of_int id;
    generics = no_args;
  }

let adt (args : Pure.generic_args) : Pure.ty = Pure.TAdt (Pure.TTuple, args)

let trait_ty (r : Pure.trait_ref) : Pure.ty =
  Pure.TTraitType (r, Charon.Types.AssocTypeId.of_int 0)

let u8 : Pure.ty = Pure.TLiteral (Pure.TUInt Charon.Values.U8)

(* --- cases ---------------------------------------------------------------- *)

let () =
  (* A trait named directly: the ordinary case, and the one that creates the
     cycle in serde (a method bounded by [S : Serializer<...>]). *)
  check_traits "TraitType names its trait" [ 3 ] (trait_ty (tref 3));

  (* An arrow names traits on either side. *)
  check_traits "TArrow sees its argument" [ 3 ]
    (Pure.TArrow (trait_ty (tref 3), u8));
  check_traits "TArrow sees its result" [ 4 ] (Pure.TArrow (u8, trait_ty (tref 4)));

  (* Every applied type carries generic arguments; a trait can sit in the type
     arguments or in the trait-reference arguments. *)
  check_traits "TAdt sees a trait in its type arguments" [ 3 ]
    (adt (args_with_types [ trait_ty (tref 3) ]));
  check_traits "TAdt sees a trait in its trait-ref arguments" [ 5 ]
    (adt (args_with_refs [ tref 5 ]));
  check_traits "TAdt sees a trait nested in its type arguments" [ 6 ]
    (adt (args_with_types [ Pure.TArrow (u8, trait_ty (tref 6)) ]));

  (* A trait reference's instance kind can name another declaration: a parent
     clause is a real reference to the supertrait. *)
  check_traits "ParentClause contributes the parent trait" [ 7; 8 ]
    (trait_ty (parent_ref 8 7));
  check_traits "TraitImpl contributions come from its generics" [ 1; 9 ]
    (trait_ty (impl_ref 0 1) |> fun t ->
      match t with
      | Pure.TTraitType (r, a) ->
          Pure.TTraitType
            ( { r with trait_id = Pure.TraitImpl (Charon.Types.TraitImplId.of_int 0, args_with_types [ trait_ty (tref 9) ]) },
              a )
      | _ -> t);

  (* A dyn Trait binder holds its predicates in the binder's trait clauses. *)
  check_traits "TDynTrait sees its binder clauses" [ 10 ]
    (Pure.TDynTrait { params = { no_params with trait_clauses = [ clause 10 ] } });

  (* Leaves genuinely mention nothing: if one of these reports a trait, the
     traversal is inventing names rather than reading them. *)
  check_traits "literal mentions nothing" [] u8;
  check_traits "never mentions nothing" [] Pure.TNever;
  check_traits "type variable mentions nothing" []
    (Pure.TVar (Charon.Types.Free (Charon.Types.TypeVarId.of_int 0)));
  check_traits "error type mentions nothing" [] Pure.TError;

  (* A trait named twice is listed once, or the binder list would carry a
     duplicate and Lean would reject the declaration. *)
  check_traits "a repeated mention is listed once" [ 3 ]
    (adt (args_with_types [ trait_ty (tref 3); trait_ty (tref 3) ]));

  (* Order is first-mention order, so the emitted binder list is stable from run
     to run and diffs stay readable. *)
  check_traits "mentions keep first-mention order" [ 14; 15 ]
    (adt (args_with_types [ trait_ty (tref 14); trait_ty (tref 15) ]));

  (* Group assembly: a member's sisters are the group members it names, minus
     itself, and nothing from outside the group. *)
  let group = [ "serde.Serialize"; "serde.Serializer"; "serde.SerializeSeq" ] in
  check "only in-group names become siblings"
    (Trait_encoding.siblings_of ~this:"serde.Serialize" ~group
       [ "serde.Serializer"; "std.fmt.Display" ]
    = [ "serde.Serializer" ])
    (String.concat ", "
       (Trait_encoding.siblings_of ~this:"serde.Serialize" ~group
          [ "serde.Serializer"; "std.fmt.Display" ]));
  check "a trait is not its own sibling"
    (Trait_encoding.siblings_of ~this:"serde.Serializer" ~group
       [ "serde.Serializer"; "serde.SerializeSeq" ]
    = [ "serde.SerializeSeq" ])
    (String.concat ", "
       (Trait_encoding.siblings_of ~this:"serde.Serializer" ~group
          [ "serde.Serializer"; "serde.SerializeSeq" ]));

  (* A bound is not a type. [fn ser<S: Serializer<...>>] names its sister in the
     signature's clauses, and that is what closes serde's cycle: the field type
     mentions nothing, yet the declaration cannot be ordered. *)
  let llbc_no_params : Charon.Types.generic_params =
    {
      regions = [];
      types = [];
      const_generics = [];
      trait_clauses = [];
      outlives = [];
      trait_type_constraints = [];
    }
  in
  let sig_ ?(clauses = []) ?(constraints = []) ?(inputs = []) ?(output = u8) () :
      Pure.fun_sig =
    {
      generics = { no_params with trait_clauses = clauses };
      explicit_info = { explicit_types = []; explicit_const_generics = [] };
      known_from_trait_refs = { known_types = []; known_const_generics = [] };
      llbc_generics = llbc_no_params;
      preds = { trait_type_constraints = constraints };
      fwd_info =
        {
          effect_info =
            { can_fail = false; can_diverge = false; is_rec = false };
          ignore_output = false;
        };
      back_effect_info = Pure.RegionGroupId.Map.empty;
      inputs;
      output;
    }
  in
  let mentions s = Trait_encoding.traits_in_sig s in
  check "a method's trait clause is a mention"
    (mentions (sig_ ~clauses:[ clause 3 ] ()) = [ Pure.TraitDeclId.of_int 3 ])
    (show_ids (mentions (sig_ ~clauses:[ clause 3 ] ())));
  check "a signature's inputs and result are still mentions"
    (mentions (sig_ ~inputs:[ trait_ty (tref 4) ] ~output:(trait_ty (tref 5)) ())
    = [ Pure.TraitDeclId.of_int 5; Pure.TraitDeclId.of_int 4 ])
    (show_ids
       (mentions (sig_ ~inputs:[ trait_ty (tref 4) ] ~output:(trait_ty (tref 5)) ())));
  let constraint_ : Pure.trait_type_constraint =
    { trait_ref = tref 6; type_id = Charon.Types.AssocTypeId.of_int 0; ty = u8 }
  in
  check "an associated-type constraint is a mention"
    (mentions (sig_ ~constraints:[ constraint_ ] ()) = [ Pure.TraitDeclId.of_int 6 ])
    (show_ids (mentions (sig_ ~constraints:[ constraint_ ] ())));

  if !failures = 0 then print_endline "ALL PASS"
  else Printf.printf "%d FAILED\n" !failures
