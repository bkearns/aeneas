(* Type traversal for cyclic trait-declaration groups.

   A trait is only "cyclic" because some type somewhere names it, so the analysis
   over types decides the whole encoding. That analysis has to be exhaustive: a
   mention hidden in generic arguments, a [Sized] proof, a [dyn Trait] binder, an
   associated-type constraint or a trait reference's own [kind] creates the same
   cycle as an obvious one, and a missed mention emits a declaration that still
   fails to elaborate.

   These cases pin one representative per [ty_kind] variant plus the nested
   carriers, using hand-built types rather than an LLBC fixture so the shape under
   test is visible in the test itself.

   Run with `dune build @runtest` from src/. *)

let failures = ref 0

open Aeneas
open Charon.Types

let check (what : string) (ok : bool) (detail : string) =
  if not ok then begin
    incr failures;
    Printf.printf "FAIL  %-58s %s\n" what detail
  end
  else Printf.printf "PASS  %-58s\n" what

let show_ids (ids : trait_decl_id list) : string =
  "[" ^ String.concat ", " (List.map TraitDeclId.to_string ids) ^ "]"

let check_traits (what : string) (expected : int list) (ty : ty) =
  let got = Trait_encoding.traits_in_ty ty in
  let expected = List.map TraitDeclId.of_int expected in
  check what (got = expected)
    (Printf.sprintf "expected %s got %s" (show_ids expected) (show_ids got))

(* --- fixtures ------------------------------------------------------------- *)

let no_args : generic_args =
  { regions = []; types = []; const_generics = []; trait_refs = [] }

let no_params : generic_params =
  {
    regions = [];
    types = [];
    const_generics = [];
    trait_clauses = [];
    outlives = [];
    trait_type_constraints = [];
  }

(** A binder over regions only, which is what a trait predicate carries. *)
let rb (v : 'a) : 'a region_binder =
  { binder_regions = []; outlives = []; binder_value = v }

(** A full binder, which is what a [dyn Trait] predicate carries. *)
let full_binder (params : generic_params) (v : 'a) : 'a binder =
  { binder_params = params; binder_value = v }

let tref (id : int) : trait_ref =
  {
    kind = TraitImpl { id = TraitImplId.of_int 0; generics = no_args };
    trait_decl_ref = ({ id = TraitDeclId.of_int id; generics = no_args } : trait_decl_ref);
  }

let parent_clause_ref (parent : int) (id : int) : trait_ref =
  {
    kind = ParentClause (tref parent, TraitClauseId.of_int 0, { regions = [] });
    trait_decl_ref = ({ id = TraitDeclId.of_int id; generics = no_args } : trait_decl_ref);
  }

let args_with_types (types : ty list) : generic_args = { no_args with types }

let args_with_refs (ids : int list) : generic_args =
  { no_args with trait_refs = List.map (fun id -> rb (tref id)) ids }

let clause (id : int) : trait_param =
  {
    clause_id = TraitClauseId.of_int 0;
    span = None;
    origin = WhereClauseOnFn;
    trait = rb ({ id = TraitDeclId.of_int id; generics = no_args } : trait_decl_ref);
  }

let adt (args : generic_args) : ty =
  TAdt ({ id = TypeDeclId.of_int 0; generics = args; builtin = None } : type_decl_ref)

let trait_ty (r : trait_ref) : ty =
  TTraitType (r, AssocTypeId.of_int 0, no_args)

let u8 : ty = TScalar (TInteger (Unsigned U8))

(** An array length, which the traversal must not confuse for a type. *)
let len : constant_expr = { kind = CBool true; ty = u8 }

let fnsig ?(inputs = []) ?(output = u8) () : fun_sig =
  { is_unsafe = false; abi = AbiRust; is_variadic = false; inputs; output }

(* --- cases ---------------------------------------------------------------- *)

let () =
  (* A trait named directly: the ordinary case, and the one that creates the
     cycle in serde (a method bounded by [S : Serializer<...>]). *)
  check_traits "TraitType names its trait" [ 3 ] (trait_ty (tref 3));

  (* References and raw pointers only wrap: the trait is inside. *)
  check_traits "TRef recurses into the pointee" [ 3 ]
    (TRef (RStatic, trait_ty (tref 3), RShared));
  check_traits "TRawPtr recurses into the pointee" [ 3 ]
    (TRawPtr (trait_ty (tref 3), RShared));
  check_traits "TPtrMetadata recurses into the pointee" [ 3 ]
    (TPtrMetadata (trait_ty (tref 3)));

  (* A region can carry a type of its own: RLub is the least upper bound of the
     regions of a type, and that type may name a trait. *)
  check_traits "TRef sees a trait inside an RLub region" [ 3 ]
    (TRef (RLub (trait_ty (tref 3)), u8, RShared));

  (* An array and a slice each carry an optional [Sized] proof that is a trait
     reference, and their element type may name a trait as well. *)
  check_traits "TArray sees the element type" [ 3 ]
    (TArray (trait_ty (tref 3), len, None));
  check_traits "TArray sees the Sized proof" [ 4 ]
    (TArray (u8, len, Some (tref 4)));
  check_traits "TSlice sees the element type" [ 3 ]
    (TSlice (trait_ty (tref 3), None));
  check_traits "TSlice sees the Sized proof" [ 4 ]
    (TSlice (u8, Some (tref 4)));

  (* Every applied type carries generic arguments; a trait can sit in the type
     arguments or in the trait-reference arguments. *)
  check_traits "TAdt sees a trait in its type arguments" [ 3 ]
    (adt (args_with_types [ trait_ty (tref 3) ]));
  check_traits "TAdt sees a trait in its trait-ref arguments" [ 5 ]
    (adt (args_with_refs [ 5 ]));
  check_traits "TAdt sees a trait nested in its type arguments" [ 6 ]
    (adt (args_with_types [ TSlice (u8, Some (tref 6)) ]));

  (* A trait reference's own kind can carry another trait: a parent clause is a
     real reference to the supertrait. *)
  check_traits "ParentClause contributes the parent trait" [ 7; 8 ]
    (trait_ty (parent_clause_ref 8 7));

  (* Pattern types scrutinise a value: the type under the pattern still counts. *)
  check_traits "TPattern recurses into the scrutinee" [ 3 ]
    (TPattern (trait_ty (tref 3), NotNull));

  (* A dyn Trait binder holds its predicates in the binder's trait clauses. *)
  check_traits "TDynTrait sees its binder clauses" [ 9 ]
    (TDynTrait { binder = full_binder { no_params with trait_clauses = [ clause 9 ] } u8 });

  (* Function-item and function-pointer types name traits through their signature. *)
  check_traits "TFnPtr sees a trait in its inputs" [ 10 ]
    (TFnPtr (rb (fnsig ~inputs:[ trait_ty (tref 10) ] ())));
  check_traits "TFnPtr sees a trait in its output" [ 11 ]
    (TFnPtr (rb (fnsig ~output:(trait_ty (tref 11)) ())));
  check_traits "TFnDef sees its trait-method reference" [ 12 ]
    (TFnDef
       (rb
          {
            kind = TraitMethod (tref 12, TraitMethodId.of_int 0);
            generics = no_args;
          }));

  (* A constraint on an associated type names both the trait and the type it is
     constrained to: [<T as Trait>::Item = U] mentions Trait and U. *)
  check_traits "associated-type constraint names its trait" [ 13 ]
    (TDynTrait
       {
         binder =
           full_binder
             {
               no_params with
               trait_type_constraints =
                 [ rb { trait_ref = tref 13; type_id = AssocTypeId.of_int 0; ty = u8 } ];
             }
             u8;
       });
  check_traits "associated-type constraint sees the constrained type" [ 0; 16 ]
    (TDynTrait
       {
         binder =
           full_binder
             {
               no_params with
               trait_type_constraints =
                 [
                   rb
                     {
                       trait_ref = tref 0;
                       type_id = AssocTypeId.of_int 0;
                       ty = trait_ty (tref 16);
                     };
                 ];
             }
             u8;
       });

  (* Leaves genuinely mention nothing: if one of these reports a trait, the
     traversal is inventing names rather than reading them. *)
  check_traits "scalar mentions nothing" [] u8;
  check_traits "never mentions nothing" [] TNever;
  check_traits "type variable mentions nothing" [] (TVar (Free (TypeVarId.of_int 0)));
  check_traits "error type mentions nothing" [] (TError "incomplete");

  (* A trait named twice is listed once, or the binder list would contain a
     duplicate and Lean would reject the declaration. *)
  check_traits "a repeated mention is listed once" [ 3 ]
    (adt (args_with_types [ trait_ty (tref 3); trait_ty (tref 3) ]));

  (* Order is first-mention order, so the emitted binder list is stable from run
     to run and diffs stay readable. *)
  check_traits "mentions keep first-mention order" [ 14; 15 ]
    (adt (args_with_types [ trait_ty (tref 14); trait_ty (tref 15) ]));

  if !failures = 0 then print_endline "ALL PASS"
  else Printf.printf "%d FAILED\n" !failures
