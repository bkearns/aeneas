(** How a recursive trait-declaration group is represented in the emitted Lean.

    Lean rejects a [mutual] block whose members do not share one parameter list
    ("Invalid mutually inductive types: ... has N parameter(s), but the preceding
    type has M"), and a trait's parameter count is decided by its associated
    types, which Rust does not constrain across a cycle. Charon therefore hands
    us groups that cannot be written as Lean mutually inductive types at all --
    every alternative encoding was measured and rejected by the kernel, so the
    question is not how to write the [mutual] block but what to emit instead.

    The representation that does type-check keeps every trait an ordinary
    structure and turns the sister traits' dictionary TYPES into parameters.
    A trait then names no other declaration, so there is nothing to order and no
    [mutual] block is emitted. The parameter must live one universe up (a
    dictionary type whose fields quantify over [Type] inhabits [Type 1]), which
    is why the emitted binder is [Type (u+1)].

    This module decides the shape from the group alone, so the decision is
    testable without an LLBC fixture and without a formatter. *)

type member = {
  name : string;  (** the trait's Lean name, e.g. "serde_core.ser.Serialize" *)
  siblings : string list;
      (** Lean names of the other members this trait's fields mention *)
}

type plan =
  | Plain
      (** No member mentions another. Emit each declaration as usual; the group
          needs neither [mutual] nor extra parameters. *)
  | Parameterized of (string * string list) list
      (** Cyclic group: per member, the extra type parameters to emit, in the
          order they must appear in the binder list. *)

(** Remove repeated names, keeping the first occurrence: a binder list is a set
    of types, and a repeated binder makes Lean reject the declaration. *)
let dedup (names : string list) : string list =
  let seen = Hashtbl.create 8 in
  List.filter
    (fun n ->
      if Hashtbl.mem seen n then false
      else begin
        Hashtbl.add seen n ();
        true
      end)
    names

(** A group is cyclic exactly when one of its traits names another in a field
    type. Everything else -- ordering, universe placement, emission -- follows
    from that one fact, so it is decided here rather than rediscovered by the
    printer. *)
let plan_of_group (members : member list) : plan =
  if List.for_all (fun (m : member) -> m.siblings = []) members then Plain
  else
    Parameterized
      (List.map (fun (m : member) -> (m.name, dedup m.siblings)) members)

(** The binder name used for a sister trait's dictionary type.

    A trait's own name is a dotted Lean name, which is a valid *declaration* name
    and an invalid *binder* name ("invalid binder name ..., it must be atomic"),
    so it is carried into the binder list in guillemets. Guillemets also make the
    mapping injective: a component containing an underscore and a component
    separator both stay visible characters inside the same quoted identifier, so
    two distinct trait names cannot collapse onto one binder -- a collision Lean
    would report as a duplicate binder far from the cause. *)
let binder_name (trait_ : string) : string = "«" ^ trait_ ^ "»"

(** The full binder, including the universe the parameter has to live in.
    A dictionary type whose fields quantify over [Type] inhabits [Type 1], so the
    parameter is declared at [Type (u+1)]; [u] is declared once, at the top of the
    emitted trait section. *)
let binder_text (trait_ : string) : string =
  "(" ^ binder_name trait_ ^ " : Type (u+1))"

(** Which traits a type mentions.

    This has to be exhaustive over [ty_kind]: a cycle is created by any mention,
    and the variants that hide one are not the obvious ones. A trait appears

    - directly in [TTraitType] -- a trait's type applied to arguments, which is
      how a bound such as [S : Serializer<...>] is written;
    - inside [generic_args], which every applied type carries, including its
      [trait_refs] component;
    - in the proof-carrying positions that do not read as types: the optional
      [Sized] proof on [TArray] and [TSlice], and the predicates inside a
      [dyn Trait] binder;
    - in function-item and function-pointer types, through their signatures;
    - and inside the [kind] of a trait reference itself, because [ParentClause]
      and [TraitMethod] carry another trait reference.

    Leaves -- [TScalar], [TNever], [TVar], [TError] -- mention nothing. The
    recursion is named [raw_*] and wrapped by a de-duplicating entry point, so
    callers never see the same trait twice. *)
let rec raw_traits_in_ty (t : Charon.Types.ty) : Charon.Types.trait_decl_id list =
  let open Charon.Types in
  match t with
  | TScalar _ | TNever | TVar _ | TError _ -> []
  | TRef (region, inner, _) ->
      raw_traits_in_region region @ raw_traits_in_ty inner
  | TRawPtr (inner, _) | TPtrMetadata inner -> raw_traits_in_ty inner
  | TArray (inner, _, sized) | TSlice (inner, sized) ->
      raw_traits_in_ty inner @ raw_traits_in_ref_opt sized
  | TAdt d -> raw_traits_in_args d.generics
  | TTraitType (r, _, args) -> raw_traits_in_ref r @ raw_traits_in_args args
  | TPattern (scrutinee, _) -> raw_traits_in_ty scrutinee
  | TFnDef b -> raw_traits_in_fn_ptr b.binder_value
  | TFnPtr b ->
      raw_traits_in_ty b.binder_value.output
      @ List.concat_map raw_traits_in_ty b.binder_value.inputs
  | TDynTrait d -> raw_traits_in_params d.binder.binder_params

(** A region can carry a type: [RLub] is the least upper bound of the regions of
    a type, and that type may name a trait. *)
and raw_traits_in_region (r : Charon.Types.region) :
    Charon.Types.trait_decl_id list =
  match r with
  | Charon.Types.RLub t -> raw_traits_in_ty t
  | Charon.Types.RVar _ | Charon.Types.RStatic | Charon.Types.RErased -> []
  | Charon.Types.RBody _ -> []

and raw_traits_in_args (args : Charon.Types.generic_args) :
    Charon.Types.trait_decl_id list =
  let open Charon.Types in
  List.concat_map raw_traits_in_ty args.types
  @ List.concat_map
      (fun (r : poly_trait_ref) ->
        [ r.binder_value.trait_decl_ref.id ]
        @ raw_traits_in_args r.binder_value.trait_decl_ref.generics)
      args.trait_refs

and raw_traits_in_ref (r : Charon.Types.trait_ref) :
    Charon.Types.trait_decl_id list =
  let open Charon.Types in
  let itself =
    [ r.trait_decl_ref.id ] @ raw_traits_in_args r.trait_decl_ref.generics
  in
  let from_kind =
    match r.kind with
    | TraitImpl i -> raw_traits_in_args i.generics
    | Clause _ -> []
    | ParentClause (parent, _, _) ->
        [ parent.trait_decl_ref.id ]
        @ raw_traits_in_args parent.trait_decl_ref.generics
    | ItemClause _ -> []
    | Self -> []
    | Dyn -> []
    | BuiltinOrAuto _ -> []
    | UnknownTrait _ -> []
  in
  itself @ from_kind

and raw_traits_in_ref_opt (r : Charon.Types.trait_ref option) :
    Charon.Types.trait_decl_id list =
  match r with None -> [] | Some r -> raw_traits_in_ref r

and raw_traits_in_fn_ptr (p : Charon.Types.fn_ptr) :
    Charon.Types.trait_decl_id list =
  let open Charon.Types in
  let from_kind =
    match p.kind with Fun _ -> [] | TraitMethod (r, _) -> raw_traits_in_ref r
  in
  from_kind @ raw_traits_in_args p.generics

and raw_traits_in_params (p : Charon.Types.generic_params) :
    Charon.Types.trait_decl_id list =
  List.concat_map
    (fun (c : Charon.Types.trait_param) ->
      let b = c.trait in
      [ b.binder_value.id ] @ raw_traits_in_args b.binder_value.generics)
    p.trait_clauses
  @ List.concat_map
      (fun (c : Charon.Types.trait_type_constraint Charon.Types.region_binder) ->
        raw_traits_in_ref c.binder_value.trait_ref
        @ raw_traits_in_ty c.binder_value.ty)
      p.trait_type_constraints

(** The traits a type mentions, each listed once, in first-mention order. *)
let traits_in_ty (t : Charon.Types.ty) : Charon.Types.trait_decl_id list =
  List.fold_left
    (fun acc id -> if List.mem id acc then acc else acc @ [ id ])
    [] (raw_traits_in_ty t)
