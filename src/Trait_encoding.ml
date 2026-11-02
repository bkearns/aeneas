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

    Everything here works on the translated model -- [Pure], which is what the
    printer prints -- and not on the LLBC types, which are gone by this point. *)

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

    The traversal is exhaustive over [ty]: a cycle is created by any mention, and
    the variants that hide one are not the obvious ones. A trait appears

    - directly in [TTraitType] -- a trait's type applied to arguments;
    - inside [generic_args], which every applied type carries, including its
      [trait_refs] component;
    - in an arrow, on either side;
    - and inside a [dyn Trait] binder's clauses.

    There is no pointer, array, slice, pattern or function-item variant to walk:
    [Pure] has already erased or lowered them, which is why this traversal is
    shorter than the one over LLBC types it replaced.

    Leaves -- [TVar], [TLiteral], [TNever], [TError] -- mention nothing. *)
let rec raw_traits_in_ty (t : Pure.ty) : Pure.trait_decl_id list =
  match t with
  | Pure.TAdt (_, args) -> raw_traits_in_args args
  | Pure.TVar _ | Pure.TLiteral _ | Pure.TNever | Pure.TError -> []
  | Pure.TArrow (arg, ret) -> raw_traits_in_ty arg @ raw_traits_in_ty ret
  | Pure.TTraitType (r, _) -> raw_traits_in_ref r
  | Pure.TDynTrait { params } -> raw_traits_in_params params

and raw_traits_in_args (args : Pure.generic_args) : Pure.trait_decl_id list =
  List.concat_map raw_traits_in_ty args.types
  @ List.concat_map raw_traits_in_ref args.trait_refs

and raw_traits_in_ref (r : Pure.trait_ref) : Pure.trait_decl_id list =
  let itself =
    [ r.trait_decl_ref.trait_decl_id ]
    @ raw_traits_in_args r.trait_decl_ref.decl_generics
  in
  let from_kind =
    match r.trait_id with
    (* A parent clause names the supertrait it comes from in its own right; the
       instance it is projected from carries no further declaration. *)
    | Pure.ParentClause (_, parent_id, _) -> [ parent_id ]
    | Pure.TraitImpl (_, generics) -> raw_traits_in_args generics
    | Pure.Self | Pure.Clause _ | Pure.BuiltinOrAuto _ | Pure.UnknownTrait _ ->
        []
  in
  itself @ from_kind

and raw_traits_in_params (params : Pure.generic_params) : Pure.trait_decl_id list
    =
  List.concat_map
    (fun (c : Pure.trait_param) -> [ c.trait_id ] @ raw_traits_in_args c.generics)
    params.trait_clauses

let uniq (ids : Pure.trait_decl_id list) : Pure.trait_decl_id list =
  List.fold_left
    (fun acc id -> if List.mem id acc then acc else acc @ [ id ])
    [] ids

(** The traits a type mentions, each listed once, in first-mention order. *)
let traits_in_ty (t : Pure.ty) : Pure.trait_decl_id list =
  uniq (raw_traits_in_ty t)

(** The traits a signature mentions: what it takes and what it returns, the
    clauses it quantifies over ([fn ser<S: Serializer<...>>]), and the
    constraints on its associated types. The clauses are the carrier that closes
    serde's cycle: the field types mention nothing, yet the declaration cannot be
    ordered against its sister. *)
let traits_in_sig (s : Pure.fun_sig) : Pure.trait_decl_id list =
  let from_types =
    raw_traits_in_ty s.output @ List.concat_map raw_traits_in_ty s.inputs
  in
  let from_clauses = raw_traits_in_params s.generics in
  let from_preds =
    List.concat_map
      (fun (c : Pure.trait_type_constraint) ->
        raw_traits_in_ref c.trait_ref @ raw_traits_in_ty c.ty)
      s.preds.trait_type_constraints
  in
  from_types @ from_clauses @ from_preds

(** Every trait a declaration mentions anywhere: its methods' signatures, the
    clauses that make it a subtrait, and its associated constants' types.
    Associated types contribute on their own only through the generics of their
    binder, which the clauses already cover. *)
let traits_in_decl (d : Pure.trait_decl) : Pure.trait_decl_id list =
  let methods =
    List.concat_map
      (fun (m : Pure.trait_method) -> traits_in_sig m.signature)
      d.methods
  in
  let parent_clauses =
    List.concat_map
      (fun (c : Pure.trait_param) -> [ c.trait_id ] @ raw_traits_in_args c.generics)
      d.parent_clauses
  in
  let consts = List.concat_map (fun (_, _, ty) -> raw_traits_in_ty ty) d.consts in
  uniq (methods @ parent_clauses @ consts)

(** Which of the mentioned names are sisters: inside the group, and not the
    trait's own name. The trait itself must not become a parameter of itself --
    that is the encoding's degenerate case, not a cycle -- and a name from
    outside the group is declared elsewhere and orders itself. *)
let siblings_of ~(this : string) ~(group : string list) (names : string list) :
    string list =
  List.filter (fun n -> n <> this && List.mem n group) names

(** One member of a group: which of its sisters it names, by Lean name. *)
let member_of_decl ~(this : string) ~(group : string list)
    ~(name_of : Pure.trait_decl_id -> string option) (d : Pure.trait_decl) :
    member =
  let names = List.filter_map name_of (traits_in_decl d) in
  { name = this; siblings = siblings_of ~this ~group names }

(** The binders in force for the declaration being printed, keyed by the id of
    the sister trait they stand for.

    The printer's context is immutable and threaded through every print
    function, so a scoped table is the smaller change; [with_binders] is the
    only way in, and it restores the previous state on every exit path. *)
let current_binders : (string, string) Hashtbl.t = Hashtbl.create 8

let current_header : string list ref = ref []

let with_binders ~(header : string list)
    ~(siblings : (Pure.trait_decl_id * string) list) (f : unit -> unit) : unit =
  let saved = Hashtbl.copy current_binders in
  let saved_header = !current_header in
  Hashtbl.reset current_binders;
  List.iter
    (fun (id, binder) ->
      Hashtbl.replace current_binders (Pure.TraitDeclId.to_string id) binder)
    siblings;
  current_header := header;
  Fun.protect f ~finally:(fun () ->
      Hashtbl.reset current_binders;
      Hashtbl.iter (fun k v -> Hashtbl.replace current_binders k v) saved;
      current_header := saved_header)

(** The binder standing for a trait in the declaration being printed, if any. *)
let binder_for (id : Pure.trait_decl_id) : string option =
  Hashtbl.find_opt current_binders (Pure.TraitDeclId.to_string id)

(** The extra parameters to print on the declaration being printed's header. *)
let header_binders () : string list = !current_header
