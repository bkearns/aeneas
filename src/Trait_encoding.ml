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
    emitted trait section.

    The binder carries a default because the parameter is not always
    recoverable at the use site. A dictionary type is a Rust where-clause in
    disguise: [Deserialize V] can only be completed by the [Deserializer] the
    surrounding declaration works with, and when nothing in scope names one
    there is no honest argument to print. A default turns that into one hole
    at the declaration instead of a partially applied type former at every use
    -- and a hole is visible in the file, whereas a made-up dictionary type
    would type-check and lie about what the model says. Sites where the clauses
    do supply the whole dictionary still get it, through {!arguments_of}, but on
    a serde-sized crate almost none do: a declaration binds the clauses its own
    signature needs, not the whole group's. *)
let binder_text (trait_ : string) : string =
  "(" ^ binder_name trait_ ^ " : Type (u+1) := sorry)"

(** The same parameter spelled as the *type* it stands for, for naming it where
    a value is expected rather than declaring it.

    An ascription cannot carry a default, so this cannot be [binder_text]: the
    two denote one type and have to be written differently, and using the
    declarative spelling inside a method's binder is a syntax error far from the
    cause. *)
let binder_ref (trait_ : string) : string =
  "(" ^ binder_name trait_ ^ " : Type (u+1))"

(** A sister trait that a declaration of a parameterized group takes as a
    parameter, with the Lean name an argument can be written against.

    The plan below says which parameters a declaration carries; a use site
    needs the other half, the *argument*. It cannot be recovered from the use
    site: [Deserialize V] says nothing about which [Deserializer] the
    surrounding declaration works with. So the name is recorded where the group
    was decided and looked up again by id. *)
type extra_param = { sister_id : Pure.trait_decl_id; sister_name : string }

(** A dictionary type as it can be written at one use site: the sister, the
    arguments the clause binds it to, and -- because that dictionary's own
    parameters ask for dictionaries in turn -- the arguments *those* need. *)
type argument = {
  arg_param : extra_param;
  arg_clause : Pure.trait_param;
  arg_nested : argument list;
}

(** Build the arguments a use site can write, out of the clauses it has.

    All or nothing, and that is the whole point. A dictionary type is written
    [Sister T1 .. Tn], so naming it means naming the dictionaries its *own*
    parameters ask for -- [Serialize] takes [Serializer]'s, which takes the
    eight [Serialize*] traits', which take [Serialize]'s again. Half a term is
    not a type: leaving the tail to the parameter defaults would put a hole
    inside an argument rather than at the end of the argument list, where it
    could not even be seen. So the answer is [None] unless every level can be
    written, and the caller reports the gap instead.

    [visited] is the chain already being written, and it is not an optimisation.
    Dependencies inside a group are cyclic, so an unguarded walk would never
    terminate; a repeat means the term would be infinite, which is to say:
    unwritable.

    [params_of] is the parameter list of a declaration. It is passed in rather
    than read from the table so the decision can be tested on its own. *)
let rec arguments_of ~(clauses : Pure.trait_param list)
    ~(params_of : Pure.trait_decl_id -> extra_param list)
    ~(visited : Pure.trait_decl_id list) (params : extra_param list) :
    argument list option =
  match params with
  | [] -> Some []
  | p :: rest -> (
      let bound =
        List.find_opt
          (fun (c : Pure.trait_param) -> c.trait_id = p.sister_id)
          clauses
      in
      match bound with
      | Some arg_clause
        when not (List.exists (fun id -> id = p.sister_id) visited) -> (
          match
            arguments_of ~clauses ~params_of
              ~visited:(p.sister_id :: visited)
              (params_of p.sister_id)
          with
          | None -> None
          | Some arg_nested -> (
              match arguments_of ~clauses ~params_of ~visited rest with
              | None -> None
              | Some rest ->
                  Some ({ arg_param = p; arg_clause; arg_nested } :: rest)))
      | _ -> None)

(** Per-declaration parameters, filled once per file before anything is printed.

    A group's plan is decided at the group, but its use sites are printed
    wherever they occur -- an impl of the trait, a function that takes it as a
    clause, a field of an unrelated type -- and [split-files] prints use sites in
    a file that does not print the declarations at all. A table keyed by
    declaration id is therefore the only place where the arity is visible at
    both ends. It is rebuilt from the crate's declaration groups at the start of
    every file, so a second crate extracted in the same run cannot inherit the
    first one's ids. *)
let parameterized : (string, extra_param list) Hashtbl.t = Hashtbl.create 16

let reset_parameterized () : unit = Hashtbl.reset parameterized

let register_parameterized ~(id : Pure.trait_decl_id)
    (params : extra_param list) : unit =
  Hashtbl.replace parameterized (Pure.TraitDeclId.to_string id) params

(** The extra parameters a declaration carries, in binder order. Empty for the
    overwhelming majority of traits, which no group makes cyclic. *)
let extra_params (id : Pure.trait_decl_id) : extra_param list =
  Option.value
    ~default:[]
    (Hashtbl.find_opt parameterized (Pure.TraitDeclId.to_string id))

(** The trait clauses of the declaration being printed.

    A use site can only be completed from what that declaration binds: a clause
    is the only place where a dictionary type is named with the arguments its
    methods need, and the surrounding function's own parameters are the only
    names a term may mention. *)

let current_clauses : (string, Pure.trait_param) Hashtbl.t = Hashtbl.create 16

let current_owner : string ref = ref ""

let current_clauses_list () : Pure.trait_param list =
  Hashtbl.fold (fun _ c acc -> c :: acc) current_clauses []

(** Install the clauses in force while [f] prints one declaration.

    [owner] names the declaration, for the report emitted when a parameter
    cannot be supplied -- a bare span does not say which of two hundred
    functions the reader should look at. *)
let with_clauses ~(owner : string) ~(clauses : Pure.trait_param list)
    (f : unit -> unit) : unit =
  let saved = Hashtbl.copy current_clauses in
  let saved_owner = !current_owner in
  Hashtbl.reset current_clauses;
  (* First clause wins: two clauses on one trait are two dictionaries, and either
     names types the declaration may use, so picking one is enough and picking
     the same one every run keeps the output stable. *)
  List.iter
    (fun (c : Pure.trait_param) ->
      let key = Pure.TraitDeclId.to_string c.trait_id in
      if not (Hashtbl.mem current_clauses key) then
        Hashtbl.add current_clauses key c)
    clauses;
  current_owner := owner;
  Fun.protect f ~finally:(fun () ->
      Hashtbl.reset current_clauses;
      Hashtbl.iter (fun k v -> Hashtbl.replace current_clauses k v) saved;
      current_owner := saved_owner)

(** The declaration whose clauses are in force, for error messages: a span alone
    does not say which of two hundred functions the reader should look at. *)
let owner () : string = !current_owner

(** {!arguments_of} against the scope in force: the arguments this use site can
    carry, or [None] when it can carry none of them. *)
let arguments_here (id : Pure.trait_decl_id) : argument list option =
  arguments_of ~clauses:(current_clauses_list ()) ~params_of:extra_params
    ~visited:[] (extra_params id)

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
