(** How a recursive trait-declaration group is represented in the emitted Lean.

    Lean rejects a [mutual] block whose members do not share one parameter list
    ("Invalid mutually inductive types: ... has N parameter(s), but the preceding
    type has M"), and a trait's parameter count is decided by its associated
    types, which Rust does not constrain across a cycle. Charon therefore hands
    us groups that cannot be written as Lean mutually inductive types at all --
    three different encodings were measured and rejected by the kernel, so the
    question is not how to write the [mutual] block but what to emit instead.

    The representation that does type-check keeps every trait an ordinary
    structure and turns the sister traits' dictionary TYPES into parameters.
    A trait then names no other declaration, so there is nothing to order and no
    [mutual] block is emitted. The parameter must live one universe up (a
    dictionary type whose fields quantify over [Type] lives in [Type 1]), which
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

(** Remove repeated names, keeping the first occurrence: the binder list is a
    set of types, and a repeated binder makes Lean reject the declaration. *)
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
    separator both render as visible characters inside the same quoted
    identifier, so two distinct trait names cannot collapse onto one binder -- a
    collision Lean would report as a duplicate binder far from the cause. *)
let binder_name (trait_ : string) : string = "«" ^ trait_ ^ "»"

(** The full binder, including the universe the parameter has to live in.
    A dictionary type whose fields quantify over [Type] inhabits [Type 1], so the
    parameter is declared at [Type (u+1)]; [u] is declared once, at the top of the
    emitted trait section. *)
let binder_text (trait_ : string) : string =
  "(" ^ binder_name trait_ ^ " : Type (u+1))"
