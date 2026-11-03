(** Naming a declaration the translation does not carry.

    Aeneas translates a *subset* of a crate, so an id taken from the LLBC does
    not prove that the translated declaration for it exists: the item may have
    been filtered out, may live in a crate left opaque, or may have been dropped
    because its own translation failed. A bare [Map.find] on such a map raises
    [Not_found], which aborts the whole file and names neither the declaration
    nor the lookup that wanted it -- one unusable item costs the entire crate,
    and the log says only "Fatal error: exception Not_found".

    Every lookup of a translated-declaration map therefore picks one of three
    answers, and there is no fourth:

    - {!decl_lookup}: the construct cannot be modelled without the declaration,
      so the miss is reported at the construct's span, naming the declaration.
      The run then continues with one error instead of dying. Call it through
      its macro, [[%decl_lookup] span ~what ~name lookup key], so the report
      names the call site and not this module.
    - a construct that is *dropped* rather than modelled reports through the
      helper it already uses ([%save_error] / [%warn_opt_span]) with {!msg}, so
      the same sentence names the item there too.
    - {!default}: the caller's question has a sound answer without the
      declaration -- typically a name test, where an absent callee is simply not
      the function being looked for. This answers silently, and is only correct
      when absence cannot change the model: a silent fallback on a *needed*
      declaration yields a wrong model, which is worse than a crash.

    Each takes the name to report, because an id on its own is a number. *)

let msg ~(what : string) ~(name : string) : string =
  what ^ " '" ^ name ^ "' is not part of the translation"

let decl_lookup (file : string) (line : int) (span : Meta.span option)
    ~(what : string) ~(name : string) (lookup : 'k -> 'd option) (key : 'k) : 'd
    =
  match lookup key with
  | Some decl -> decl
  | None -> Errors.craise_opt_span file line span (msg ~what ~name)

let default (fallback : 'd) (lookup : 'k -> 'd option) (key : 'k) : 'd =
  match lookup key with Some decl -> decl | None -> fallback
