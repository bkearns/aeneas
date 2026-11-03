(** The "tag model" for the very wide enumerations, in the Lean backend.

    Lean rejects an inductive with more than 244 constructors
    (["tag for constructor 'X.c244' is too big"]). Lean encodes the constructors
    of an inductive with a tag whose width it computes from the number of
    constructors, and that computation saturates at [U8] for the encodings we
    hit, so the whole declaration is rejected. Some real Rust enums are wider
    than that: [rustls::enums::CipherSuite] has 377 variants. Today such an enum
    loses its definition, and every function which mentions it then fails to
    elaborate.

    For those enums we therefore emit, instead of an inductive, a structure
    which stores the discriminant explicitly, plus one [Option] field per
    variant which has a payload:

    {v
      structure Foo where
        disc : Std.U16
        f3 : Option (Std.U32 × Bool) := none
    v}

    and we emit one function per variant ([Foo.Bar]) which builds the
    corresponding value, so that all the occurrences of the constructor names in
    the rest of the generated code (and in the proofs) keep working unchanged.

    The other backends have no such limit, and their code is not affected.

    Remark: this is the *type* half of the encoding. Matching on such an enum is
    done by testing [x.disc] (see the [Match] case of [extract_texpr]), because
    the type has no constructors to match on anymore. *)

open Pure
open Config
include ExtractBase

(** The maximum number of constructors of a Lean inductive. *)
let threshold = 244

(** Check whether a type declaration must use the tag model, i.e. whether it is
    an enumeration with more than {!threshold} variants which we must extract to
    Lean.

    The result is [{false}] for the other backends: they have no constructor
    limit, and the tag model is a Lean-specific encoding. *)
let is_wide_enum (ctx : extraction_ctx) (id : TypeDeclId.id) : bool =
  if backend () <> Lean then false
  else
    match TypeDeclId.Map.find_opt id ctx.trans_types with
    | None -> false
    | Some def -> (
        match def.kind with
        | Enum variants -> List.length variants > threshold
        | Struct _ | Opaque -> false)
