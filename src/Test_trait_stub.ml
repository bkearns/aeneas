(* Traits the crate names but does not declare.

   `serde_core::ser::Serialize` is the case: the LLBC mentions the trait, so the names
   map knows it, but its declaration lives in a crate aeneas does not translate, so
   nothing ever declares it. Every use then elaborates to `Unknown identifier`, which
   reads like a missing std instance but is a missing declaration for a third-party
   trait -- the same situation as the third-party *types* that are already declared
   opaque (`def rustls.error.other_error.OtherError : Type := sorry`).

   A trait is used as a type applied to its arguments, so the declaration has to take
   them: `structure <name> (Self : Type _) (_ : Type _) where` for a trait used at two
   type arguments. These cases pin the registry the printer fills and the text the
   driver emits before the declaration that uses it.

   Run with `dune build @runtest` from src/. *)

let failures = ref 0

open Aeneas

let expect (what : string) (expected : string) (actual : string) =
  if expected <> actual then begin
    incr failures;
    Printf.printf "FAIL  %-44s expected %S got %S\n" what expected actual
  end
  else Printf.printf "PASS  %-44s %s\n" what (String.trim actual)

(* What the driver prints for everything registered since the last flush. *)
let flush () =
  let buf = Buffer.create 256 in
  let fmt = Format.formatter_of_buffer buf in
  ExtractBase.flush_untranslated_trait_decls fmt;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let () =
  (* 1. One registration is one declaration, taking the arguments it is applied at:
     the trait is used as `serde_core.ser.Serialize T`, so the first parameter is the
     implementor and there is one more. *)
  let _ = ExtractBase.register_untranslated_trait ~name:"serde_core.ser.Serialize" ~arity:2 in
  expect "one trait, two type arguments"
    "structure serde_core.ser.Serialize (Self : Type _) (_ : Type _) where\n"
    (flush ());

  (* 2. The printer reaches the same trait from every use site, and a declaration may
     only be emitted once. *)
  let first =
    ExtractBase.register_untranslated_trait ~name:"serde_core.ser.Serialize" ~arity:2
  in
  let second =
    ExtractBase.register_untranslated_trait ~name:"serde_core.ser.Serialize" ~arity:2
  in
  expect "second registration reports it was known" "false" (string_of_bool second);
  let _ = first in
  expect "a trait registered twice is declared once" "" (flush ());

  (* 3. Order is the order the misses were found, because a declaration may be used by
     the next one. *)
  let _ = ExtractBase.register_untranslated_trait ~name:"a.First" ~arity:1 in
  let _ = ExtractBase.register_untranslated_trait ~name:"b.Second" ~arity:1 in
  expect "declarations keep the order they were found in"
    "structure a.First (Self : Type _) where\n\
     structure b.Second (Self : Type _) where\n"
    (flush ());

  (* 4. A flush empties the registry: the next declaration must not re-emit them. *)
  expect "flush leaves nothing behind" "" (flush ());

  (* 5. Arity 0 (a trait used with no type arguments) is still a usable type. *)
  let _ = ExtractBase.register_untranslated_trait ~name:"c.NoArgs" ~arity:0 in
  expect "no type arguments" "structure c.NoArgs where\n" (flush ());

  let _ = ExtractBase.register_untranslated_trait ~name:"d.Three" ~arity:3 in
  expect "three type arguments"
    "structure d.Three (Self : Type _) (_ : Type _) (_ : Type _) where\n"
    (flush ());

  (* 6. Ordering is the property the registry alone cannot give: the miss is only
     discovered by a lookup made while the declaration is being printed, and Lean has
     no forward references, so the stub has to be placed before the text that was
     already written. A driver that flushes before printing therefore emits the stub
     after its first use, which is the bug this pins. *)
  ExtractBase.reset_untranslated_traits ();
  let out = Buffer.create 256 in
  let out_fmt = Format.formatter_of_buffer out in
  ExtractBase.with_trait_stubs out_fmt (fun body ->
      ignore
        (ExtractBase.register_untranslated_trait
           ~name:"serde_core.ser.Serialize" ~arity:2);
      Format.fprintf body "def uses_serde : Nat := 0");
  Format.pp_print_flush out_fmt ();
  expect "a group that uses an undeclared trait is preceded by its stub"
    "structure serde_core.ser.Serialize (Self : Type _) (_ : Type _) where\ndef \
     uses_serde : Nat := 0"
    (Buffer.contents out);

  (* 7. A group that discovers nothing prints exactly what it printed before, with no
     stray blank line or box left behind. *)
  let out = Buffer.create 256 in
  let out_fmt = Format.formatter_of_buffer out in
  ExtractBase.with_trait_stubs out_fmt (fun body ->
      Format.fprintf body "def plain : Nat := 1");
  Format.pp_print_flush out_fmt ();
  expect "a group with nothing to declare is unchanged" "def plain : Nat := 1"
    (Buffer.contents out);

  (* 8. Each output file declares its own stubs: aeneas can split a crate across files,
     and a trait declared in the first is not in scope in the second. *)
  ExtractBase.reset_untranslated_traits ();
  let out = Buffer.create 256 in
  let out_fmt = Format.formatter_of_buffer out in
  ExtractBase.with_trait_stubs out_fmt (fun body ->
      ignore
        (ExtractBase.register_untranslated_trait
           ~name:"serde_core.ser.Serialize" ~arity:2);
      Format.fprintf body "def other : Nat := 2");
  Format.pp_print_flush out_fmt ();
  expect "a second output file declares the trait again"
    "structure serde_core.ser.Serialize (Self : Type _) (_ : Type _) where\ndef \
     other : Nat := 2"
    (Buffer.contents out);

  Printf.printf "\n%s\n"
    (if !failures = 0 then "ALL PASS" else Printf.sprintf "%d FAILED" !failures);
  exit (if !failures = 0 then 0 else 1)
