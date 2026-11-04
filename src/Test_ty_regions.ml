(* Regression tests for [ty_regions].

   [ty_regions] answers one question: which FREE regions does this type mention. A prepass
   rewrites body and variable regions to [RErased] (PrePasses.ml), so after prepasses a type may
   legitimately mention a region that is not free. Aborting on those answers a question the
   caller never asked, and takes the whole run with it.

   A third kind of region is legitimate in a type this collector sees: a bound one, where a
   function item binds the regions of its own arguments ([for<'a> String::as_str<'a>], as it
   appears inside [Map<Iter<String>, …>] once [impl Iterator] has been resolved). The binder is
   part of the type, and its regions are instantiated afresh at every call, so they are not
   regions of this signature either. All three are therefore skipped, and only the free regions
   are reported.

   Run with `dune build @runtest` from src/. *)

open Aeneas
open Types

let scalar = TScalar (TInteger (Signed Isize))
let ref_to (r : region) : ty = TRef (r, scalar, RShared)
let free i : region = RVar (Free (RegionId.of_int i))
let bound i : region = RVar (Bound (0, RegionId.of_int i))
let failures = ref 0

let report name = function
  | Ok note -> Printf.printf "PASS  %-52s %s\n" name note
  | Error note ->
      incr failures;
      Printf.printf "FAIL  %-52s %s\n" name note

let describe (s : RegionId.Set.t) =
  Printf.sprintf "{%s}"
    (String.concat ", "
       (List.map string_of_int
          (List.map RegionId.to_int (RegionId.Set.elements s))))

let expect_returned name (f : unit -> RegionId.Set.t) (expected : int list) =
  match f () with
  | s ->
      let got =
        List.sort compare (List.map RegionId.to_int (RegionId.Set.elements s))
      in
      let expected = List.sort compare expected in
      if got = expected then
        report name (Ok (Printf.sprintf "returned %s" (describe s)))
      else
        report name
          (Error
             (Printf.sprintf "returned %s, expected {%s}" (describe s)
                (String.concat ", " (List.map string_of_int expected))))
  | exception Failure m ->
      report name
        (Error (Printf.sprintf "raised Failure(%S); expected no exception" m))

let expect_raise name (f : unit -> RegionId.Set.t) =
  (* Any exception is a refusal, which is what this control is about; the report names the one
     that was raised so a change of exception is visible rather than silently accepted. *)
  match f () with
  | s ->
      report name
        (Error (Printf.sprintf "returned %s; expected an exception" (describe s)))
  | exception e ->
      report name (Ok (Printf.sprintf "raised %s, as required" (Printexc.to_string e)))

let () =
  (* An erased region is not a free region: it must be skipped, not abort the caller. *)
  expect_returned "erased region is skipped"
    (fun () -> TypesUtils.ty_regions (ref_to RErased))
    [];
  (* Same for a body region: it belongs to a closure body, not to this signature. *)
  expect_returned "body region is skipped"
    (fun () -> TypesUtils.ty_regions (ref_to (RBody (RegionId.of_int 0))))
    [];
  (* Static is neither free nor a reason to raise. *)
  expect_returned "static region contributes nothing"
    (fun () -> TypesUtils.ty_regions (ref_to RStatic))
    [];
  (* The positive control: a free region is still collected, so an always-empty answer fails. *)
  expect_returned "free region is collected"
    (fun () -> TypesUtils.ty_regions (ref_to (free 7)))
    [ 7 ];
  (* A type that mentions all three still reports only the free one: the outer reference is
     erased and its pointee is a reference whose region is a body region, which in turn points at
     a free region nested one level deeper. *)
  expect_returned "free region under erased and body is reported"
    (fun () ->
      TypesUtils.ty_regions
        (TRef
           ( RErased,
             TRef (RBody (RegionId.of_int 1), ref_to (free 3), RShared),
             RShared )))
    [ 3 ];
  (* Erased nested inside another erased-only type is still no reason to raise. *)
  expect_returned "nested erased regions are skipped"
    (fun () -> TypesUtils.ty_regions (TRef (RErased, ref_to RErased, RMut)))
    [];
  (* A bound region belongs to a binder inside the type, not to this signature: a function item
     binds its own, and instantiates them at every call. Skip it, as for an erased or body one. *)
  expect_returned "bound region is skipped"
    (fun () -> TypesUtils.ty_regions (ref_to (bound 9)))
    [];
  (* The positive control still holds next to it: a free region is collected even when the same
     type also mentions a bound one. *)
  expect_returned "free region beside a bound one is still collected"
    (fun () -> TypesUtils.ty_regions (TRef (free 4, ref_to (bound 9), RShared)))
    [ 4 ];
  (* The fix must not swallow the inconsistency it was never about: a Lub region is a
     least-upper-bound constraint, not a region of the signature, and stays an error. *)
  expect_raise "Lub region still raises" (fun () ->
      TypesUtils.ty_regions (ref_to (RLub scalar)));

  if !failures = 0 then (
    Printf.printf "\nty_regions: all contracts hold\n";
    exit 0)
  else (
    Printf.printf "\nty_regions: %d contract(s) broken\n" !failures;
    exit 1)
