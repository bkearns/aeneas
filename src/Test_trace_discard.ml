(** Tests for {!Cps.trace_needed}: a discarded trace must not be built.

    The symbolic interpreter threads a continuation that rebuilds the symbolic AST, and it
    does so one statement at a time: every evaluated statement contributes a closure, and
    each closure keeps the evaluation context it was built with reachable. A context holds
    a whole environment (hundreds of bindings), so building that chain over a body of
    [n] statements costs [n] environments, whether or not anything ever reads the chain.

    The loop fixed point is the pass where this matters: it evaluates the body of a loop
    repeatedly, only to learn where control goes and what the context is on reentry, and it
    drops the trace every time. On a function whose body is dominated by cleanup ladders
    (a derived deserialiser over thirteen fields arrives with ~10^5 statements, 92% of them
    [StorageDead]) that discarded chain is several gigabytes and the translation is killed
    at its memory ceiling before the loop is even out of its first iteration.

    These checks pin the contract that makes the passes safe to run on such a body: under
    {!Cps.without_trace} the composed continuation must not keep the statement's context
    reachable. Reachability is measured with a weak pointer, which is what "retained" means
    here -- not "allocated", and not a timing. *)

open Aeneas
open SymbolicAst

let failures = ref 0

let check (name : string) (cond : bool) : unit =
  if not cond then begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

(* A span for the composed continuation's "this should never be applied" failure. *)
let span : Meta.span =
  {
    data =
      {
        file =
          {
            name = Meta.Local "crate/src/lib.rs";
            crate_name = "crate";
            contents = None;
          };
        beg_loc = { line = 1; col = 0 };
        end_loc = { line = 1; col = 0 };
      };
    generated_from_span = None;
  }

(** One statement's trace: a closure over a payload that stands in for the evaluation
    context the real interpreter captures. Applying it yields the payload's identity, so a
    test that does apply the trace can tell whether it was composed. *)
let compose ~(needed : bool) () : Bytes.t Weak.t * (expr list -> expr) =
  let payload = Bytes.make 1_000_000 'x' in
  let weak = Weak.create 1 in
  Weak.set weak 0 (Some payload);
  let cf_st1 (el : expr list) : expr =
    (* Reading the payload is what makes it live in this closure. *)
    if Bytes.get payload 0 = 'x' then List.hd el else List.hd el
  in
  let cf_st2 (el : expr list) : expr list = el in
  let composed =
    if needed then Cps.compose_trace span cf_st1 cf_st2
    else Cps.without_trace (fun () -> Cps.compose_trace span cf_st1 cf_st2)
  in
  (weak, composed)

(* The property the leak violated: a discarded trace holds nothing.

   The composed continuation is the value the evaluator returns and the caller keeps, so it
   is what is held live here; the statement's context (the payload) must still be
   collectable. *)
let test_discarded_trace_retains_nothing () =
  let weak, composed = compose ~needed:false () in
  ignore (Sys.opaque_identity composed : expr list -> expr);
  Gc.full_major ();
  check
    "without_trace: the statement's context is still reachable from the discarded trace"
    (Weak.get weak 0 = None)

(* The mirror image: when the trace *is* wanted, it must be composed for real. Without this
   check the previous one could pass by dropping the trace unconditionally. *)
let test_needed_trace_is_composed () =
  let weak, composed = compose ~needed:true () in
  ignore (Sys.opaque_identity composed : expr list -> expr);
  Gc.full_major ();
  check "trace needed: the statement's context was released" (Weak.get weak 0 <> None);
  check "trace needed: the trace is the head applied to the tail"
    (composed [ Panic ] = Panic)

(* [without_trace] is a dynamic extent, not a switch: it must end when it returns, and it
   must end when the wrapped computation raises. *)
let test_without_trace_is_scoped () =
  check "the trace is wanted outside any scope" (Cps.trace_needed ());
  Cps.without_trace (fun () ->
      check "the trace is not wanted inside the scope" (not (Cps.trace_needed ())));
  check "the trace is wanted again after the scope" (Cps.trace_needed ());
  (try Cps.without_trace (fun () -> failwith "boom") with Failure _ -> ());
  check "an exception inside the scope restores the flag" (Cps.trace_needed ())

(* A scope nested inside another restores the outer value, not the default. *)
let test_nested_scopes () =
  Cps.without_trace (fun () ->
      Cps.without_trace (fun () ->
          check "the innermost scope does not want the trace"
            (not (Cps.trace_needed ())));
      check "the outer scope is still in force" (not (Cps.trace_needed ())));
  check "both scopes ended" (Cps.trace_needed ())

let () =
  test_discarded_trace_retains_nothing ();
  test_needed_trace_is_composed ();
  test_without_trace_is_scoped ();
  test_nested_scopes ();
  if !failures = 0 then Printf.printf "test_trace_discard: all checks passed\n"
  else begin
    Printf.printf "test_trace_discard: %d check(s) failed\n" !failures;
    exit 1
  end
