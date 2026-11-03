(** Tests for {!Trace_ring}: a diagnostic trace must not become a leak.

    A trace that keeps every value it is shown turns a bounded computation into an
    unbounded one: the search for a loop fixed point holds one whole evaluation
    environment per retained context, so an unbounded trace grows with the number of
    iterations rather than with the size of the loop. These checks pin the contract
    that makes the trace safe to leave in the code — the newest values are kept, older
    ones are dropped, and the amount retained does not depend on how many values were
    pushed. *)

open Aeneas

let failures = ref 0

let check (name : string) (cond : bool) : unit =
  if not cond then begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let ints (xs : int list) : string = String.concat "," (List.map string_of_int xs)

let check_eq (name : string) (expected : int list) (actual : int list) : unit =
  check
    (Printf.sprintf "%s: expected [%s], got [%s]" name (ints expected) (ints actual))
    (expected = actual)

(* An empty ring stays empty. *)
let test_empty () =
  check "push into empty ring keeps the value" (Trace_ring.push 1 [] = [ 1 ]);
  check "an empty ring prints as empty" (Trace_ring.to_list [] = [])

(* Below capacity nothing is dropped, and to_list restores chronological order. *)
let test_under_capacity () =
  let ring = Trace_ring.push 3 (Trace_ring.push 2 (Trace_ring.push 1 [])) in
  check "three values in a ring of eight are all kept" (List.length ring = 3);
  check_eq "to_list reads oldest first" [ 1; 2; 3 ] (Trace_ring.to_list ring)

(* At capacity the newest value is kept and the oldest is dropped. *)
let test_at_capacity () =
  let capacity = Trace_ring.default_capacity in
  let ring =
    List.fold_left (fun ring x -> Trace_ring.push x ring) [] (List.init (capacity + 1) (fun i -> i))
  in
  check "a full ring does not grow past its capacity" (List.length ring = capacity);
  check "the newest value is retained" (List.hd ring = capacity);
  check "the oldest value is dropped" (not (List.mem 0 ring));
  check_eq
    (Printf.sprintf "to_list keeps the last %d values in order" capacity)
    (List.init capacity (fun i -> i + 1))
    (Trace_ring.to_list ring)

(* The amount retained is independent of how many values were pushed — this is the
   property that makes the trace safe to leave enabled in a production path. *)
let test_retention_is_bounded () =
  let after n =
    List.fold_left (fun ring x -> Trace_ring.push x ring) [] (List.init n (fun i -> i))
  in
  let small = after 50 in
  let large = after 50_000 in
  check
    (Printf.sprintf "50 pushes retain %d values, 50000 retain %d — they must agree"
       (List.length small) (List.length large))
    (List.length small = List.length large);
  check "a large trace keeps only the newest values" (List.hd large = 49_999)

(* An explicit capacity is honoured, including the degenerate ones. *)
let test_explicit_capacity () =
  let ring = Trace_ring.push ~capacity:2 3 (Trace_ring.push ~capacity:2 2 (Trace_ring.push ~capacity:2 1 [])) in
  check_eq "capacity two keeps the two newest" [ 2; 3 ] (Trace_ring.to_list ring);
  let one = Trace_ring.push ~capacity:1 2 (Trace_ring.push ~capacity:1 1 []) in
  check_eq "capacity one keeps only the newest" [ 2 ] (Trace_ring.to_list one);
  let zero = Trace_ring.push ~capacity:0 1 [] in
  check "capacity zero retains nothing" (zero = [])

(* Pushing the same value repeatedly stays bounded. The ring compares nothing — a
   retained context is a large value and a structural comparison per push would cost
   more than the memory it saves — so repeats are kept, newest first. *)
let test_repeated_pushes () =
  let ring =
    List.fold_left (fun ring _ -> Trace_ring.push 7 ring) [] (List.init 100 (fun i -> i))
  in
  check "repeated pushes stay bounded" (List.length ring = Trace_ring.default_capacity);
  check "repeated pushes keep the newest value" (List.hd ring = 7);
  check "repeated pushes retain only that value" (List.for_all (fun x -> x = 7) ring)

let () =
  test_empty ();
  test_under_capacity ();
  test_at_capacity ();
  test_retention_is_bounded ();
  test_explicit_capacity ();
  test_repeated_pushes ();
  if !failures = 0 then Printf.printf "test_trace_ring: all checks passed\n"
  else begin
    Printf.printf "test_trace_ring: %d check(s) failed\n" !failures;
    exit 1
  end
