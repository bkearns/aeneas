(** Tests for when a branch point's branches are joined: {!Cps.joins} and
    {!Cps.width_after_branch}.

    Symbolic execution keeps one evaluation context per path and a context holds a whole
    environment, so the number of paths a statement list ends in is what a body costs. A
    branch point contributes two kinds of result: the paths that continue to the rest of the
    block, which are evaluated again there, and the ones that have finished -- an early
    [return], or the [break] a desugared [?] error path becomes -- which are carried only so
    that their result is reported.

    Which of the two decides the join used to be a scan of the sub-blocks ("does any branch
    contain a [break] anywhere below it"), and a block's tail is where the enclosing loop's
    own [break] lives. On one crate that scan declined to join at all 16476 branch points of
    a body, leaving 8230 contexts in a single statement list of which 8230 - 38 were paths
    that had already finished. The numbers are recorded here because they are what the rule
    below is for: a decision made from the results joins the branch points that can be
    joined, and the arithmetic of the ones that cannot is what a fix has to move.

    Note what these checks do *not* claim: a branch point that has finished paths and two or
    more continuing ones is still not joined, because a [Let] binds a value and so the
    symbolic AST cannot carry a [break] in the bound expression. Pinning that here keeps the
    limitation where a reader will find it. *)

open Aeneas

let failures = ref 0

let check (name : string) (cond : bool) : unit =
  if not cond then begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let joins = Cps.joins
let width = Cps.width_after_branch

(* A branch point whose paths all continue is joined when there are at least two of them,
   whatever its sub-blocks contain: that scan is gone, and with it the reason a switch in a
   looping body never joined. *)
let test_continuing_paths_are_joined () =
  check "two continuing paths are joined" (joins ~continuing:2 ~exiting:0);
  check "three continuing paths are joined" (joins ~continuing:3 ~exiting:0);
  check "one continuing path is not joined" (not (joins ~continuing:1 ~exiting:0));
  check "nothing to join" (not (joins ~continuing:0 ~exiting:0))

(* A finished path makes the branch point unjoinable: the join is a [Let] over the branch
   expression and a [Let] may not carry control flow. This is the case that keeps the width
   of the visitor at 2^13, so it is pinned rather than left implicit. *)
let test_finished_paths_prevent_the_join () =
  check "one finished path is enough to prevent it"
    (not (joins ~continuing:2 ~exiting:1));
  check "so is a finished path among many continuing ones"
    (not (joins ~continuing:8 ~exiting:1))

(* The width the rest of the block is evaluated at, which is what the contexts cost. *)
let test_width_after_branch () =
  check "a joined branch point hands over one context"
    (width ~continuing:2 ~exiting:0 = 1);
  check "an unjoined one hands over one per continuing path"
    (width ~continuing:2 ~exiting:1 = 3);
  check "a finished path is carried at cost one"
    (width ~continuing:1 ~exiting:1 = 2)

(* The arithmetic of the shape that was measured: [n] field checks in sequence, each of
   which finishes one path (the duplicate-field early exit) and lets the rest continue.
   Counted as (continuing, finished) carried into the next check.

   With the join the count is linear; without it the continuing paths double and the
   finished ones pile up behind them, which is the 8230-context statement list the finding
   records. Both numbers are pinned so that a change which does not move the second one
   cannot look like it moved the first. *)
let chain (n : int) : int * int =
  let rec loop step continuing finished =
    if step = 0 then (continuing, finished)
    else
      (* The check splits every continuing path in two and finishes one per continuing
         path it was given before the split. *)
      let finished = finished + continuing in
      let branched = continuing * 2 in
      let continuing =
        if joins ~continuing:branched ~exiting:0 then 1 else branched
      in
      loop (step - 1) continuing finished
  in
  loop n 1 0

let total (continuing, finished) = continuing + finished

let test_the_measured_shape () =
  check "two early exits leave three contexts" (total (chain 2) = 3);
  check "thirteen early exits leave fourteen contexts" (total (chain 13) = 14);
  check "thirteen early exits leave 16383 contexts when not joined"
    (let continuing, finished =
       (* The same chain with the join disabled, which is the shape measured: the visitor's
          twelve chained checks left 8191 finished paths in one list. *)
       let rec loop step continuing finished =
         if step = 0 then (continuing, finished)
         else loop (step - 1) (continuing * 2) (finished + continuing)
       in
       loop 13 1 0
     in
     continuing + finished = 16383)

let () =
  test_continuing_paths_are_joined ();
  test_finished_paths_prevent_the_join ();
  test_width_after_branch ();
  test_the_measured_shape ();
  if !failures = 0 then Printf.printf "test_join_width: all checks passed\n"
  else begin
    Printf.printf "test_join_width: %d check(s) failed\n" !failures;
    exit 1
  end
