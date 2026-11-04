(** Tests for structure sharing in the evaluation environment.

    The synthesis pass keeps one evaluation context per symbolic statement (see
    {!SymbolicAst}), by construction. That is only affordable if a context costs
    the part of the environment which differs from the one it was derived from:
    the environments at a loop fixed point hold every abstraction of the
    function, and a rewrite which rebuilds all of them makes every retained
    context cost a full copy — so the retained memory grows with the size of the
    function times the number of statements, instead of just the number of
    statements.

    These checks pin the contract on the environment-wide map, which is the path
    every context-wide rewrite goes through (destructuring abstractions,
    reducing a context, ending an abstraction, writing through a path): the
    result must share every abstraction the rewrite left alone, and the memory
    the retained result adds must not grow with the number of abstractions.

    All the values involved are immutable, so sharing is observationally
    transparent; the checks below measure it with {!Obj.reachable_words}, which
    counts the blocks reachable from a value once and is therefore what
    retaining that value actually costs. *)

open Aeneas

let failures = ref 0

let check (name : string) (cond : bool) : unit =
  if not cond then begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let span : Meta.span =
  let file : Meta.file =
    { name = Meta.NotReal "test"; crate_name = "test"; contents = None }
  in
  let loc : Meta.loc = { line = 1; col = 0 } in
  { data = { file; beg_loc = loc; end_loc = loc }; generated_from_span = None }

let int_ty : Types.ty = TypesUtils.mk_usize_ty

(** One abstract value, holding a mutable loan: the shape of an abstraction
    which tracks a borrow. *)
let mk_avalue (bid : int) : Values.tavalue =
  let bid = Values.BorrowId.of_int bid in
  let child = ValuesUtils.mk_aignored span int_ty None in
  {
    Values.value = Values.ALoan (Values.AMutLoan (Values.PNone, bid, child));
    ty = int_ty;
  }

(** An abstraction holding [n_avalues] such values. *)
let mk_abs (id : int) (n_avalues : int) : Values.abs =
  {
    abs_id = Values.AbsId.of_int id;
    kind = Values.Identity;
    can_end = true;
    parents = Values.AbsId.Set.empty;
    regions = { Values.owned = Types.RegionSet.empty };
    ended_subabs = Values.AbsLevelSet.empty;
    avalues = List.init n_avalues (fun j -> mk_avalue ((id * n_avalues) + j));
    cont = None;
  }

(** An environment of [n_abs] abstractions. The environment of a context stores
    its elements in reverse order; it doesn't matter here, we only care that a
    rewrite touches a bounded number of them. *)
let mk_env (n_abs : int) : Values.env =
  List.init n_abs (fun id -> Values.EAbs (mk_abs id 8))

(** A rewrite which rebuilds the abstraction it is given, like the context-wide
    rewrites do (destructuring, filtering, reordering): it allocates a new
    abstraction and a new list of abstract values, but the abstract values
    themselves are the ones it was given — this is what "unchanged" looks like
    at the granularity which matters, since an abstraction's values carry the
    continuations of the translation. *)
let rebuild_abs (abs : Values.abs) : Values.abs =
  { abs with avalues = List.map (fun (av : Values.tavalue) -> av) abs.avalues }

let rewrite (target : int) (abs : Values.abs) : Values.abs =
  let abs = rebuild_abs abs in
  if Values.AbsId.to_int abs.abs_id = target then { abs with can_end = false }
  else abs

(** The words reachable from a value: what retaining it actually costs, counting
    shared blocks once. *)
let retained_words (v : 'a) : int = Obj.reachable_words (Obj.repr v)

(* Rewriting one abstraction must not copy the others. This is the property a
   retained context needs: the abstraction which changed is new, everything else
   is the block the previous context already held. *)
let test_retained_delta_is_independent_of_env_size () =
  let env = mk_env 128 in
  let abs_words = retained_words (List.hd env) in
  let env_words = retained_words env in
  let mapped = Contexts.env_map_abs (rewrite 0) env in
  (* Both the original and its successor are alive: this is exactly the state of
     a synthesis pass, which holds one context per statement. *)
  let both = retained_words (env, mapped) in
  let delta = both - env_words in
  check
    (Printf.sprintf
       "a rewritten environment retains %d words on top of the original (%d \
        words for the whole environment, %d for one abstraction) — it must \
        retain about one abstraction, not a second environment"
       delta env_words abs_words)
    (delta < (env_words / 2) + abs_words)

(* The same property, stated in the form that matters for a long function: the
   memory a rewrite adds must not grow with the environment. *)
let test_retained_delta_scaling () =
  let delta_for n_abs =
    let env = mk_env n_abs in
    let env_words = retained_words env in
    let mapped = Contexts.env_map_abs (rewrite 0) env in
    retained_words (env, mapped) - env_words
  in
  let small = delta_for 16 in
  let large = delta_for 256 in
  check
    (Printf.sprintf
       "rewriting one abstraction retains %d words with 16 abstractions and %d \
        words with 256 — the retained cost must not scale with the environment"
       small large)
    (large <= (2 * small) + 64)

(* A rewrite which changes nothing must return the environment itself: the
   common case (most statements leave a given abstraction alone) then costs
   nothing at all to retain. *)
let test_unchanged_env_is_the_original () =
  let env = mk_env 64 in
  let same = Contexts.env_map_abs rebuild_abs env in
  check "mapping an environment with a no-op rewrite returns it unchanged"
    (same == env)

(* A single-point update (the path taken when a loan or a borrow is rewritten,
   see {!InterpBorrowsCore}) must share the rest of the environment: it knows
   that at most one element changes. *)
let test_single_element_update_shares () =
  let env = mk_env 128 in
  let target_words = retained_words (List.nth env 1) in
  let env_words = retained_words env in
  let updated =
    Contexts.env_map_first
      (fun ee ->
        match ee with
        | Values.EAbs abs when Values.AbsId.to_int abs.abs_id = 1 ->
            Some (Values.EAbs (rebuild_abs { abs with can_end = false }))
        | _ -> None)
      env
  in
  let delta = retained_words (env, updated) - env_words in
  check
    (Printf.sprintf
       "a single-point update retains %d words on top of the original (%d \
        words for the environment, %d for the updated element)"
       delta env_words target_words)
    (delta < (env_words / 2) + target_words)

let () =
  test_retained_delta_is_independent_of_env_size ();
  test_retained_delta_scaling ();
  test_unchanged_env_is_the_original ();
  test_single_element_update_shares ();
  if !failures = 0 then Printf.printf "test_ctx_sharing: all checks passed\n"
  else begin
    Printf.printf "test_ctx_sharing: %d check(s) failed\n" !failures;
    exit 1
  end
