(** This module defines various utilities to write the interpretation functions
    in continuation passing style. *)

open Contexts
open Errors

(** TODO: change the name *)
type eval_error = EPanic

(** Result of evaluating a statement *)
type statement_eval_res =
  | Unit
  | Break of int
  | Continue of int
  | Return
  | Panic
      (** TODO: this one should only be used in concrete executions, not when
          synthesizing code *)
[@@deriving show]

(** Function which takes a context as input, and evaluates to:
    - a new context
    - a continuation with which to build the execution trace, provided the trace
      for the end of the execution. *)
type cm_fun = eval_ctx -> eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr)

type st_cm_fun =
  eval_ctx ->
  (eval_ctx * statement_eval_res) * (SymbolicAst.expr -> SymbolicAst.expr)

(** Type of a function used when evaluating a statement *)
type stl_cm_fun =
  eval_ctx ->
  (eval_ctx * statement_eval_res) list
  * (SymbolicAst.expr list -> SymbolicAst.expr)

(** Compose continuations that we use to compute execution traces *)
let cc_comp (f : 'b -> 'c) (g : 'a -> 'b) : 'a -> 'c = fun e -> f (g e)

(** Whether the caller of a statement evaluation will consume the trace it builds.

    Evaluating a statement returns the contexts it ends in *and* a continuation that
    rebuilds the symbolic AST. The continuation is a chain of closures, one per statement
    evaluated, and each closure keeps the evaluation context it was built with alive: an
    environment is a few hundred bindings, so the chain costs memory proportional to the
    number of statements in the body rather than to the size of its result. Some passes
    never use the trace -- the search for a loop fixed point evaluates a body repeatedly
    only to learn where it goes and how the context evolves, and drops the trace every
    time -- and on a body of 10^5 statements that discarded chain is the largest thing in
    the heap. Those passes run under {!without_trace}, and {!trace_needed} tells
    {!InterpStatements.eval_statement_list} to compose nothing.

    Domain-local rather than a [Config] flag: functions are translated in parallel, so a
    global switch would silence the trace of every other function too. *)
let trace_needed_key : bool Domain.DLS.key = Domain.DLS.new_key (fun () -> true)

(** Whether the caller will consume the execution trace. *)
let trace_needed () : bool = Domain.DLS.get trace_needed_key

(** Run [f] in a state where the trace is not needed. Restored on exception, so a failure
    inside a loop body does not leave the rest of the translation with no trace. *)
let without_trace (f : unit -> 'a) : 'a =
  let previous = Domain.DLS.get trace_needed_key in
  Domain.DLS.set trace_needed_key false;
  Fun.protect
    ~finally:(fun () -> Domain.DLS.set trace_needed_key previous)
    f

(** Compose the trace of one statement with the trace of the rest of the block.

    This is where a statement's node joins the chain, so it is also where a pass that does
    not want the chain says so: rather than returning `cf_st1` composed with `cf_st2` --
    which keeps the statement's context reachable for as long as the caller holds the
    trace -- it returns a continuation that would fail if applied, exactly as
    {!InterpLoops.eval_loop_concrete} does. Callers that discard the trace never apply it,
    so the difference is invisible in the result and it is the difference between O(1) and
    O(statements) live contexts.

    Kept polymorphic in the expression type so that this module does not need to know
    about the symbolic AST. *)
let compose_trace (span : Meta.span) (cf_st1 : 'b -> 'c) (cf_st2 : 'a -> 'b) : 'a -> 'c
    =
  if trace_needed () then cc_comp cf_st1 cf_st2 else fun _ -> [%internal_error] span

let comp (f : 'b -> 'c) (g : 'x * ('a -> 'b)) : 'x * ('a -> 'c) =
  let x, g = g in
  (x, cc_comp f g)

let comp2 (f : 'b -> 'c) (g : 'x * 'y * ('a -> 'b)) : 'x * 'y * ('a -> 'c) =
  let x, y, g = g in
  (x, y, cc_comp f g)

(** [fold] operation for functions which thread a context and return a
    continuation *)
let fold_left_apply_continuation (f : 'a -> 'c -> 'c * ('e -> 'e))
    (inputs : 'a list) (ctx : 'c) : 'c * ('e -> 'e) =
  let rec eval_list (inputs : 'a list) : 'c -> 'b =
   fun ctx ->
    match inputs with
    | [] -> (ctx, fun x -> x)
    | x :: inputs ->
        let ctx, cc = f x ctx in
        comp cc (eval_list inputs ctx)
  in
  eval_list inputs ctx

(** [map] operation for functions which thread a context and return a
    continuation *)
let map_apply_continuation (f : 'a -> 'c -> 'b * 'c * ('e -> 'e))
    (inputs : 'a list) (ctx : 'c) : 'b list * 'c * ('e -> 'e) =
  let rec eval_list (inputs : 'a list) (ctx : 'c) : 'b list * 'c * ('e -> 'e) =
    match inputs with
    | [] -> ([], ctx, fun e -> e)
    | x :: inputs ->
        let v, ctx, cc1 = f x ctx in
        let vl, ctx, cc2 = eval_list inputs ctx in
        (v :: vl, ctx, cc_comp cc1 cc2)
  in
  eval_list inputs ctx

let cc_singleton file line span cf el =
  match el with
  | [ e ] -> cf e
  | _ -> internal_error file line span

let cf_singleton file line span el =
  match el with
  | [ e ] -> e
  | _ -> internal_error file line span

let cf_empty file line span e el =
  match el with
  | [] -> e
  | _ -> internal_error file line span

(** Whether a branch point's branches should be joined, from what they ended in.

    [continuing] paths go on to the rest of the block and [exiting] ones have finished
    ([break], [continue], [return] or a panic). Two or more continuing paths are worth
    merging -- the rest of the block is then evaluated once instead of once per path -- and
    a finished path cannot be merged with anything. The answers have to come from the
    results rather than from inspecting the sub-blocks: a block's tail holds the enclosing
    loop's own [break], so a syntactic scan says "can leave" about almost every branch point
    in a body that loops or returns, and an over-cautious [No] here is paid for by
    duplicating the rest of the block at every branch.

    [exiting > 0] is a [No] for a reason that is structural rather than cautious: joining is
    a [Let] over the branch expression, and {!SymbolicToPureExpressions.translate_let}
    forbids [break], [continue] and [return] in a bound expression. *)
let joins ~(continuing : int) ~(exiting : int) : bool =
  continuing >= 2 && exiting = 0

(** How wide a branch point leaves the rest of the block's input.

    Kept next to {!joins} because it is the same arithmetic seen from the other side: a
    joined branch point hands over one context however many branches it had, an unjoined one
    hands over one per continuing branch, and a finished branch hands over a context that is
    carried but never evaluated. *)
let width_after_branch ~(continuing : int) ~(exiting : int) : int =
  (if joins ~continuing ~exiting then 1 else continuing) + exiting

(** It happens that we need to concatenate lists of results, for instance when
    evaluating the branches of a match. When applying the continuations to build
    the symbolic expressions, we need to decompose the list of expressions we
    get to give it to the individual continuations for the branches. *)
let comp_seqs (file : string) (line : int) (span : Meta.span)
    (ls : ('a list * (SymbolicAst.expr list -> SymbolicAst.expr)) list) :
    'a list * (SymbolicAst.expr list -> SymbolicAst.expr list) =
  (* Auxiliary function: given a list of expressions el, build the expressions
     corresponding to the different branches *)
  let rec cc ls el =
    match ls with
    | [] ->
        (* End of the list of branches: there shouldn't be any expression remaining *)
        sanity_check file line span (el = []);
        []
    | (resl, cf) :: ls ->
        (* Split the list of expressions between:
           - the expressions for the current branch
           - the expressions for the remaining branches *)
        let el0, el = Collections.List.split_at el (List.length resl) in
        (* Compute the expression for the current branch *)
        let e0 = cf el0 in
        (* Compute the expressions for the remaining branches *)
        let e = cc ls el in
        (* Concatenate *)
        e0 :: e
  in
  (List.flatten (fst (List.split ls)), cc ls)
