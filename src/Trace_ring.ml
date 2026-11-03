(** A bounded, newest-first trace of values kept for diagnostics.

    A trace exists to be read when something goes wrong, which is exactly when the
    computation is already under stress. Keeping every value it is shown turns a
    bounded computation into an unbounded one: a value can be large (an evaluation
    context holds a whole environment), so an unbounded list grows with the number of
    steps taken rather than with the size of the input, and the run dies before the
    trace is ever printed.

    [push] therefore keeps the newest [capacity] values and drops older ones, so the
    amount retained is independent of how many values were pushed. Oldest-first order
    is available through [to_list], which is what a reader wants when printing.

    Nothing is compared on push: the values are typically large, and a structural
    comparison per push would cost more than the memory it saved. *)

(** How many values a trace keeps by default. Large enough to show the shape of the
    last few iterations, small enough that retaining them cannot matter. *)
let default_capacity = 8

(** [push ?capacity x ring] returns [ring] with [x] as its newest value, dropping the
    oldest value once [capacity] values are held. A capacity of zero retains nothing,
    which is the documented way to turn a trace off entirely. *)
let push ?(capacity = default_capacity) (x : 'a) (ring : 'a list) : 'a list =
  if capacity <= 0 then []
  else if List.length ring < capacity then x :: ring
  else
    (* Keep the newest [capacity - 1] values after the one being added. Dropping the
       oldest here is what makes retention independent of the number of pushes. *)
    x :: List.filteri (fun i _ -> i < capacity - 1) ring

(** The retained values in chronological order, oldest first. *)
let to_list (ring : 'a list) : 'a list = List.rev ring
