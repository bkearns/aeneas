(* Attribution of translator memory to the function that holds it.

   The whole-process [Gc] statistics in [Main] say *that* live data is growing and that the
   collector is not the fault; they cannot say which function is holding it. On a crate
   whose translation is killed at a memory ceiling that is the only question worth asking,
   so these lines are printed as each function finishes: a run that dies before its final
   report still names the last function it completed, and the one after it is the suspect.

   Attribution needs one worker -- with several domains translating at once, a delta
   measures the neighbours too -- which [Parallel.jobs_for_diagnosis] enforces. *)

(** 8 bytes a word, 1 MiB = 131072 words. *)
let words_to_mib (words : int) : float = float_of_int words *. 8.0 /. 1048576.0

(** One line per finished function: the live-words change it caused, the live total after
    it, its size and rank, and its name last so the log reads like an incident trail. *)
let memory_line ~(name : string) ~(delta_words : int) ~(live_words : int)
    ~(size : int) ~(rank : int) : string =
  Printf.sprintf "mem%+8.1f MiB  live %8.1f MiB  size %7d  rank %5d  %s"
    (words_to_mib delta_words) (words_to_mib live_words) size rank name

let log_memory ~(name : string) ~(delta_words : int) ~(live_words : int)
    ~(size : int) ~(rank : int) : unit =
  prerr_endline (memory_line ~name ~delta_words ~live_words ~size ~rank);
  flush stderr

(** The function being translated right now, printed before it starts.

    A run killed inside one function has no completed line for it -- the kill is the
    evidence that it never finished -- so the last [running] line is what names the
    culprit. *)
let running_line ~(name : string) ~(live_words : int) ~(size : int)
    ~(rank : int) : string =
  Printf.sprintf "mem    running     live %8.1f MiB  size %7d  rank %5d  %s"
    (words_to_mib live_words) size rank name

let log_running ~(name : string) ~(live_words : int) ~(size : int)
    ~(rank : int) : unit =
  prerr_endline (running_line ~name ~live_words ~size ~rank);
  flush stderr

(** Whether live data has passed the run's memory budget.

    A run that exceeds a ceiling set by the caller should refuse where it stands, naming
    the function it just finished, instead of being killed by a cgroup and leaving the
    caller to guess. [0] is no limit. *)
let over_budget ~(limit_mb : int) ~(live_words : int) : bool =
  limit_mb > 0 && words_to_mib live_words > float_of_int limit_mb

(** The refusal itself: what was being translated, how much was live, what the caller asked
    for. Written to stderr because that is where the streamed lines already are. *)
let budget_message ~(limit_mb : int) ~(live_words : int) ~(last : string) : string =
  Printf.sprintf
    "FAIL: memory limit of %d MiB exceeded (live %.0f MiB) after translating %s\n\
     Refusing rather than being killed: this crate needs -max-parallel-jobs 1, a \
     narrower charon scope, or a higher -memory-limit-mb."
    limit_mb (words_to_mib live_words) last

(* ------------------------------------------------------------------------------------ *)
(* Streaming samples to a file, so that a run killed outright still leaves a record.     *)
(* ------------------------------------------------------------------------------------ *)

(* A run that hits a cgroup ceiling is killed with SIGKILL. No handler runs, no [at_exit]
   runs, and the process's buffered output may never reach the caller: the one run that
   most needs to say what it was doing says nothing. So samples go to a *file* named by
   [AENEAS_STAT_FILE], one line per sample, opened and closed per write, so the bytes are
   on disk before the next allocation. Reporting is off unless that variable is set, which
   keeps the translator's normal output unchanged.

   Each line carries the phase ("prepasses", "transparent-functions", ...) and, where it
   applies, the declaration being translated, because "live 4.9 GiB" alone does not tell a
   reader which pass to look at. [AENEAS_STAT_INTERVAL] sets the sampling period in
   seconds (default 5). *)

let stat_file_env = "AENEAS_STAT_FILE"
let stat_interval_env = "AENEAS_STAT_INTERVAL"

let stat_path () =
  match Sys.getenv_opt stat_file_env with
  | Some p when String.trim p <> "" -> Some p
  | _ -> None

(** Sampling is opt-in, and call sites may test this before doing naming work. *)
let sampling_enabled () = Option.is_some (stat_path ())

let stat_interval () =
  match Sys.getenv_opt stat_interval_env with
  | Some s -> (
      match float_of_string_opt (String.trim s) with
      | Some f when f > 0. -> f
      | _ -> 5.)
  | None -> 5.

let started_at = Unix.gettimeofday ()
let phase : string Atomic.t = Atomic.make "startup"
let current_item : string Atomic.t = Atomic.make ""

(** One sample, as text: elapsed time, phase, declaration, then the counters. Kept as a
    pure function so the format can be tested without a file or a translator. *)
let sample_line ~(elapsed : float) ~(phase : string) ~(item : string)
    ~(live_words : int) ~(heap_words : int) ~(top_heap_words : int)
    ~(minor_words : int) ~(major_collections : int) ~(steps : int) ~(env_len : int)
    ~(env_vars : int) ~(env_dummies : int) ~(env_abs : int)
    ?(probe : string = "") () : string =
  Printf.sprintf
    "stat t=%.1fs phase=%s live_words=%d live_mib=%.1f heap_words=%d heap_mib=%.1f \
     top_heap_words=%d minor_words=%d major_collections=%d steps=%d env=%d vars=%d \
     dummies=%d abs=%d%s item=%s"
    elapsed phase live_words (words_to_mib live_words) heap_words
    (words_to_mib heap_words) top_heap_words minor_words major_collections steps
    env_len env_vars env_dummies env_abs
    (if probe = "" then "" else " " ^ probe)
    item

let write_lock = Mutex.create ()

(* Open, write, close: a sample that is buffered in the process when the kernel kills it
   would be worth nothing, and a file that survives the kill is the whole point. *)
let append (line : string) : unit =
  match stat_path () with
  | None -> ()
  | Some path -> (
      Mutex.protect write_lock (fun () ->
          match
            open_out_gen [ Open_append; Open_creat; Open_wronly ] 0o644 path
          with
          | exception Sys_error _ -> ()
          | oc ->
              (try
                 output_string oc (line ^ "\n");
                 flush oc
               with Sys_error _ -> ());
              close_out_noerr oc))

(** Work performed, as opposed to data held.

    Samples alone show *that* live data grows; the counter shows whether the growth is
    spread over many cheap steps (accumulation) or sitting inside one step (a single
    quadratic operation). [bump] is called per evaluated statement and reset when the
    declaration changes, so between two samples the counter says how many statements were
    evaluated and the next sample's live delta says what they cost. *)
let steps : int Atomic.t = Atomic.make 0
let env_len : int Atomic.t = Atomic.make 0
let env_vars : int Atomic.t = Atomic.make 0
let env_dummies : int Atomic.t = Atomic.make 0
let env_abs : int Atomic.t = Atomic.make 0

let bump ?(env = 0) ?(vars = 0) ?(dummies = 0) ?(abs = 0) () : unit =
  if sampling_enabled () then begin
    ignore (Atomic.fetch_and_add steps 1);
    Atomic.set env_len env;
    Atomic.set env_vars vars;
    Atomic.set env_dummies dummies;
    Atomic.set env_abs abs
  end

(* --- How wide a body gets, and why ------------------------------------------------ *)

(* Symbolic execution returns one evaluation context per path of a body, and a context
   holds a whole environment, so the width of that list is what the body costs. Two things
   widen it: a branching statement whose branches are joined collapses back to one
   context, and one whose branches are not joined keeps them apart -- either because a
   branch leaves the block (break, continue, return), where joining is not attempted, or
   because the join failed, where it is attempted and gives up. A failed join is
   recoverable by default and duplicates the code after the branch silently, so from the
   outside the two cases look the same. Which of them produces the width decides the fix:
   if it is failures, joining harder narrows the list; if it is paths that legitimately
   leave, nothing about joining helps and the list is what has to stop being materialized.

   The widths are summed rather than averaged because a width is a product of the branch
   points on the way to it: the sum says which cause accounts for the paths that exist. *)

(** What happened at a branching statement whose branches produced [width] contexts. *)
type join_outcome =
  | Joined  (** one context out; the rest of the block is evaluated once *)
  | Failed  (** the join raised; the paths stay separate and the rest is duplicated *)
  | Skipped  (** a branch leaves the block; joining is not attempted *)

let join_counts : int Atomic.t array =
  [| Atomic.make 0; Atomic.make 0; Atomic.make 0 |]

let join_widths : int Atomic.t array =
  [| Atomic.make 0; Atomic.make 0; Atomic.make 0 |]

let join_width_max : int Atomic.t array =
  [| Atomic.make 0; Atomic.make 0; Atomic.make 0 |]

(** Where the widest list came from, so a number in a log names a statement. *)
let join_where : string Atomic.t array =
  [| Atomic.make ""; Atomic.make ""; Atomic.make "" |]

let join_continuing_max : int Atomic.t array =
  [| Atomic.make 0; Atomic.make 0; Atomic.make 0 |]

let skip_continuing : int Atomic.t = Atomic.make 0

let ctx_list_where : string Atomic.t = Atomic.make ""

let index_of = function Joined -> 0 | Failed -> 1 | Skipped -> 2

(** One branching statement: how many contexts its branches ended in, and what was done
    with them.

    [continuing] is how many of those contexts carry [Unit] -- the ones that go on to be
    evaluated on the rest of the block. A context that carries [Break], [Continue] or
    [Return] is finished: the rest of the block is not evaluated on it, so it does not
    widen anything. Counting the two apart says whether a width is a set of paths that
    really do continue side by side, or a set of exits that only look like paths. *)
let note_switch_join ~(outcome : join_outcome) ~(width : int)
    ~(continuing : int) ~(where : unit -> string) : unit =
  if sampling_enabled () then begin
    let i = index_of outcome in
    ignore (Atomic.fetch_and_add join_counts.(i) 1);
    ignore (Atomic.fetch_and_add join_widths.(i) width);
    if width > Atomic.get join_width_max.(i) then begin
      Atomic.set join_width_max.(i) width;
      (* [where] is forced only here: naming a statement costs a lookup and a string. *)
      Atomic.set join_where.(i) (where ());
      Atomic.set join_continuing_max.(i) continuing
    end;
    if outcome = Skipped then begin
      ignore (Atomic.fetch_and_add skip_continuing continuing)
    end
  end

(** Where the contexts a statement list ends in came from.

    A list is wide either because the paths in it really do run side by side -- each has to
    be evaluated on the rest of the block -- or because it also carries the paths that have
    already finished, which nothing evaluates again. Only the first kind can be narrowed by
    joining; the second is pure retention, and the only fix is to stop keeping it. Summing
    the two apart across a declaration says which it is, without a per-statement log. *)
let origin_units : int Atomic.t = Atomic.make 0
let origin_exits : int Atomic.t = Atomic.make 0
let origin_max_exits : int Atomic.t = Atomic.make 0

let note_list_origins ~(units : int) ~(exits : int) : unit =
  if sampling_enabled () then begin
    ignore (Atomic.fetch_and_add origin_units units);
    ignore (Atomic.fetch_and_add origin_exits exits);
    if exits > Atomic.get origin_max_exits then Atomic.set origin_max_exits exits
  end

(** A branch point that was not joined, bucketed by how many of its results continue.

    A switch that leaves the block from one arm still has the other arms' contexts
    continuing side by side, and today the whole switch declines to join as soon as any arm
    can leave. So the bucket says whether the width is one continuing context per exit --
    which no join helps -- or several, which a join would collapse to one. *)
let skip_unit_buckets = 4

let skip_by_units : int Atomic.t array =
  Array.init skip_unit_buckets (fun _ -> Atomic.make 0)

let skip_width_by_units : int Atomic.t array =
  Array.init skip_unit_buckets (fun _ -> Atomic.make 0)

let skip_maxwidth_by_units : int Atomic.t array =
  Array.init skip_unit_buckets (fun _ -> Atomic.make 0)

let bucket_of_units n =
  if n < 0 then 0 else if n >= skip_unit_buckets - 1 then skip_unit_buckets - 1 else n

let note_skip_shape ~(units : int) ~(width : int) : unit =
  if sampling_enabled () then begin
    let b = bucket_of_units units in
    ignore (Atomic.fetch_and_add skip_by_units.(b) 1);
    ignore (Atomic.fetch_and_add skip_width_by_units.(b) width);
    if width > Atomic.get skip_maxwidth_by_units.(b) then
      Atomic.set skip_maxwidth_by_units.(b) width
  end

(** The shape of the widest list seen: how many of its contexts continue, how many are
    finished, and how wide each of the branch point's arms was. Arm widths say whether the
    width is one arm or all of them, which decides whether joining or retention is the
    lever. *)
let widest_shape : string Atomic.t = Atomic.make ""

let note_shape ~(width : int) ~(units : int) ~(exits : int) ~(arms : int list)
    ~(where : string) : unit =
  if sampling_enabled () then begin
    let current =
      match Atomic.get widest_shape with
      | "" -> 0
      | s -> (
          match String.index_opt s ' ' with
          | Some i -> ( try int_of_string (String.sub s 2 (i - 2)) with _ -> 0)
          | None -> 0)
    in
    if width > current then
      Atomic.set widest_shape
        (Printf.sprintf "w=%d units=%d exits=%d arms=[%s] at=[%s]" width units
           exits
           (String.concat "," (List.map string_of_int arms))
           where)
  end

let ctx_list_count : int Atomic.t = Atomic.make 0
let ctx_list_width : int Atomic.t = Atomic.make 0
let ctx_list_width_max : int Atomic.t = Atomic.make 0

(** One statement list, and the number of paths it ended in. *)
let note_ctx_list ~(width : int) ~(where : unit -> string) : unit =
  if sampling_enabled () then begin
    ignore (Atomic.fetch_and_add ctx_list_count 1);
    ignore (Atomic.fetch_and_add ctx_list_width width);
    if width > Atomic.get ctx_list_width_max then begin
      Atomic.set ctx_list_width_max width;
      Atomic.set ctx_list_where (where ())
    end
  end

let loop_body_paths : int Atomic.t = Atomic.make 0
let loop_body_paths_max : int Atomic.t = Atomic.make 0
let loop_body_evals : int Atomic.t = Atomic.make 0

(** One evaluation of a loop body done only to learn where it goes: the number of paths it
    ended in, all of them held at once. *)
let note_loop_body ~(paths : int) : unit =
  if sampling_enabled () then begin
    ignore (Atomic.fetch_and_add loop_body_evals 1);
    ignore (Atomic.fetch_and_add loop_body_paths paths);
    if paths > Atomic.get loop_body_paths_max then
      Atomic.set loop_body_paths_max paths
  end

(* How a body's paths end. A path that ends in [Unit] goes on to the rest of the block; one
   that ends in [Break], [Continue], [Return] or [Panic] is finished. The split is what says
   whether a width is a set of states that really do continue side by side -- which joining
   could merge -- or a set of exits, which it cannot. *)

let path_units : int Atomic.t = Atomic.make 0
let path_breaks : int Atomic.t = Atomic.make 0
let path_continues : int Atomic.t = Atomic.make 0
let path_returns : int Atomic.t = Atomic.make 0
let path_panics : int Atomic.t = Atomic.make 0

let note_path_kinds ~(unit : int) ~(brk : int) ~(cont : int) ~(ret : int)
    ~(panic : int) : unit =
  if sampling_enabled () then begin
    ignore (Atomic.fetch_and_add path_units unit);
    ignore (Atomic.fetch_and_add path_breaks brk);
    ignore (Atomic.fetch_and_add path_continues cont);
    ignore (Atomic.fetch_and_add path_returns ret);
    ignore (Atomic.fetch_and_add path_panics panic)
  end

(** What one more retained path costs on top of the first one: the words reachable from
    both, minus the words reachable from the first. Kept because it is the number that
    decides whether a wide list is a list of states or a list of pointers at one state. *)
let path_marginal_n : int Atomic.t = Atomic.make 0
let path_marginal_words : int Atomic.t = Atomic.make 0
let path_marginal_max : int Atomic.t = Atomic.make 0
let path_first_words : int Atomic.t = Atomic.make 0

let note_path_marginal ~(words : int) ~(first : int) : unit =
  if sampling_enabled () then begin
    ignore (Atomic.fetch_and_add path_marginal_n 1);
    ignore (Atomic.fetch_and_add path_marginal_words words);
    if words > Atomic.get path_marginal_max then
      Atomic.set path_marginal_max words;
    Atomic.set path_first_words first
  end

let reset_probe () : unit =
  if sampling_enabled () then begin
    Array.iter (fun a -> Atomic.set a 0) join_counts;
    Array.iter (fun a -> Atomic.set a 0) join_widths;
    Array.iter (fun a -> Atomic.set a 0) join_width_max;
    Array.iter (fun a -> Atomic.set a 0) join_continuing_max;
    Array.iter (fun a -> Atomic.set a "") join_where;
    Atomic.set skip_continuing 0;
    Atomic.set ctx_list_count 0;
    Atomic.set ctx_list_width 0;
    Atomic.set ctx_list_width_max 0;
    Atomic.set ctx_list_where "";
    Atomic.set loop_body_paths 0;
    Atomic.set loop_body_paths_max 0;
    Atomic.set loop_body_evals 0;
    Atomic.set path_units 0;
    Atomic.set path_breaks 0;
    Atomic.set path_continues 0;
    Atomic.set path_returns 0;
    Atomic.set path_panics 0;
    Atomic.set path_marginal_n 0;
    Atomic.set path_marginal_words 0;
    Atomic.set path_marginal_max 0;
    Atomic.set path_first_words 0;
    Atomic.set origin_units 0;
    Atomic.set origin_exits 0;
    Atomic.set origin_max_exits 0;
    Array.iter (fun a -> Atomic.set a 0) skip_by_units;
    Array.iter (fun a -> Atomic.set a 0) skip_width_by_units;
    Array.iter (fun a -> Atomic.set a 0) skip_maxwidth_by_units;
    Atomic.set widest_shape ""
  end

(** [sum] / [count], or 0 when nothing was counted. *)
let mean (sum : int Atomic.t) (count : int Atomic.t) : int =
  match Atomic.get count with 0 -> 0 | n -> Atomic.get sum / n

let probe_text () : string =
  if not (sampling_enabled ()) then ""
  else
    let one name i =
      Printf.sprintf "%s_n=%d %s_avg=%d %s_max=%d %s_cont=%d %s_at=[%s]" name
        (Atomic.get join_counts.(i)) name
        (mean join_widths.(i) join_counts.(i))
        name
        (Atomic.get join_width_max.(i)) name
        (Atomic.get join_continuing_max.(i)) name
        (Atomic.get join_where.(i))
    in
    String.concat " "
      [
        one "joined" 0;
        one "failed" 1;
        one "skipped" 2;
        Printf.sprintf "skip_cont_sum=%d" (Atomic.get skip_continuing);
        Printf.sprintf "ctxlist_n=%d ctxlist_avg=%d ctxlist_max=%d ctxlist_at=[%s]"
          (Atomic.get ctx_list_count)
          (mean ctx_list_width ctx_list_count)
          (Atomic.get ctx_list_width_max)
          (Atomic.get ctx_list_where);
        Printf.sprintf "loopbody_n=%d loopbody_avg=%d loopbody_max=%d"
          (Atomic.get loop_body_evals)
          (mean loop_body_paths loop_body_evals)
          (Atomic.get loop_body_paths_max);
        Printf.sprintf
          "kinds unit=%d break=%d cont=%d ret=%d panic=%d marginal_n=%d \
           marginal_avg_w=%d marginal_max_w=%d first_w=%d"
          (Atomic.get path_units) (Atomic.get path_breaks)
          (Atomic.get path_continues) (Atomic.get path_returns)
          (Atomic.get path_panics)
          (Atomic.get path_marginal_n)
          (mean path_marginal_words path_marginal_n)
          (Atomic.get path_marginal_max)
          (Atomic.get path_first_words);
        Printf.sprintf "origins units=%d exits=%d max_exits=%d"
          (Atomic.get origin_units) (Atomic.get origin_exits)
          (Atomic.get origin_max_exits);
        Printf.sprintf "skips_units[0]=%d/avg%d/max%d [1]=%d/avg%d/max%d [2]=%d/avg%d/max%d \
                        [3+]=%d/avg%d/max%d"
          (Atomic.get skip_by_units.(0))
          (mean skip_width_by_units.(0) skip_by_units.(0))
          (Atomic.get skip_maxwidth_by_units.(0))
          (Atomic.get skip_by_units.(1))
          (mean skip_width_by_units.(1) skip_by_units.(1))
          (Atomic.get skip_maxwidth_by_units.(1))
          (Atomic.get skip_by_units.(2))
          (mean skip_width_by_units.(2) skip_by_units.(2))
          (Atomic.get skip_maxwidth_by_units.(2))
          (Atomic.get skip_by_units.(3))
          (mean skip_width_by_units.(3) skip_by_units.(3))
          (Atomic.get skip_maxwidth_by_units.(3));
        Printf.sprintf "widest=(%s)" (Atomic.get widest_shape);
      ]

(** Write one sample now. Cheap when sampling is off. *)
let sample () : unit =
  if sampling_enabled () then
    let st = Gc.quick_stat () in
    append
      (sample_line ~elapsed:(Unix.gettimeofday () -. started_at)
         ~phase:(Atomic.get phase) ~item:(Atomic.get current_item)
         ~live_words:st.Gc.live_words ~heap_words:st.Gc.heap_words
         ~top_heap_words:st.Gc.top_heap_words
         ~minor_words:(int_of_float st.Gc.minor_words)
         ~major_collections:st.Gc.major_collections
         ~steps:(Atomic.get steps) ~env_len:(Atomic.get env_len)
         ~env_vars:(Atomic.get env_vars) ~env_dummies:(Atomic.get env_dummies)
         ~env_abs:(Atomic.get env_abs) ~probe:(probe_text ()) ())

(** Enter a phase: record it immediately, so even a short phase names itself, then keep
    sampling. Every phase boundary is a sample, which is what makes a killed run's file
    say where it died even if the sampling domain never got to run. [clear_item] is false
    for a sub-pass of the declaration already in flight (symbolic execution, translation to
    the pure AST), where the item must stay named. *)
let set_phase ?(clear_item = true) (p : string) : unit =
  if sampling_enabled () then begin
    Atomic.set phase p;
    if clear_item then Atomic.set current_item "";
    sample ()
  end

(** The declaration in flight, so the last line of a killed run names it. Called from
    worker domains, hence atomics. *)
let set_item (i : string) : unit =
  if sampling_enabled () then begin
    Atomic.set current_item i;
    (* [steps] is per declaration: a sample of a new function starts at zero, so the
       counter reads as "statements evaluated in this function". *)
    Atomic.set steps 0;
    reset_probe ()
  end

let sampler_started = ref false

(** Sample every [stat_interval] seconds from a domain of its own.

    Deliberately not a signal handler: the previous approach used [ITIMER_REAL] with a
    SIGALRM handler, which does fire, but its output goes to stderr and is therefore lost
    with the process when the ceiling kills it -- and a handler that raises or is
    overwritten silently disables all reporting. A domain that only sleeps and writes
    a file has neither failure mode. *)
let start_sampler () : unit =
  if sampling_enabled () && not !sampler_started then begin
    sampler_started := true;
    sample ();
    (* Bytecode has no domains and [Domain.spawn] raises there; phase boundaries still
       sample, so reporting degrades instead of failing. *)
    try
      ignore
        (Domain.spawn (fun () ->
             while true do
               Unix.sleepf (stat_interval ());
               sample ()
             done))
    with _ -> ()
  end

