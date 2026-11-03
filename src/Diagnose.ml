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
    : string =
  Printf.sprintf
    "stat t=%.1fs phase=%s live_words=%d live_mib=%.1f heap_words=%d heap_mib=%.1f \
     top_heap_words=%d minor_words=%d major_collections=%d steps=%d env=%d item=%s"
    elapsed phase live_words (words_to_mib live_words) heap_words
    (words_to_mib heap_words) top_heap_words minor_words major_collections steps
    env_len item

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

let bump ?(env = 0) () : unit =
  if sampling_enabled () then begin
    ignore (Atomic.fetch_and_add steps 1);
    Atomic.set env_len env
  end

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
         ~steps:(Atomic.get steps) ~env_len:(Atomic.get env_len))

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
    Atomic.set steps 0
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

