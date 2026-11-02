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
