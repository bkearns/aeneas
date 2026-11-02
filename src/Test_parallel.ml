(* Bounds on the parallel translator.

   `parallel_filter_map` schedules every function at once and lets the pool
   decide: on a 16-core host that is 15 workers, each translating a whole Rust
   function. Aeneas already knows each function's size, so a run can be bounded
   by what is in flight instead of by what is queued -- the measured difference
   on `ferrosa_sstable.llbc` was 8.8+ GiB and climbing versus 2.0 GiB, with the
   cgroup killing the former.

   These cases pin the two bounds independently, because a scheduler that
   respects only one of them still reproduces the failure: capping job count
   does nothing when one function is enormous, and capping cost does nothing
   when the functions are numerous and small.

   Run with `dune build @runtest` from src/. *)

let failures = ref 0

open Aeneas

let expect (what : string) (expected : int) (actual : int) =
  if expected <> actual then begin
    incr failures;
    Printf.printf "FAIL  %-52s expected %-4d got %-4d\n" what expected actual
  end
  else Printf.printf "PASS  %-52s %d\n" what actual

(* What the scheduler is doing right now. Both fields are updated from the
   worker domains, so reads and writes go through the same mutex. *)
type gauge = { mutable running : int; mutable running_cost : int; mutable peak_jobs : int; mutable peak_cost : int; peak_mutex : Mutex.t }

let gauge () =
  { running = 0; running_cost = 0; peak_jobs = 0; peak_cost = 0; peak_mutex = Mutex.create () }

let sample (g : gauge) (cost : int) (delta : int) =
  Mutex.lock g.peak_mutex;
  g.running <- g.running + delta;
  g.running_cost <- g.running_cost + (delta * cost);
  g.peak_jobs <- max g.peak_jobs g.running;
  g.peak_cost <- max g.peak_cost g.running_cost;
  Mutex.unlock g.peak_mutex

let with_gauge (g : gauge) (cost : int) (work : unit -> 'a) : 'a =
  sample g cost 1;
  Fun.protect ~finally:(fun () -> sample g cost (-1)) work

let items n = List.init n (fun i -> i)

(* Hold a worker long enough that two of them are provably alive at once. *)
let spin () =
  for _ = 1 to 200_000 do
    Domain.cpu_relax ()
  done

let () =
  Config.parallel := true;

  (* Two jobs at a time, whatever the costs are. *)
  let g = gauge () in
  let out =
    Parallel.parallel_filter_map_bounded ~cost:(fun _ -> 1) ~budget:1000
      ~max_jobs:2
      (fun x ->
        with_gauge g 1 (fun () ->
            spin ();
            Some (x * 2)))
      (items 10)
  in
  expect "bounded window: peak jobs with max_jobs=2" 2 g.peak_jobs;
  expect "bounded window: results count" 10 (List.length out);

  (* Cost at a time, whatever the job count is. Costs 6,6,4,4,1,1,1,1 with a
     budget of 10 can only ever hold one six and one four. *)
  let g = gauge () in
  let weighted = [ (6, "a"); (6, "b"); (4, "c"); (4, "d"); (1, "e"); (1, "f"); (1, "g"); (1, "h") ] in
  let out =
    Parallel.parallel_filter_map_bounded ~cost:fst ~budget:10 ~max_jobs:8
      (fun (cost, label) ->
        with_gauge g cost (fun () ->
            spin ();
            Some (cost, label)))
      weighted
  in
  if g.peak_cost < 8 || g.peak_cost > 10 then begin
    incr failures;
    Printf.printf "FAIL  %-52s expected 8..10 got %d\n" "bounded window: peak cost with budget=10" g.peak_cost
  end
  else Printf.printf "PASS  %-52s %d\n" "bounded window: peak cost with budget=10" g.peak_cost;
  expect "bounded window: weighted results count" 8 (List.length out);

  (* Order and dropping must match the sequential filter_map exactly. *)
  let input = items 12 in
  let keep = function x when x mod 3 = 0 -> Some x | _ -> None in
  let sequential = List.filter_map keep input in
  let bounded =
    Parallel.parallel_filter_map_bounded ~cost:(fun _ -> 1) ~budget:4 ~max_jobs:3 keep input
  in
  if sequential <> bounded then begin
    incr failures;
    Printf.printf "FAIL  %-52s sequential and bounded results differ\n" "bounded window: order and drops"
  end
  else Printf.printf "PASS  %-52s %s\n" "bounded window: order and drops" "identical";

  (* With parallelism off the bound is trivially one. *)
  Config.parallel := false;
  let g = gauge () in
  ignore
    (Parallel.parallel_filter_map_bounded ~cost:(fun _ -> 1) ~budget:1000
       ~max_jobs:4
       (fun x -> with_gauge g 1 (fun () -> Some x))
       (items 6));
  expect "sequential mode: peak jobs" 1 g.peak_jobs;
  Config.parallel := true;

  (* Every element is visited exactly once, even when the budget is smaller
     than a single element's cost. *)
  let seen = Array.make 8 0 in
  let guarded x =
    let previous = seen.(x) in
    seen.(x) <- previous + 1;
    Some x
  in
  ignore
    (Parallel.parallel_filter_map_bounded ~cost:(fun _ -> 9) ~budget:1 ~max_jobs:2
       guarded (items 8));
  expect "bounded window: elements visited once" 8
    (Array.fold_left (fun acc n -> if n = 1 then acc + 1 else acc) 0 seen);

  (* Worker count follows memory, not cores. Each worker holds the symbolic body of the
     function it translates, and a single large function in a real crate was measured at
     roughly 4 GiB of live data, so a core-counted default is what produced the 18.5 GiB
     run the cgroup killed. *)
  expect "worker count: 30 GiB free, 16 cores" 3
    (Parallel.max_jobs_for ~available_mb:30_000 ~cores:16);
  expect "worker count: 8 GiB free, 16 cores" 1
    (Parallel.max_jobs_for ~available_mb:8_000 ~cores:16);
  expect "worker count: 256 GiB free, 4 cores" 3
    (Parallel.max_jobs_for ~available_mb:256_000 ~cores:4);
  expect "worker count: no memory reading, 16 cores" 15
    (Parallel.max_jobs_for ~available_mb:0 ~cores:16);

  Printf.printf "\n%s\n" (if !failures = 0 then "ALL PASS" else Printf.sprintf "%d FAILED" !failures);
  exit (if !failures = 0 then 0 else 1)
