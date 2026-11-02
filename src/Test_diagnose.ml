(* Attribution of translator memory to functions.

   The run this exists for is the one that gets killed: `ferrosa_sstable.llbc` reached 18.5
   GiB of anonymous RSS and the cgroup took it, and the Gc statistics that aeneas already
   prints said live data was growing while the heap stayed near 1.4x live. That rules out
   the collector but cannot say *which function* is holding the memory, because the report
   is a whole-process gauge.

   Two decisions are pinned here. The line is streamed per function rather than sorted at
   the end, so a run that never reaches its final report still names the last function it
   finished. And attribution forces one worker: with several domains translating at once a
   per-function live-words delta measures the neighbours too.

   Run with `dune build @runtest` from src/. *)

let failures = ref 0

open Aeneas

let expect (what : string) (expected : string) (actual : string) =
  if expected <> actual then begin
    incr failures;
    Printf.printf "FAIL  %-44s expected %-40s got %s\n" what expected actual
  end
  else Printf.printf "PASS  %-44s %s\n" what actual

let expect_int (what : string) (expected : int) (actual : int) =
  if expected <> actual then begin
    incr failures;
    Printf.printf "FAIL  %-44s expected %-4d got %-4d\n" what expected actual
  end
  else Printf.printf "PASS  %-44s %d\n" what actual

let expect_bool (what : string) (expected : bool) (actual : bool) =
  if expected <> actual then begin
    incr failures;
    Printf.printf "FAIL  %-44s expected %-5b got %-5b\n" what expected actual
  end
  else Printf.printf "PASS  %-44s %b\n" what actual

let () =
  (* 131072 words = 1 MiB, so the unit is checkable by hand. *)
  expect_int "words_to_mib: 1 MiB" 1
    (int_of_float (Diagnose.words_to_mib 131_072));

  (* The streaming line has to survive a kill: one line per finished function, the delta
     signed, and the name last so it reads like an incident log. *)
  expect "memory_line: growth"
    "mem  +256.0 MiB  live   1024.0 MiB  size    4211  rank     3  \
     ferrosa_sstable::compression::Compression::decompress"
    (Diagnose.memory_line
       ~name:"ferrosa_sstable::compression::Compression::decompress"
       ~delta_words:(256 * 131_072) ~live_words:(1024 * 131_072) ~size:4211
       ~rank:3);
  expect "memory_line: negative delta prints its sign"
    "mem   -64.0 MiB  live    512.0 MiB  size      10  rank     9  f"
    (Diagnose.memory_line ~name:"f" ~delta_words:(-(64 * 131_072))
       ~live_words:(512 * 131_072) ~size:10 ~rank:9);

  (* The function that never finishes: its start line is the only evidence a killed run
     leaves naming it. *)
  expect "running_line: names the function in flight"
    "mem    running     live   3072.0 MiB  size  204800  rank     1  \
     ferrosa_sstable::Storage::write_partition"
    (Diagnose.running_line ~name:"ferrosa_sstable::Storage::write_partition"
       ~live_words:(3072 * 131_072) ~size:204_800 ~rank:1);

  (* Attribution needs one worker; asking for more must not silently produce numbers that
     belong to a neighbour. *)
  expect_int "diagnosis forces one worker (asked for 8)" 1
    (Parallel.jobs_for_diagnosis ~diagnose_memory:true ~max_jobs:8);
  expect_int "no diagnosis keeps the planned worker count" 8
    (Parallel.jobs_for_diagnosis ~diagnose_memory:false ~max_jobs:8);
  expect_int "diagnosis with a single worker stays at one" 1
    (Parallel.jobs_for_diagnosis ~diagnose_memory:true ~max_jobs:1);

  (* A run that would be killed by a cgroup ceiling should refuse first, and say what it
     was doing. A zero limit means no limit, so the flag is inert unless asked for. *)
  expect_bool "budget: 0 means unlimited" false
    (Diagnose.over_budget ~limit_mb:0 ~live_words:(4096 * 131_072));
  expect_bool "budget: 99 MiB of a 100 MiB limit is under" false
    (Diagnose.over_budget ~limit_mb:100 ~live_words:(99 * 131_072));
  expect_bool "budget: 101 MiB of a 100 MiB limit is over" true
    (Diagnose.over_budget ~limit_mb:100 ~live_words:(101 * 131_072));

  Printf.printf "\n%s\n"
    (if !failures = 0 then "ALL PASS" else Printf.sprintf "%d FAILED" !failures);
  exit (if !failures = 0 then 0 else 1)
