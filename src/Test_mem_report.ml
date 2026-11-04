(* What a killed run leaves behind.

   A translator that dies at a memory ceiling is killed with SIGKILL. Nothing in the
   process runs on the way out -- no [at_exit], no signal handler -- so the report has to be
   on disk *before* the kill. This test starts a child that samples into a file, has it
   killed the way a ceiling kills (see below), and insists the file still says which phase
   it was in and how much live data it held.

   Two sinks are compared, because "printed on exit" is the failure mode: [sample_line] is
   checked as text, and the survival case is checked against a real file written by a real
   killed process.

   Run with `dune build @runtest` from src/. *)

let failures = ref 0

open Aeneas

let check (what : string) (cond : bool) (detail : string) =
  if cond then Printf.printf "PASS  %s\n" what
  else begin
    incr failures;
    Printf.printf "FAIL  %s%s\n" what (if detail = "" then "" else "  (" ^ detail ^ ")")
  end

let contains haystack needle =
  let n = String.length needle and h = String.length haystack in
  let rec go i = i + n <= h && (String.sub haystack i n = needle || go (i + 1)) in
  n = 0 || go 0

(* ------------------------------------------------------------------------------------ *)
(* The line format                                                                        *)
(* ------------------------------------------------------------------------------------ *)

let test_line () =
  let line =
    Diagnose.sample_line ~elapsed:12.5 ~phase:"transparent-functions"
      ~item:"crate::metadata::visit_map" ~live_words:(4 * 131072) ~heap_words:(5 * 131072)
      ~top_heap_words:(6 * 131072) ~minor_words:1000 ~major_collections:7 ~steps:42
      ~env_vars:7 ~env_dummies:25 ~env_abs:5
      ~env_len:37 ()
  in
  check "sample names its phase" (contains line "phase=transparent-functions") line;
  check "sample reports live words" (contains line "live_words=524288") line;
  check "sample reports heap words" (contains line "heap_words=655360") line;
  check "sample names the declaration" (contains line "item=crate::metadata::visit_map")
    line;
  check "sample is a single line" (not (contains line "\n")) line

(* ------------------------------------------------------------------------------------ *)
(* A killed child still leaves a record                                                   *)
(* ------------------------------------------------------------------------------------ *)

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    close_in ic;
    s
  with Sys_error _ -> ""

(* Poll until [path] holds at least one non-empty line, or the deadline passes. A complete
   line is the unit that matters: a half-written line would not name a phase. *)
let wait_for_record ~(path : string) ~(timeout : float) : bool =
  let deadline = Unix.gettimeofday () +. timeout in
  let rec go () =
    let s = read_file path in
    if contains s "phase=" && contains s "\n" then true
    else if Unix.gettimeofday () > deadline then false
    else begin
      ignore (Unix.select [] [] [] 0.02);
      go ()
    end
  in
  go ()

let wait_exit ~(pid : int) ~(timeout : float) : Unix.process_status option =
  let deadline = Unix.gettimeofday () +. timeout in
  let rec go () =
    match Unix.waitpid [ Unix.WNOHANG ] pid with
    | 0, _ ->
        if Unix.gettimeofday () > deadline then None
        else begin
          ignore (Unix.select [] [] [] 0.02);
          go ()
        end
    | _, status -> Some status
  in
  go ()

(* Is a memory ceiling available? A cgroup is what the real failure is (SIGKILL from the
   kernel, unhandleable), so use one when this host has a user manager; otherwise fall back
   to sending SIGKILL ourselves, which is the same signal and the same absence of cleanup. *)
let scope_available () =
  Sys.command "systemd-run --user --version >/dev/null 2>&1" = 0

let test_killed_child_leaves_record () =
  let path = Filename.temp_file "aeneas-stat" ".log" in
  Sys.remove path;
  Unix.putenv Diagnose.stat_file_env path;
  Unix.putenv Diagnose.stat_interval_env "0.05";
  let self = Sys.executable_name in
  let scoped = scope_available () in
  let prog, argv =
    if scoped then
      ( "systemd-run",
        [| "systemd-run"; "--user"; "--scope"; "--quiet"; "--collect"; "-p";
           "MemoryMax=256M"; "-p"; "MemorySwapMax=0"; self; "--memstat-child" |] )
    else (self, [| self; "--memstat-child" |])
  in
  let devnull = Unix.openfile "/dev/null" [ Unix.O_RDONLY ] 0 in
  let pid =
    Unix.create_process prog argv devnull Unix.stderr Unix.stderr
  in
  Unix.close devnull;
  let recorded = wait_for_record ~path ~timeout:30. in
  check "killed child wrote a record before dying" recorded path;
  (* Out of scope we are the executioner; in a scope the ceiling is. Either way the child
     must not be left running. *)
  if not scoped then (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
  let status = wait_exit ~pid ~timeout:30. in
  (match status with
  | None -> check "child terminated" false "still running"
  | Some s ->
      let killed =
        match s with
        | Unix.WEXITED 137 -> true
        | Unix.WSIGNALED n -> n = Sys.sigkill
        | _ -> false
      in
      check "child was killed, not exited" killed
        (Printf.sprintf "status=%d" (match s with Unix.WEXITED n -> n | Unix.WSIGNALED n -> -n | Unix.WSTOPPED n -> n)));
  let body = read_file path in
  check "record is non-empty after the kill" (String.trim body <> "") body;
  check "record names the phase" (contains body "phase=transparent-functions") body;
  check "record has live_words" (contains body "live_words=") body;
  check "record has heap_words" (contains body "heap_words=") body;
  if Sys.file_exists path then Sys.remove path

(* The child: sample like the translator does, then allocate until something kills it. *)
let child () =
  Diagnose.set_phase "startup";
  Diagnose.start_sampler ();
  Diagnose.set_phase "transparent-functions";
  Diagnose.set_item "crate::metadata::visit_map";
  let keep = ref [] in
  let i = ref 0 in
  while true do
    incr i;
    keep := Bytes.make 1_000_000 (Char.chr (!i land 255)) :: !keep
  done

let () =
  if Array.length Sys.argv >= 2 && Sys.argv.(1) = "--memstat-child" then child ()
  else begin
    test_line ();
    test_killed_child_leaves_record ();
    Printf.printf "\n%d failure(s)\n" !failures;
    if !failures > 0 then exit 1
  end
