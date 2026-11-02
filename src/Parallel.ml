open Domain

exception Stop of exn * Printexc.raw_backtrace

(** Exceptions are not properly propagated through domain boundaries with the
    consequence that we lose precious backtraces when they are not properly
    caught.

    This helper wraps a function call inside a try with to catch uncaught
    exceptions and save their backtrace. *)
let run_with_backtrace (f : 'a -> 'b) (x : 'a) : 'b =
  (* We have to activate the backtrace for the domain - it is not activated by default! *)
  Printexc.record_backtrace true;
  try f x with exn -> raise (Stop (exn, Printexc.get_raw_backtrace ()))

let catch_reraise (f : 'a -> 'b) (x : 'a) : 'b =
  try f x with Stop (e, bt) -> Printexc.raise_with_backtrace e bt

(** A persistent pool that is created once and reused for all parallel
    operations. This avoids the overhead of creating and tearing down domains
    for each parallel call. *)
module Pool = struct
  module T = Domainslib.Task

  let pool =
    lazy
      (let num_domains = recommended_domain_count () - 1 in
       T.setup_pool ~num_domains ())

  let get () = Lazy.force pool

  (* Tear down the pool at program exit *)
  let () =
    at_exit (fun () ->
        if Lazy.is_val pool then T.teardown_pool (Lazy.force pool))
end

(** Run a map in parallel.

    We divide the list in chunks and use one domain to compute the map on a
    chunk. We allocate the maximum number of recommended domains. *)
let parallel_map_chunks_aux (f : 'a -> 'b) (ls : 'a list) : 'b list =
  (* Only run in parallel if the option is activated *)
  if !Config.parallel then
    let f = run_with_backtrace f in
    (* Decompose the list into chunks and spawn a domain for each chunk *)
    let num_domains = recommended_domain_count () in
    let elems_per_domain = List.length ls / num_domains in
    let chunks = Collections.List.chunks elems_per_domain ls in
    let domains =
      List.map (fun chunk -> spawn (fun () -> List.map f chunk)) chunks
    in
    (* Join *)
    let ll = List.map join domains in
    List.flatten ll
  else List.map f ls

let parallel_map_chunks f ls = catch_reraise (parallel_map_chunks_aux f) ls

(** Run a filter_map in parallel.

    We divide the list in chunks and use one domain to compute the filter map on
    a chunk. We allocate the maximum number of recommended domains. *)
let parallel_filter_map_chunks_aux (f : 'a -> 'b option) (ls : 'a list) :
    'b list =
  (* Only run in parallel if the option is activated *)
  if !Config.parallel then
    let f = run_with_backtrace f in
    (* Decompose the list into chunks and spawn a domain for each chunk *)
    let num_domains = recommended_domain_count () in
    let elems_per_domain = List.length ls / num_domains in
    let chunks = Collections.List.chunks elems_per_domain ls in
    let domains =
      List.map (fun chunk -> spawn (fun () -> List.filter_map f chunk)) chunks
    in
    (* Join *)
    let ll = List.map join domains in
    List.flatten ll
  else List.filter_map f ls

let parallel_filter_map_chunks f ls =
  catch_reraise (parallel_filter_map_chunks_aux f) ls

(** Run a map in parallel using the persistent pool.

    We allocate the maximum number of recommended domains. Each element gets its
    own async task, allowing the pool to schedule work dynamically (avoiding the
    problem where chunking gives all the biggest tasks to the first worker). *)
let parallel_map_pool_aux (f : 'a -> 'b) (ls : 'a list) : 'b list =
  (* Only run in parallel if the option is activated *)
  if !Config.parallel then
    let f = run_with_backtrace f in
    let module T = Domainslib.Task in
    let pool = Pool.get () in
    (* Run the tasks asynchronously *)
    let run (x : 'a) () = f x in
    let tasks = List.map (fun x -> T.async pool (run x)) ls in
    (* Wait *)
    T.run pool (fun _ -> List.map (T.await pool) tasks)
  else List.map f ls

let parallel_map_pool f ls = catch_reraise (parallel_map_pool_aux f) ls

(** Run a filter_map in parallel using the persistent pool.

    We allocate the maximum number of recommended domains. Each element gets its
    own async task, allowing the pool to schedule work dynamically. *)
let parallel_filter_map_pool_aux (f : 'a -> 'b option) (ls : 'a list) : 'b list
    =
  (* Only run in parallel if the option is activated *)
  if !Config.parallel then
    let f = run_with_backtrace f in
    let module T = Domainslib.Task in
    let pool = Pool.get () in
    (* Run the tasks asynchronously *)
    let run (x : 'a) () = f x in
    let tasks = List.map (fun x -> T.async pool (run x)) ls in
    (* Wait *)
    T.run pool (fun _ -> List.filter_map (T.await pool) tasks)
  else List.filter_map f ls

let parallel_filter_map_pool f ls =
  catch_reraise (parallel_filter_map_pool_aux f) ls

(** Run a filter_map with bounded work in flight.

    [parallel_filter_map] submits every element at once and lets the pool decide, so the
    number of functions being translated simultaneously is the pool size no matter how
    large each one is. On a large Rust crate that multiplies the working set of the
    biggest functions: measured on [ferrosa_sstable.llbc] the fifteen-worker run passed
    8.8 GiB and was still climbing, where the sequential run peaked at 2.0 GiB. Aeneas
    already knows each function's size, so the bound belongs on what is in flight.

    Elements are packed into waves in input order: a wave stops growing at [max_jobs]
    elements or when the sum of their [cost] would pass [budget]. Each wave is awaited
    before the next is submitted, so the bound holds at every instant, and results keep
    the input order. An element whose own cost exceeds [budget] runs in a wave by itself
    rather than being dropped. *)
let parallel_filter_map_bounded_aux ~(cost : 'a -> int) ~(budget : int)
    ~(max_jobs : int) (f : 'a -> 'b option) (ls : 'a list) : 'b list =
  if not !Config.parallel then List.filter_map f ls
  else begin
    let f = run_with_backtrace f in
    let module T = Domainslib.Task in
    let pool = Pool.get () in
    let max_jobs = max 1 max_jobs in
    let budget = max 1 budget in
    let waves =
      let rec go acc cur cur_cost = function
        | [] -> List.rev (match cur with [] -> acc | _ -> List.rev cur :: acc)
        | x :: rest ->
            let x_cost = cost x in
            if cur = [] then go acc [ x ] x_cost rest
            else if List.length cur >= max_jobs || cur_cost + x_cost > budget
            then go (List.rev cur :: acc) [ x ] x_cost rest
            else go acc (x :: cur) (cur_cost + x_cost) rest
      in
      go [] [] 0 ls
    in
    let run (x : 'a) () = f x in
    if max_jobs <= 1 then
      (* One worker is the sequential path: entering the pool once per element would pay
         the scheduler for nothing. *)
      List.filter_map f ls
    else
      List.concat_map
        (fun wave ->
          let tasks = List.map (fun x -> T.async pool (run x)) wave in
          T.run pool (fun _ -> List.filter_map (T.await pool) tasks))
        waves
  end

let parallel_filter_map_bounded ~cost ~budget ~max_jobs f ls =
  catch_reraise
    (fun () -> parallel_filter_map_bounded_aux ~cost ~budget ~max_jobs f ls)
    ()

(** What one worker is allowed to hold.

    A worker keeps the symbolic body of the function it is translating alive until the
    function is done, and on [ferrosa_sstable.llbc] a single function reached ~4 GiB of
    live data. That number is the reason the worker count cannot follow the core count. *)
let per_worker_mb = 4096

(** How many functions may be translated at once.

    Half of the available memory is the ceiling, so a translator running next to a desktop
    leaves that desktop usable; [cores - 1] is the floor of ambition, since more workers
    than cores only adds contention. A reading of [0] means the memory could not be
    determined, and the core count is all that is known. *)
let max_jobs_for ~(available_mb : int) ~(cores : int) : int =
  let by_cores = Stdlib.max 1 (cores - 1) in
  if available_mb <= 0 then by_cores
  else begin
    let by_memory = available_mb / 2 / per_worker_mb in
    Stdlib.max 1 (Stdlib.min by_cores by_memory)
  end

(** Available memory in MiB, when the platform says so.

    Only Linux publishes this in a form that needs no process spawn; elsewhere the caller
    falls back to the core count. *)
let available_memory_mb () : int =
  try
    let channel = open_in "/proc/meminfo" in
    Fun.protect
      ~finally:(fun () -> close_in_noerr channel)
      (fun () ->
        let rec scan () =
          match input_line channel with
          | line -> (
              match String.split_on_char ':' line with
              | [ "MemAvailable"; rest ] -> (
                  match
                    String.split_on_char ' ' (String.trim rest)
                    |> List.filter (fun s -> s <> "")
                  with
                  | value :: _ -> ( try Some (int_of_string value / 1024) with _ -> None)
                  | [] -> None)
              | _ -> scan ())
          | exception End_of_file -> None
        in
        match scan () with Some mb -> mb | None -> 0)
  with _ -> 0

(** How many workers a memory attribution run may use.

    A per-function delta measured while other domains are translating belongs partly to
    the neighbours, so asking for attribution selects one worker. Returning the request
    unchanged when nobody asked keeps this from becoming a silent global serialiser. *)
let jobs_for_diagnosis ~(diagnose_memory : bool) ~(max_jobs : int) : int =
  if diagnose_memory then 1 else max_jobs

let parallel_map = parallel_map_pool
let parallel_filter_map = parallel_filter_map_pool
