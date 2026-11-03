(* Regression tests for the report of a [CFailure].

   A [CFailure] carries the message, the source span of the construct and (when the raising
   code knows it) the declaration being translated. None of that reached the user: the
   exception payload was printed by the OCaml runtime as [_], so an aborted run said

     Fatal error: exception Aeneas.Errors.CFailure(_)

   next to "Internal error, please file an issue" -- a request to file a report that named
   neither the construct nor its source. The contracts pinned here are that the report
   carries the message, the span and the declaration, that the runtime printer uses it, and
   that the declaration is captured when the failure is raised rather than when it is
   reported (the handlers unwind in between).

   Run with `dune build @runtest` from src/. *)

open Aeneas

let failures = ref 0

let report name = function
  | Ok note -> Printf.printf "PASS  %-52s %s\n" name note
  | Error note ->
      incr failures;
      Printf.printf "FAIL  %-52s %s\n" name note

let substring_at (haystack : string) (needle : string) (i : int) =
  String.length haystack - i >= String.length needle
  && String.sub haystack i (String.length needle) = needle

let contains (haystack : string) (needle : string) =
  let n = String.length haystack and m = String.length needle in
  let rec loop i = i + m <= n && (substring_at haystack needle i || loop (i + 1)) in
  m = 0 || loop 0

let expect_contains name ~(text : string) ~(needle : string) =
  if contains text needle then report name (Ok ("reports \"" ^ needle ^ "\""))
  else report name (Error ("does not report \"" ^ needle ^ "\": " ^ text))

let loc (line : int) (col : int) : Meta.loc = { line; col }

let span : Meta.span =
  {
    data =
      {
        file =
          {
            name = Meta.Local "crate/src/lib.rs";
            crate_name = "crate";
            contents = None;
          };
        beg_loc = loc 10 4;
        end_loc = loc 12 5;
      };
    generated_from_span = None;
  }

let sample : Errors.cfailure =
  {
    span = Some span;
    file = "Errors.ml";
    line = 179;
    msg = "Internal error, please file an issue";
    item = Some "crate::m::<u32>::f";
  }

let () =
  (* The three parts a reader needs to act on the report. *)
  let printed = Errors.cfailure_to_string sample in
  expect_contains "the message is reported" ~text:printed
    ~needle:"Internal error, please file an issue";
  expect_contains "the source span is reported" ~text:printed ~needle:"crate/src/lib.rs";
  expect_contains "the lines are reported" ~text:printed ~needle:"10:4-12:5";
  expect_contains "the declaration is reported" ~text:printed
    ~needle:"While translating: crate::m::<u32>::f";

  (* What an uncaught failure prints: the runtime asks the registered printer, and before
     the fix it answered [_] for the whole payload. *)
  let uncaught = Printexc.to_string (Errors.CFailure sample) in
  expect_contains "the runtime printer includes the message" ~text:uncaught
    ~needle:"Internal error, please file an issue";
  expect_contains "the runtime printer includes the declaration" ~text:uncaught
    ~needle:"crate::m::<u32>::f";
  (if contains uncaught "(_)" then
     report "the runtime printer does not print the payload as _" (Error uncaught)
   else report "the runtime printer does not print the payload as _" (Ok ""));

  (* No declaration known: the report stays readable instead of printing a dangling label. *)
  let anonymous = { sample with item = None } in
  let printed_anonymous = Errors.cfailure_to_string anonymous in
  (if contains printed_anonymous "While translating" then
     report "an unknown declaration is not named" (Error printed_anonymous)
   else report "an unknown declaration is not named" (Ok "the label is omitted"));

  (* The declaration is captured when the failure is raised: by the time the report is
     printed the handler has unwound, so a cell read at reporting time would be empty. *)
  let raised =
    Errors.with_current_item "crate::m::f" (fun () ->
        match Errors.craise_opt_span_silent "Test_cfailure.ml" 1 (Some span) "boom" with
        | _ -> None
        | exception Errors.CFailure error -> error.item)
  in
  (match raised with
  | Some "crate::m::f" -> report "the declaration is captured at raise time" (Ok "")
  | other ->
      report "the declaration is captured at raise time"
        (Error
           ("captured "
           ^ Print.option_to_string (fun x -> x) other
           ^ ", expected Some \"crate::m::f\"")));

  (* ... and the capture does not leak into the next declaration. *)
  let after =
    Errors.with_current_item "crate::m::g" (fun () -> Errors.current_item ())
  in
  (match after with
  | Some "crate::m::g" -> report "the declaration is scoped" (Ok "")
  | other ->
      report "the declaration is scoped"
        (Error
           ("captured " ^ Print.option_to_string (fun x -> x) other)));
  (match Errors.current_item () with
  | None -> report "the declaration is restored on exit" (Ok "")
  | Some name ->
      report "the declaration is restored on exit" (Error ("still " ^ name)));

  if !failures = 0 then (
    Printf.printf "\ncfailure: all contracts hold\n";
    exit 0)
  else (
    Printf.printf "\ncfailure: %d contract(s) broken\n" !failures;
    exit 1)
