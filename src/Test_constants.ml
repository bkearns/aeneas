(* Regression tests for turning a constant into a value.

   A constant that is not a literal -- an aggregate, an array, a pointer, a function
   item -- has no representation as a {!Values.literal}. What must not happen is what
   happened before: an unguarded [Failure "Expected a primitive constant"] that names
   neither the value nor the item and takes the whole run down with it.

   These tests pin the two halves of the replacement:
   - {!TypesUtils.constant_expr_as_literal_opt} answers [None] for those shapes instead
     of raising, so the caller (which knows the item) can report a located error;
   - {!TypesUtils.constant_expr_kind_desc} says what the shape actually is, so that
     message can name it.

   The description is deliberately context-free, because a caller in the middle of a
   body has no formatter set up for the item it is translating; hence nothing here
   involves one.

   Run with `dune build @runtest` from src/. *)

open Aeneas
open Types

let int_ty = TScalar (TInteger (Signed Isize))

(* Build a constant expression of the given shape. Only the shape matters below, so
   every one of them carries the same scalar type. *)
let of_kind kind : constant_expr = { kind; ty = int_ty }
let int_literal = Values.SignedInteger (Isize, Z.of_int 3)
let failures = ref 0

let report name = function
  | Ok note -> Printf.printf "PASS  %-56s %s\n" name note
  | Error note ->
      incr failures;
      Printf.printf "FAIL  %-56s %s\n" name note

let contains ~needle haystack =
  let re = Str.regexp_string needle in
  try
    ignore (Str.search_forward re haystack 0);
    true
  with Not_found -> false

let expect_desc name (kind : constant_expr_kind) (fragments : string list) =
  let got = TypesUtils.constant_expr_kind_desc kind in
  let missing = List.filter (fun f -> not (contains ~needle:f got)) fragments in
  if missing = [] then report name (Ok (Printf.sprintf "described as '%s'" got))
  else
    report name
      (Error
         (Printf.sprintf "described as '%s'; missing %s" got
            (String.concat ", " (List.map (Printf.sprintf "%S") missing))))

let expect_literal name (kind : constant_expr_kind) =
  match TypesUtils.constant_expr_as_literal_opt (of_kind kind) with
  | Some _ -> report name (Ok "converted to a literal")
  | None -> report name (Error "returned None; expected a literal")

let expect_no_literal name (kind : constant_expr_kind) (fragments : string list) =
  match TypesUtils.constant_expr_as_literal_opt (of_kind kind) with
  | None -> expect_desc name kind fragments
  | Some _ -> report name (Error "returned a literal; expected None")

let () =
  (* The positive control: literals still convert, so a converter that always answers
     [None] fails here. *)
  expect_literal "boolean literal converts" (CBool true);
  expect_literal "integer literal converts" (CInteger int_literal);
  expect_literal "string literal converts" (CStr "abc");
  expect_literal "byte-string literal converts" (CByteStr [ 0; 255 ]);

  (* An aggregate allocation. This is the shape of a `CStr` literal, whose bytes are a
     one-field aggregate, and it is read as `&constant` at the use site. *)
  expect_no_literal "aggregate value is not a literal"
    (CAdt (None, [ of_kind (CInteger int_literal) ]))
    [ "aggregate"; "1 field" ];
  (* An array allocation, e.g. the backing store of a slice literal. *)
  expect_no_literal "array value is not a literal"
    (CArray
       [
         of_kind (CInteger int_literal);
         of_kind (CInteger int_literal);
         of_kind (CInteger int_literal);
       ])
    [ "array"; "3 element" ];
  (* A zero-sized value: not a scalar either. *)
  expect_no_literal "empty array is not a literal" (CArray []) [ "array"; "0 element" ];
  (* Shapes that name something the reader needs to see. *)
  expect_desc "extern symbol is named" (CExternSymbol "some_symbol") [ "some_symbol" ];
  expect_desc "opaque reason is kept" (COpaque "not evaluated")
    [ "opaque"; "not evaluated" ];

  (* The integer converter is still the old raising one, but its message now says what
     it got: it is a fallback for shapes the callers believed they had excluded. *)
  (match
     try
       let _ = TypesUtils.constant_expr_as_integer (of_kind (CArray [])) in
       None
     with Failure msg -> Some msg
   with
  | Some msg when contains ~needle:"an array value with 0 element(s)" msg ->
      report "integer conversion names the shape it got"
        (Ok (Printf.sprintf "raised Failure(%S)" msg))
  | Some msg ->
      report "integer conversion names the shape it got"
        (Error (Printf.sprintf "raised Failure(%S); missing the shape" msg))
  | None ->
      report "integer conversion names the shape it got"
        (Error "did not raise; expected a Failure"));

  if !failures = 0 then (
    Printf.printf "\nconstants: all contracts hold\n";
    exit 0)
  else (
    Printf.printf "\n%d test(s) failed\n" !failures;
    exit 1)
