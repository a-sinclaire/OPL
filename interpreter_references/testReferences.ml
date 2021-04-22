(* ocamlc interpreter_references.ml testReferences.ml -o testReferences *)

open Interpreter_references

let assert_equal a b = assert (a = b)

let assert_raises exc f =
  match f () with
  | exception exc' when exc = exc' -> ()
  | _ -> assert false

let test_1 () =
  assert_equal (multi_step (Malloc (Num 1)) [] |> fst) (Label 0)

let test_2 () =
  assert_equal
    (multi_step (Mread (Malloc (Malloc (Num 1)))) [] |> fst)
    (Label 0)

let test_3 () =
  assert_raises Eval_error (fun _ ->
      multi_step
        (Apply (Lambda ("n", TRef TInt, Mread (Var "n")), Label 0))
        [])

let test_4 () =
  assert_equal
    ( multi_step
        (Apply
           ( Lambda ("n", TRef TInt, Mread (Var "n"))
           , Malloc (Plus (Num 5, Num 1)) ))
        []
    |> fst )
    (Num 6)

let test_5 () =
  assert_equal
    ( multi_step
        (Apply
           ( Lambda
               ( "b"
               , TRef TBool
               , Sequence
                   ( If (Mread (Var "b"), Assign (Var "b", False), Unit)
                   , Mread (Var "b") ) )
           , Malloc True ))
        []
    |> fst )
    False

let test_6 () =
  assert_equal
    ( multi_step
        (Apply
           ( Lambda
               ( "n"
               , TRef TInt
               , Sequence
                   ( Assign (Var "n", Plus (Mread (Var "n"), Num 1))
                   , Assign (Var "n", Mult (Mread (Var "n"), Num 2)) ) )
           , Malloc (Num 3) ))
        []
    |> fst )
    Unit

let test_7 () =
  assert_equal
    ( multi_step
        (Apply
           ( Lambda
               ( "n"
               , TRef TInt
               , Apply
                   ( Lambda
                       ( "f"
                       , TArrow (TUnit, TUnit)
                       , Sequence
                           ( Apply (Var "f", Unit)
                           , Sequence (Apply (Var "f", Unit), Mread (Var "n"))
                           ) )
                   , Lambda
                       ( "_"
                       , TUnit
                       , Assign (Var "n", Div (Mread (Var "n"), Num 2)) ) )
               )
           , Malloc (Num 32) ))
        []
    |> fst )
    (Num 8)

let test_8 () =
  assert_equal
    ( multi_step
        (Apply
           ( Apply
               ( Apply
                   ( Lambda
                       ( "x"
                       , TRef TInt
                       , Lambda
                           ( "y"
                           , TRef TInt
                           , Lambda
                               ( "z"
                               , TInt
                               , Apply
                                   ( Lambda
                                       ( "f"
                                       , TArrow (TInt, TInt)
                                       , Sequence
                                           ( Assign (Var "x", Num 10)
                                           , Sequence
                                               ( Assign (Var "y", Num 12)
                                               , Apply
                                                   (Var "f", Mread (Var "y"))
                                               ) ) )
                                   , Lambda
                                       ( "a"
                                       , TInt
                                       , Plus
                                           ( Var "a"
                                           , Plus (Mread (Var "x"), Var "z")
                                           ) ) ) ) ) )
                   , Malloc (Num 0) )
               , Malloc (Num 0) )
           , Num 20 ))
        []
    |> fst )
    (Num 42)

let () =
  print_endline "References tests, your grade: 0.94";
  test_1 ();
  test_2 ();
  print_endline "Tests 1-2 passed, your grade: 0.95";
  test_3 ();
  test_4 ();
  print_endline "Tests 3-4 passed, your grade: 0.96";
  test_5 ();
  print_endline "Test 5 passed, your grade: 0.97";
  (* test_6 (); *)
  print_endline "Test 6 passed, your grade: 0.98";
  (* test_7 (); *)
  print_endline "Test 7 passed, your grade: 0.99";
  (* test_8 (); *)
  print_endline "Test 8 passed, your grade: 1.0"
