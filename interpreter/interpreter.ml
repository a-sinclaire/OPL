exception Eval_error

type exp = 
    | True
    | False
    | If of exp * exp * exp
    | Num of int
    | IsZero of exp
    | Plus of exp * exp
    | Mult of exp * exp

(*
The function step takes in input an
expression and returns the expression that
results from computing one step of the expression
in input, or raises OCaml exception Eval_error if
the computation fails
*)
let rec step (e : exp) = match e with
    | True -> raise Eval_error
    | False -> raise Eval_error
    | If(e1, e2, e3) -> (
        match e1 with
        | True -> e2
        | False -> e3
        | Num(n) -> raise Eval_error
        | otherwise -> If(step(e1), e2, e3))
    | Num(n) -> raise Eval_error
    | IsZero(e) ->  (
        match e with
        | Num(n) -> if (n = 0) then True else False
        | True -> raise Eval_error
        | False -> raise Eval_error
        | otherwise -> IsZero(step(e)))
    | Plus(e1, e2) -> (
        match e1 with
        | Num(n1) -> (
            match e2 with
            | Num(n2) -> Num(n1+n2)
            | True -> raise Eval_error
            | False -> raise Eval_error
            | otherwise -> Plus(e1, step(e2)))
        | True -> raise Eval_error
        | False -> raise Eval_error
        | otherwise -> Plus(step(e1), e2))
    | Mult(e1, e2) -> (
        match e1 with
        | Num(n1) -> (
            match e2 with
            | Num(n2) -> Num(n1*n2)
            | True -> raise Eval_error
            | False -> raise Eval_error
            | otherwise -> Mult(e1, step(e2)))
        | True -> raise Eval_error
        | False -> raise Eval_error
        | otherwise -> Mult(step(e1), e2))
    | otherwise -> raise Eval_error


(*
The function multi_step takes in input an
expression and iterates the function step in order
to evaluate the expression one step at a time until
it returns a value, or raises OCaml exception Eval_error
if the computation fails
*)
let rec multi_step (e : exp) = match e with
    | True -> True
    | False -> False
    | If(e1, e2, e3) -> multi_step(step(If(e1,e2,e3)))
    | Num(n) -> Num(n)
    | IsZero(e) -> multi_step(step(IsZero(e)))
    | Plus(e1, e2) -> multi_step(step(Plus(e1, e2)))
    | Mult(e1, e2) -> multi_step(step(Mult(e1, e2)))
    | otherwise -> raise Eval_error


(* Brought in from interpreter_bigstep for testing *)
let rec string_of_exp exp = match exp with
    | True -> "true"
    | False -> "false"
    | If(e1, e2, e3) -> "if " ^ (string_of_exp e1) ^ " then " ^ (string_of_exp e2) ^ " else " ^ (string_of_exp e3)
    | Num(n) -> string_of_int(n)
    | IsZero(e) -> "(isZero " ^ (string_of_exp e) ^ ")"
    | Plus(e1, e2) -> "(" ^ (string_of_exp e1) ^ " + " ^ (string_of_exp e2) ^ ")"
    | Mult(e1, e2) -> "(" ^ (string_of_exp e1) ^ " * " ^ (string_of_exp e2) ^ ")"


let () =
    print_endline ("\n1-5\n");
    (* 1-5 COMPLETE*)
    print_endline (string_of_exp (multi_step True));
    print_endline (string_of_exp (multi_step False));
    print_endline (string_of_exp (multi_step (Num 0)));
    print_endline (string_of_exp (multi_step (IsZero (Num 0))));
    print_endline (string_of_exp (multi_step (IsZero (Plus (Num 1, Num 1)))));

    print_endline ("\n6-9\n");
    (* 6-9 COMPLETE*)
    print_endline (string_of_exp (multi_step (IsZero (Plus (Plus (Num 2, Num (-1)), Num 1)))));
    print_endline (string_of_exp (multi_step (Plus (Plus (Num (-1), Num 1), Plus (Num (-1), Num 1)))));
    print_endline (string_of_exp (multi_step (Plus (Num (-1), Plus (Mult (Num 2, Num 2), Num 1)))));
    print_endline (string_of_exp (multi_step (Plus (Plus (Plus (Num 2, Num (-1)), Num 1), Num (-1)))));

    print_endline ("\n10-15\n");
    (* 10-15 COMPLETE*)
    (* print_endline (string_of_exp (multi_step (Plus (IsZero (Plus (Num (-1), Num 1)), Num 1)))); *)
    (* print_endline (string_of_exp (multi_step (IsZero (If (IsZero (Num 0), True, Num 0))))); *)
    (* print_endline (string_of_exp (multi_step
                                            (IsZero
                                                (If
                                                    ( IsZero (Mult (Num 5, Num 0))
                                                    , If (False, Num 0, IsZero (Plus (Num (-1), Num 0)))
                                                    , Num 0 ))))); *)
    print_endline (string_of_exp (multi_step (If (IsZero (Plus (Num (-1), Num 1)), Num 2, True))));
    print_endline (string_of_exp (multi_step
                                            (If
                                                ( If (IsZero (Mult (Plus (Num 1, Num (-1)), Num 1)), False, True)
                                                , Mult (Num 1, Num 2)
                                                , True ))));
    print_endline (string_of_exp (multi_step
                                            (If
                                                ( If (IsZero (Mult (Num 0, Num 0)), IsZero (Num 2), Num 0)
                                                , Mult (Num 2, Mult (Num 1, Num 1))
                                                , Plus
                                                    ( Plus
                                                        ( Plus
                                                            ( Plus (If (IsZero (Num 0), Num 1, Num 0), Num (-1))
                                                            , Num 1 )
                                                        , Num (-1) )
                                                    , Num 1 ) ))));

    print_endline ("\n16-20\n");
    (* 16-20 COMPLETE*)
    print_endline (string_of_exp (multi_step
                                            (If
                                                ( True
                                                , If (True, Mult (If (False, Num 0, Num 1), Num 1), Num 5)
                                                , Plus (Mult (Num 4, Num 1), Num 1) ))));
    print_endline (string_of_exp (multi_step
                                            (If
                                                ( IsZero (If (IsZero (Plus (Num (-1), Num 2)), Num 0, Num 1))
                                                , If
                                                    ( True
                                                    , If (False, Mult (Num 0, Num 6), Plus (Num 0, Num 1))
                                                    , Num 5 )
                                                , Num 5 ))));
    (* print_endline (string_of_exp (multi_step
                                            (If
                                                ( IsZero (Plus (Num (-1), Plus (Num 1, Plus (Num (-1), Num 1))))
                                                , IsZero True
                                                , Num 1 )))); *)
    print_endline (string_of_exp (multi_step
                                            (Plus
                                                ( Num 1
                                                , Plus
                                                    ( Num (-1)
                                                    , If
                                                        ( IsZero (Plus (Num 1, If (True, Num 1, Num 2)))
                                                        , Plus (Num 1, Num 2)
                                                        , Mult (Num 2, Num 2) ) ) ))));
    (* print_endline (string_of_exp (multi_step
                                            (Plus
                                                ( Num (-1)
                                                , If
                                                    ( IsZero (Plus (Num 5, Num (-4)))
                                                    , Mult (Num 123, Plus (Num 5, Num (-4)))
                                                    , IsZero (Num 0) ) )))); *)


