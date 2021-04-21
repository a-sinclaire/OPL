exception Eval_error

type exp =
    | True
    | False
    | If of exp * exp * exp
    | Num of int
    | IsZero of exp
    | Plus of exp * exp
    | Mult of exp * exp

let rec string_of_exp exp = match exp with
    | True -> "true"
    | False -> "false"
    | If(e1, e2, e3) -> "if " ^ (string_of_exp e1) ^ " then " ^ (string_of_exp e2) ^ " else " ^ (string_of_exp e3)
    | Num(n) -> string_of_int(n)
    | IsZero(e) -> "(isZero " ^ (string_of_exp e) ^ ")"
    | Plus(e1, e2) -> "(" ^ (string_of_exp e1) ^ " + " ^ (string_of_exp e2) ^ ")"
    | Mult(e1, e2) -> "(" ^ (string_of_exp e1) ^ " * " ^ (string_of_exp e2) ^ ")"

let rec eval exp = match exp with
    | True -> True
    | False -> False
    | If(e1, e2, e3) -> (
        match eval(e1) with
        | True -> eval(e2)
        | False -> eval(e3)
        | otherwise -> raise(Eval_error))
    | Num(n) -> Num(n)
    | IsZero(e) -> (
        match eval(e) with
        | Num(n) -> if (n = 0) then True else False
        | otherwise -> raise(Eval_error))
    | Plus(e1, e2) -> (
        match eval(e1) with 
        | Num(n1) -> (
            match eval(e2) with
            | Num(n2) -> Num(n1+n2)
            | otherwise -> raise(Eval_error))
        | otherwise -> raise(Eval_error))
    | Mult(e1, e2) -> (
        match eval(e1) with 
        | Num(n1) -> (
            match eval(e2) with
            | Num(n2) -> Num(n1*n2)
            | otherwise -> raise(Eval_error))
        | otherwise -> raise(Eval_error))

let () =
    (* PART TWO OF ASSIGNMENT *)
    (* Big-Step Semantics *)
    (* 1-4 *)
    print_endline (string_of_exp (eval (True)           ));
    print_endline (string_of_exp (eval (False)          ));
    print_endline (string_of_exp (eval (Num(0))         ));
    print_endline (string_of_exp (eval (IsZero(Num(0))) ));

    (* 5-8 *)
    print_endline ("\n" ^ string_of_exp (eval (IsZero(Plus(Num(1), Num(1)))) ));
    print_endline (string_of_exp (eval (IsZero(Plus(Plus(Num(2), Num(-1)), Num(1)))) ));
    print_endline (string_of_exp (eval (Plus(Plus(Num(-1), Num(1)), Plus(Num(-1), Num(1)))) ));
    print_endline (string_of_exp (eval (Plus(Num(-1), Plus(Mult(Num(2), Num(2)), Num(1)))) ));

    (* 9-12 *)
    print_endline ("\n" ^ string_of_exp (eval (Plus (Plus (Plus (Num(2), Num(-1)), Num(1)), Num(-1))) ));
    (* print_endline (string_of_exp (eval (Plus(IsZero(Plus(Num(-1), Num(1))), Num(1))) )); *)
    (* print_endline (string_of_exp (eval (IsZero(If(IsZero(Num(0)), True, Num(0)))) )); *)
    (* print_endline (string_of_exp (eval (IsZero(If(IsZero(Mult(Num(5), Num(0))), If(False, Num(0), IsZero(Plus(Num(-1), Num(0)))), Num(0)))) )); *)

    (* 13-16 *)
    print_endline ("\n" ^ string_of_exp (eval (If(IsZero(Plus(Num(-1), Num(1))), Num(2), True)) ));
    print_endline (string_of_exp (eval (If(If(IsZero(Mult(Plus(Num(1), Num(-1)), Num(1))), False, True), Mult (Num(1), Num(2)), True)) ));
    print_endline (string_of_exp (eval (If
                                        ( If (IsZero (Mult (Num 0, Num 0)), IsZero (Num 2), Num 0)
                                        , Mult (Num 2, Mult (Num 1, Num 1))
                                        , Plus
                                            ( Plus
                                                ( Plus
                                                    ( Plus (If (IsZero (Num 0), Num 1, Num 0), Num (-1))
                                                    , Num 1 )
                                                , Num (-1) )
                                            , Num 1 ) )) ));
    print_endline (string_of_exp (eval (If
                                        ( True
                                        , If (True, Mult (If (False, Num 0, Num 1), Num 1), Num 5)
                                        , Plus (Mult (Num 4, Num 1), Num 1) )) ));

    (* 17-20 *)
    print_endline ("\n" ^ string_of_exp (eval (If
                                                ( IsZero (If (IsZero (Plus (Num (-1), Num 2)), Num 0, Num 1))
                                                , If
                                                    ( True
                                                    , If (False, Mult (Num 0, Num 6), Plus (Num 0, Num 1))
                                                    , Num 5 )
                                                , Num 5 )) ));
    (* print_endline (string_of_exp (eval (If
                                        ( IsZero (Plus (Num (-1), Plus (Num 1, Plus (Num (-1), Num 1))))
                                        , IsZero True
                                        , Num 1 )) )); *)
    print_endline (string_of_exp (eval (Plus
                                        ( Num 1
                                        , Plus
                                            ( Num (-1)
                                            , If
                                                ( IsZero (Plus (Num 1, If (True, Num 1, Num 2)))
                                                , Plus (Num 1, Num 2)
                                                , Mult (Num 2, Num 2) ) ) )) ));
    print_endline (string_of_exp (eval (Plus
                                        ( Num (-1)
                                        , If
                                            ( IsZero (Plus (Num 5, Num (-4)))
                                            , Mult (Num 123, Plus (Num 5, Num (-4)))
                                            , IsZero (Num 0) ) )) ));





    (* PART ONE OF ASSIGNMENT *)

    (* 01print_endline (string_of_exp (Num(3)));
    (*02*)print_endline (string_of_exp (True));
    (*03*)print_endline (string_of_exp (False));
    (*04*)print_endline (string_of_exp (Plus(Num(3), Num(2))));
    (*05*)print_endline (string_of_exp (Mult(Num(3), Num(2))));
    (*06*)print_endline (string_of_exp (Plus(Num(3), Plus(Num(3), Mult(Num(2), Plus(Num(3), Num(2)))))));
    (* On website #7 there is an extra "then" I assume is a typo*)
    (*07*)print_endline (string_of_exp (If(True, Num(3), Num(5))));
    (*08*)print_endline (string_of_exp (If(False, Plus(Num(3), Num(2)), Plus(Num(5), Num(1)))));
    (*09*)print_endline (string_of_exp (If(Plus(False, True), Plus(Num(3), False), Mult(Num(3), Num(1)))));
    (*10*)print_endline (string_of_exp (If(IsZero(Num(1)), Plus(Num(3), Num(2)), Plus(Num(5), Num(1)))));
    (*11*)print_endline (string_of_exp (IsZero(Mult(Num(3), Num(5)))));
    (* On website #12 there exists an if statement surrounded in paratheses that shouldn't be possible - I assume it is a typo*)
    (*12*)print_endline (string_of_exp (IsZero(If(IsZero(Num(1)), Plus(Num(3), Num(2)), Plus(Num(5), Num(1))))));
    (*13*)print_endline (string_of_exp (Plus(Num(3), If(IsZero(Num(1)), Plus(Num(3), Num(2)), Plus(Num(5), Num(1))))));
    (*14*)print_endline (string_of_exp (Plus(Num(3), Mult(If(IsZero(Num(1)), Plus(Num(3), Num(2)), Plus(Num(5), Num(1))), IsZero(True)))));
    (*15*)print_endline (string_of_exp (If(If(True, True, False), Plus(Num(3), Num(2)), Plus(Num(5), Num(1)))));
    (*16*)print_endline (string_of_exp (If(True, If(IsZero(Mult(Num(3), Num(5))), Plus(Num(3), Num(2)),  Plus(Num(5), Num(1))), If(True, Mult(Num(3), Num(2)), Mult(Num(2), Plus(Num(3), Num(2))))))); *)