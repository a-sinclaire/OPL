exception Eval_error
exception Type_error

type typ = TBool | TInt

type exp = 
    | True
    | False
    | If of exp * exp * exp
    | Num of int
    | IsZero of exp
    | Plus of exp * exp
    | Mult of exp * exp

(* 
The function type_check takes in input an expression and returns the
type of that expression according to the type system that we have seen
in class, or the function raises the OCaml exception Type_error when
type checking fails
*)
let rec type_check (e : exp) = match e with
    | True -> TBool
    | False -> TBool
    | Num(n) -> TInt
    | If(e1, e2, e3) -> (
        match (type_check e2) with
        | TBool -> (
            match (type_check e3) with
            | TBool -> TBool
            | otherwise -> raise Type_error
        )
        | TInt -> (
            match (type_check e3) with
            | TInt -> TInt
            | otherwise -> raise Type_error
        )
    )
    | IsZero(e1) -> (
        match (type_check e1) with
        | TInt -> TBool
        | otherwise -> raise Type_error
    )
    | Plus(e1, e2) -> (
        match (type_check e1) with
        | TInt -> (
            match (type_check e2) with
            | TInt -> TInt
            | otherwise -> raise Type_error
        )
        | otherwise -> raise Type_error
    )
    | Mult(e1, e2) -> (
        match (type_check e1) with
        | TInt -> (
            match (type_check e2) with
            | TInt -> TInt
            | otherwise -> raise Type_error
        )
        | otherwise -> raise Type_error
    )

(*
The function step takes in input an
expression and returns the expression that
results from computing one step of the expression
in input, or raises OCaml exception Eval_error if
the computation fails
*)
let rec step (e : exp) = match e with
    | If(e1, e2, e3) -> (
        match e1 with
        | True -> e2
        | False -> e3
        | Num(n) -> raise Eval_error
        | otherwise -> If(step(e1), e2, e3))
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

(* Brought in from interpreter_bigstep for testing *)
let rec string_of_exp exp = match exp with
    | True -> "true"
    | False -> "false"
    | If(e1, e2, e3) -> "if " ^ (string_of_exp e1) ^ " then " ^ (string_of_exp e2) ^ " else " ^ (string_of_exp e3)
    | Num(n) -> string_of_int(n)
    | IsZero(e) -> "(isZero " ^ (string_of_exp e) ^ ")"
    | Plus(e1, e2) -> "(" ^ (string_of_exp e1) ^ " + " ^ (string_of_exp e2) ^ ")"
    | Mult(e1, e2) -> "(" ^ (string_of_exp e1) ^ " * " ^ (string_of_exp e2) ^ ")"

let rec string_of_typ typ = match typ with
    | TBool -> "TBool"
    | TInt -> "TInt"

let () =
    (print_endline "\n1-6\n");
    (* 1-6 *)
    (print_endline (string_of_typ (type_check (True) )));
    (print_endline (string_of_typ (type_check (False) )));
    (print_endline (string_of_typ (type_check (Num 0) )));
    (print_endline (string_of_typ (type_check (IsZero (Num 0)) )));
    (print_endline (string_of_typ (type_check (IsZero (Plus (Num 1, Num 1))) )));
    (print_endline (string_of_typ (type_check (IsZero (Plus (Plus (Num 2, Num (-1)), Num(1)))) )));

    (print_endline "\n7-13\n");
    (* 7-13 *)
    (print_endline (string_of_typ (type_check (Plus (Plus (Num (-1), Num 1), Plus (Num (-1), Num 1))) )));
    (print_endline (string_of_typ (type_check (Plus (Num (-1), Plus (Mult (Num 2, Num 2), Num 1))) )));
    (print_endline (string_of_typ (type_check (Plus (Plus (Plus (Num 2, Num (-1)), Num 1), Num (-1))) )));
    (* (print_endline (string_of_typ (type_check (Plus (IsZero (Plus (Num (-1), Num 1)), Num 1)) ))); *)
    (* (print_endline (string_of_typ (type_check (IsZero (If (IsZero (Num 0), True, Num 0))) ))); *)
    (* (print_endline (string_of_typ (type_check (IsZero
                                                (If
                                                    ( IsZero (Mult (Num 5, Num 0))
                                                    , If (False, Num 0, IsZero (Plus (Num (-1), Num 0)))
                                                    , Num 0 ))) ))); *)
    (* (print_endline (string_of_typ (type_check (If (IsZero (Plus (Num (-1), Num 1)), Num 2, True)) ))); *)

    (print_endline "\n14-20\n");
    (* 14-20 *)
    (* (print_endline (string_of_typ (type_check
                                        (If
                                            ( If (IsZero (Mult (Plus (Num 1, Num (-1)), Num 1)), False, True)
                                            , Mult (Num 1, Num 2)
                                            , True ))))); *)
    (* (print_endline (string_of_typ (type_check (If
                                            ( If (IsZero (Mult (Num 0, Num 0)), IsZero (Num 2), Num 0)
                                            , Mult (Num 2, Mult (Num 1, Num 1))
                                            , Plus
                                                ( Plus
                                                    ( Plus
                                                        ( Plus (If (IsZero (Num 0), Num 1, Num 0), Num (-1))
                                                        , Num 1 )
                                                    , Num (-1) )
                                                , Num 1 ) )) ))); *)
    (print_endline (string_of_typ (type_check (If
                                            ( True
                                            , If (True, Mult (If (False, Num 0, Num 1), Num 1), Num 5)
                                            , Plus (Mult (Num 4, Num 1), Num 1) )) )));
    (print_endline (string_of_typ (type_check (If
                                            ( IsZero (If (IsZero (Plus (Num (-1), Num 2)), Num 0, Num 1))
                                            , If
                                                ( True
                                                , If (False, Mult (Num 0, Num 6), Plus (Num 0, Num 1))
                                                , Num 5 )
                                            , Num 5 )) )));
    (* (print_endline (string_of_typ (type_check (If
                                            ( IsZero (Plus (Num (-1), Plus (Num 1, Plus (Num (-1), Num 1))))
                                            , IsZero True
                                            , Num 1 )) ))); *)
    (print_endline (string_of_typ (type_check (Plus
                                            ( Num 1
                                            , Plus
                                                ( Num (-1)
                                                , If
                                                    ( IsZero (Plus (Num 1, If (True, Num 1, Num 2)))
                                                    , Plus (Num 1, Num 2)
                                                    , Mult (Num 2, Num 2) ) ) )) )));
    (* (print_endline (string_of_typ (type_check (Plus
                                            ( Num (-1)
                                            , If
                                                ( IsZero (Plus (Num 5, Num (-4)))
                                                , Mult (Num 123, Plus (Num 5, Num (-4)))
                                                , IsZero (Num 0) ) )) ))); *)
