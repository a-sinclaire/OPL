exception Eval_error
exception Substitution_error

type typ =
    | TBool
    | TInt
    | TArrow of typ * typ

type type_environment = (string * typ) list

type exp = 
    | True
    | False
    | If of exp * exp * exp
    | Num of int
    | IsZero of exp
    | Plus of exp * exp
    | Mult of exp * exp
    | Var of string
    | Lambda of string * exp
    | Apply of exp * exp
    | TypeError


let rec find e l = match l with
    | [] -> false
    | a :: rest -> (a = e) || (find e rest)

let rec union l1 l2 = match l1 with
    | [] -> l2
    | a :: rest -> if (find a l2) then (union rest l2) else (union rest (a::l2))

let rec remove e l = match l with
    | [] -> []
    | a :: rest -> if a = e then remove e rest else a :: (remove e rest)

(* 
returns a list of strings, which are the names of the variables that are
free in e. free_variables must be implemented according to the function
definition that we have seen in class.
*)
let rec free_variables (e : exp) = match e with
    | Num(n) -> []
    | True -> []
    | False -> []
    | If(e1, e2, e3) -> (union (union (free_variables e1) (free_variables e2)) (free_variables e3))
    | IsZero(e) -> free_variables(e)
    | Plus(e1, e2) -> union (free_variables e1) (free_variables e2)
    | Mult(e1, e2) -> union (free_variables e1) (free_variables e2)
    | Var(s) -> [Var(s)]
    | Lambda(var, body) -> (remove (Var var) (free_variables body))
    | Apply(func, v) -> (free_variables func)
    | otherwise -> []

(* 
(substitution e1 "x" e2) replaces all the free occurances of "x" in the
expression e1 with e2, according to the substitution algoritm that
we have seen in class.
The function substitution raises the exception Substitution_error for
the case of variable capture that we have seen in class

x[e/x] = e
y[e/x] = y   if y is different from x
(e1 + e2)[e/x] = (e1[e/x] + e2[e/x])
... all other cases ... (3/9 lecture?)
*)
let rec substitution (e1 : exp) (x : string) (e2 : exp) = match e1 with
    | Var(var) -> if var = x then e2 else Var(var)
    | True -> True
    | False -> False
    | If(ife1, ife2, ife3) -> If((substitution ife1 x e2), (substitution ife2 x e2), (substitution ife3  x  e2))
    | Num(n) -> Num(n)
    | IsZero(ze1) -> IsZero (substitution ze1 x e2)
    | Plus(pe1, pe2) -> Plus(substitution pe1 x e2, substitution pe2 x e2)
    | Mult(pe1, pe2) -> Mult(substitution pe1 x e2, substitution pe2 x e2)
    | Lambda(var, body) -> if ( (var = x) || (find (Var(var)) (free_variables e2)) ) then Lambda(var, body) else Lambda(var, (substitution body x e2))
    | Apply(ae1, ae2) -> Apply((substitution ae1 x e2), (substitution ae2 x e2))
    | otherwise -> raise Substitution_error

(* 
The function type_check takes in input an expression and returns the
type of that expression according to the type system that we have seen
in class, or the function raises the OCaml exception Type_error when
type checking fails

add cases for variables, functions, and applications
*)

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
        | Num(n) -> TypeError
        | Lambda(v,b) -> TypeError
        | TypeError -> TypeError
        | otherwise -> If(step(e1), e2, e3))
    | IsZero(e) ->  (
        match e with
        | Num(n) -> if (n = 0) then True else False
        | True -> TypeError
        | False -> TypeError
        | Lambda(v,b) -> TypeError
        | TypeError -> TypeError
        | otherwise -> IsZero(step(e)))
    | Plus(e1, e2) -> (
        match e1 with
        | Num(n1) -> (
            match e2 with
            | Num(n2) -> Num(n1+n2)
            | True -> TypeError
            | False -> TypeError
            | Lambda(v,b) -> TypeError
            | TypeError -> TypeError
            | otherwise -> Plus(e1, step(e2)))
        | True -> TypeError
        | False -> TypeError
        | Lambda(v,b) -> TypeError
        | TypeError -> TypeError
        | otherwise -> Plus(step(e1), e2))
    | Mult(e1, e2) -> (
        match e1 with
        | Num(n1) -> (
            match e2 with
            | Num(n2) -> Num(n1*n2)
            | True -> TypeError
            | False -> TypeError
            | Lambda(v,b) -> TypeError
            | TypeError -> TypeError
            | otherwise -> Mult(e1, step(e2)))
        | True -> TypeError
        | False -> TypeError
        | Lambda(v,b) -> TypeError
        | TypeError -> TypeError
        | otherwise -> Mult(step(e1), e2))
    (* Apply --- reduction rules 1-2-3 --- e1 is func, e2 is arg (v)
    
    1)
    e1 --> e1'
    -------------------
    (e1 e2) --> e1' e2
    
    2)
    e2 --> e2'
    -------------------
    (v e2) --> (v e2')

    3)
    ((\lambda x.e) v) --> e[v/x]
    *)
    | Apply(func, arg) -> (
        match func with
        | Lambda(var, body) -> (
            match arg with
            | Num(n) -> (substitution body var arg)
            | True -> (substitution body var arg)
            | False -> (substitution body var arg)
            | Lambda(v,b) -> (substitution body var (Lambda(v,b)))
            | Var(x) -> TypeError
            | TypeError -> TypeError
            | notValue -> Apply(func, step arg))
        | Var(x) -> TypeError
        | Num(n) -> TypeError
        | True -> TypeError
        | False -> TypeError
        | TypeError -> TypeError
        | notLambda -> Apply(step func, arg))
    | otherwise -> TypeError


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
    | Var(x) -> Var(x)
    | IsZero(e) -> multi_step(step(IsZero(e)))
    | Plus(e1, e2) -> multi_step(step(Plus(e1, e2)))
    | Mult(e1, e2) -> multi_step(step(Mult(e1, e2)))
    | Apply(e1, e2) -> multi_step(step(Apply(e1, e2)))
    | Lambda(var, body) -> Lambda(var, body)
    | TypeError -> TypeError
    

let rec string_of_typ (t : typ) = match t with
    | TBool -> "bool"
    | TInt -> "int"
    | TArrow(t1, t2) -> "(" ^ (string_of_typ t1) ^ " -> " ^ (string_of_typ t2) ^ ")"

(* Brought in from interpreter_bigstep for testing *)
let rec string_of_exp (e : exp) = match e with
    | True -> "true"
    | False -> "false"
    | If(e1, e2, e3) -> "if " ^ (string_of_exp e1) ^ " then " ^ (string_of_exp e2) ^ " else " ^ (string_of_exp e3)
    | Num(n) -> string_of_int(n)
    | IsZero(e) -> "(isZero " ^ (string_of_exp e) ^ ")"
    | Plus(e1, e2) -> "(" ^ (string_of_exp e1) ^ " + " ^ (string_of_exp e2) ^ ")"
    | Mult(e1, e2) -> "(" ^ (string_of_exp e1) ^ " * " ^ (string_of_exp e2) ^ ")"
    | Var(x) -> x
    | Lambda(var, e) -> "(lambda " ^ var ^ "." ^ (string_of_exp e) ^ ")"
    | Apply(e1, e2) -> "(" ^ (string_of_exp e1) ^ ", " ^ (string_of_exp e2) ^ ")"
    | TypeError -> "TypeError"
    

let () =
    (* DYNAMIC TYPING *)
    (print_endline "\n1\n");
    (* 1 *)
    (print_endline (string_of_exp (multi_step (If (IsZero (Plus (True, Num 4)), Num 3, Num 4)))
                ));

    (print_endline "\n2-3\n");
    (* 2-3 *)
    (print_endline (string_of_exp (multi_step
   (Apply
      ( Apply
          ( Lambda
              ( "mybool"
              , Lambda
                  ("myfunction", Apply (Var "myfunction", Var "mybool"))
              )
          , Lambda ("x", Plus (Var "x", Var "x")) )
      , True ))) ));
    (print_endline (string_of_exp (multi_step
   (Apply
      ( Lambda
          ( "b"
          , Apply
              ( Lambda
                  ( "x"
                  , Apply (Lambda ("x", Mult (Var "x", Num 1)), Var "x")
                  )
              , If (Var "b", Plus (Num 5, Num 37), False) ) )
      , True ))) ));

    (print_endline "\n4-5\n");
    (* 4-5 *)
    (print_endline (string_of_exp (multi_step
   (Apply
      ( Lambda
          ( "b"
          , Apply
              ( Lambda
                  ( "x"
                  , Apply (Lambda ("x", Mult (Var "x", Num 1)), Var "x")
                  )
              , If (Var "b", Plus (Num 5, Num 37), False) ) )
      , False ))) ));
    (print_endline (string_of_exp (multi_step
   (Apply
      ( Lambda ("f", Apply (Var "f", Num 1))
      , Lambda
          ("x", Mult (Var "x", If (IsZero (Var "x"), False, Num 7))) ))) ));

    (print_endline "\n6-7\n");
    (* 6-7 *)
    (print_endline (string_of_exp (multi_step
   (Apply
      ( Lambda ("f", Apply (Var "f", Num 1))
      , Lambda
          ("x", Mult (Var "x", If (IsZero (Var "y"), False, Num 7))) ))) ));
    (print_endline (string_of_exp (multi_step
   (Apply
      ( Lambda
          ( "f"
          , Apply
              ( Lambda
                  ( "g"
                  , Apply (Var "g", Apply (Apply (Var "f", Num 0), False))
                  )
              , Lambda
                  ( "x"
                  , Mult (Var "x", If (IsZero (Var "x"), Num 1, Var "x"))
                  ) ) )
      , Lambda
          ( "x"
          , Lambda
              ( "b"
              , Plus
                  ( Var "X"
                  , If
                      ( IsZero (Var "x")
                      , If (Var "b", Num (-1), False)
                      , Num 1 ) ) ) ) ))) ));