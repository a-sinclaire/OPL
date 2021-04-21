exception Eval_error
exception Substitution_error
exception NoMatchingEnvironmentVariable

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
    | Let of string * exp * exp

type environment = (string * exp) list

let rec find e l = match l with
    | [] -> false
    | a :: rest -> (a = e) || (find e rest)

let rec union l1 l2 = match l1 with
    | [] -> l2
    | a :: rest -> if (find a l2) then (union rest l2) else (union rest (a::l2))

let rec remove e l = match l with
    | [] -> []
    | a :: rest -> if a = e then remove e rest else a :: (remove e rest)

let rec match_elem e l = match l with
    | [] -> raise NoMatchingEnvironmentVariable
    | a :: rest -> if (fst a = e) then (l, snd a) else (match_elem e rest)

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
    | Let(v,e1,e2) -> (remove (Var v) (union (free_variables e1) (free_variables e2)))
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
    | Let(v,le1,le2) -> if (v = x) then (Let(v, (substitution le1 x e2), le2)) else ( if (find (Var v) (free_variables e2)) then (raise Substitution_error) else (Let(v, (substitution le1 x e2), (substitution le2 x e2))) )
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
let rec step (env : environment) (e : exp) : (environment * exp) = match e with
    | If(e1, e2, e3) -> (
        match e1 with
        | True -> (env, e2)
        | False -> (env, e3)
        | Num(n) -> (env, TypeError)
        | Lambda(v,b) -> (env, TypeError)
        | TypeError -> (env, TypeError)
        | otherwise -> let p = (step env e1) in (union (fst p) env, If(snd p, e2, e3))
    )
    | IsZero(e) ->  (
        match e with
        | Num(n) -> if (n = 0) then (env, True) else (env, False)
        | True -> (env, TypeError)
        | False -> (env, TypeError)
        | Lambda(v,b) -> (env, TypeError)
        | TypeError -> (env, TypeError)
        | otherwise -> let p = step env e in (union (fst p) env, IsZero(snd p)))
    | Plus(e1, e2) -> (
        match e1 with
        | Num(n1) -> (
            match e2 with
            | Num(n2) -> (env, Num(n1+n2))
            | True -> (env, TypeError)
            | False -> (env, TypeError)
            | Lambda(v,b) -> (env, TypeError)
            | TypeError -> (env, TypeError)
            | otherwise -> let p = step env e2 in (union (fst p) env, Plus(e1, snd p)))
        | True -> (env, TypeError)
        | False -> (env, TypeError)
        | Lambda(v,b) -> (env, TypeError)
        | TypeError -> (env, TypeError)
        | otherwise -> let p = step env e1 in (union (fst p) env, Plus(snd p, e2)))
    | Mult(e1, e2) -> (
        match e1 with
        | Num(n1) -> (
            match e2 with
            | Num(n2) -> (env, Num(n1*n2))
            | True -> (env, TypeError)
            | False -> (env, TypeError)
            | Lambda(v,b) -> (env, TypeError)
            | TypeError -> (env, TypeError)
            | otherwise -> let p = step env e2 in (union (fst p) env, Mult(e1, snd p)))
        | True -> (env, TypeError)
        | False -> (env, TypeError)
        | Lambda(v,b) -> (env, TypeError)
        | TypeError -> (env, TypeError)
        | otherwise -> let p = step env e1 in (union (fst p) env, Mult(snd p, e2)))
    | Apply(e1, e2) -> (
        match e1 with
        | Lambda(var, body) -> (
            match e2 with
            | True -> ((var,True)::env), body
            | False -> ((var,False)::env), body
            | Num(n) -> ((var,Num n)::env), body
            | Lambda(v,b) -> ((var,Lambda(v,b))::env), body
            | TypeError -> ((var,TypeError)::env), body
            | notValue -> let p = step env e2 in ((var, e2)::env), Apply(Lambda(var,body), snd p)
        )
        | True -> (env, TypeError)
        | False -> (env, TypeError)
        | Num(n) -> (env, TypeError)
        | TypeError -> (env, TypeError)
        | notLambda -> let p = step env e1 in (env, Apply(snd p, e2))
        )
    | Var(x) -> (
        match env with
        | [] -> (env, TypeError)
        | elem :: rest -> if fst elem = x then (env, snd elem) else step rest (Var(x))
    )
    | Let(v, e1, e2) -> (env, Apply(Lambda(v,e2), e1))
    | otherwise -> (env, TypeError)


(*
The function multi_step takes in input an
expression and iterates the function step in order
to evaluate the expression one step at a time until
it returns a value, or raises OCaml exception Eval_error
if the computation fails
*)
let rec multi_step (env : environment) (e : exp) : (environment * exp) = match e with
    | True -> (env, True)
    | False -> (env, False)
    | Num(n) -> (env, Num(n))
    | Lambda(var, body) -> (env, Lambda(var, body))
    | TypeError -> (env, TypeError)
    | otherwise -> let afterstep = step env e in multi_step (fst afterstep) (snd afterstep)
    (* | If(e1, e2, e3) -> let afterstep =(step env e) in (multi_step (fst afterstep) (snd afterstep))
    | Var(x) -> (multi_step (fst(step env (Var x))) (snd(step env (Var x))) )
    | IsZero(ze) -> (multi_step (fst(step env (IsZero(e)))) (snd(step env (IsZero(e)))) )
    | Plus(e1, e2) -> (multi_step (fst(step env (Plus(e1, e2)))) (snd(step env (Plus(e1, e2)))) )
    | Mult(e1, e2) -> (multi_step (fst(step env (Mult(e1, e2)))) (snd(step env (Mult(e1, e2)))) )
    | Apply(e1, e2) -> (multi_step (fst(step env (Apply(e1, e2)))) (snd(step env (Apply(e1, e2)))) )
    | Let(s,e1,e2) -> (multi_step (fst(step env (Let(s,e1,e2)))) (snd(step env (Let(s,e1,e2)))) ) *)
    

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
    | Let(s,e1,e2) -> "Test"

let rec string_of_env env = match env with
    | [] -> "()"
    | elem :: rest -> "(" ^ (fst elem) ^ ", " ^ string_of_exp (snd elem) ^ ")" ^ (string_of_env rest)


let () =
    (* DYNAMIC TYPING *)
    (print_endline "\nDynamicScoping\n--------------");
    (* 1 *)
    (print_endline (string_of_exp (multi_step [] (Let ("x", Num 5, Num 1)) |> snd) ));
    (* (print_endline (string_of_env (multi_step [] (Let ("x", Num 5, Num 1)) |> fst) ));
    (print_endline ""); *)

    (* 2 *)
    (print_endline (string_of_exp (multi_step [] (Let ("x", Num 5, Plus (Var "x", Num 5))) |> snd) ));
    (* (print_endline (string_of_env (multi_step [] (Let ("x", Num 5, Plus (Var "x", Num 5))) |> fst) ));
    (print_endline ""); *)

    (* 3 *)
    (print_endline (string_of_exp ( multi_step [] (Let ("x", Num 3, Let ("y", Num 5, Mult (Var "x", Var "y")))) |> snd ) ));
    (* (print_endline (string_of_env ( multi_step [] (Let ("x", Num 3, Let ("y", Num 5, Mult (Var "x", Var "y")))) |> fst ) ));
    (print_endline ""); *)

    (* 4 *)
    (print_endline (string_of_exp ( multi_step [] (Let ("x", Num 3, Let ("x", Num 5, Mult (Var "x", Var "x")))) |> snd ) ));
    (* (print_endline (string_of_env ( multi_step [] (Let ("x", Num 3, Let ("x", Num 5, Mult (Var "x", Var "x")))) |> fst ) ));
    (print_endline ""); *)

    (* 5 *)
    (print_endline (string_of_exp ( multi_step [] (Mult ( Apply ( Lambda ("b", If (Var "b", Let ("x", Num 2, Num 1), Num 0)), True ), Var "x" ) ) |> snd ) ));
    (* (print_endline (string_of_env ( multi_step [] (Mult ( Apply ( Lambda ("b", If (Var "b", Let ("x", Num 2, Num 1), Num 0)), True ), Var "x" ) ) |> fst ) ));
    (print_endline ""); *)

    (* 6 *)
    (print_endline (string_of_exp ( multi_step [] ( Plus ( Apply ( Lambda ( "n", If ( IsZero (Var "n"), Let ("x", Num 5, Var "n"), Let ( "n", Num 6, Let ("x", Plus (Var "n", Num 1), Var "n") )
                    ) ), Num 0 ), Var "x" ) ) |> snd ) ));
    (* (print_endline (string_of_env ( multi_step [] ( Plus ( Apply ( Lambda ( "n", If ( IsZero (Var "n"), Let ("x", Num 5, Var "n"), Let ( "n", Num 6, Let ("x", Plus (Var "n", Num 1), Var "n") )
                    ) ), Num 0 ), Var "x" ) ) |> fst ) ));
    (print_endline ""); *)

    (* 7 *)
    (print_endline (string_of_exp ( multi_step [] ( Let ( "x", Num 1, Let ( "f", Lambda ("a", Plus (Var "x", Var "a")), Let
                ( "g", Lambda ("a", Let ("x", Num 2, Apply (Var "f", Var "a"))), Apply (Var "g", Num 3) ) ) ) ) |> snd ) ));
    (* (print_endline (string_of_env ( multi_step [] ( Let ( "x", Num 1, Let ( "f", Lambda ("a", Plus (Var "x", Var "a")), Let
                ( "g", Lambda ("a", Let ("x", Num 2, Apply (Var "f", Var "a"))), Apply (Var "g", Num 3) ) ) ) ) |> fst ) )); *)



(print_endline "\n\nDynamicTyping\n--------------");
(print_endline (string_of_exp (multi_step [] (If (IsZero (Plus (True, Num 4)), Num 3, Num 4))|>snd) ));
(print_endline (string_of_exp (multi_step []  
   (Apply
      ( Apply
          ( Lambda
              ( "mybool"
              , Lambda
                  ("myfunction", Apply (Var "myfunction", Var "mybool"))
              )
          , Lambda ("x", Plus (Var "x", Var "x")) )
      , True ))|>snd) ));
(print_endline (string_of_exp (multi_step []  
   (Apply
      ( Lambda
          ( "b"
          , Apply
              ( Lambda
                  ( "x"
                  , Apply (Lambda ("x", Mult (Var "x", Num 1)), Var "x")
                  )
              , If (Var "b", Plus (Num 5, Num 37), False) ) )
      , True ))|>snd) ));
(print_endline (string_of_exp (multi_step []  
   (Apply
      ( Lambda
          ( "b"
          , Apply
              ( Lambda
                  ( "x"
                  , Apply (Lambda ("x", Mult (Var "x", Num 1)), Var "x")
                  )
              , If (Var "b", Plus (Num 5, Num 37), False) ) )
      , False ))|>snd)
 ));
(print_endline (string_of_exp (multi_step []  
   (Apply
      ( Lambda ("f", Apply (Var "f", Num 1))
      , Lambda
          ("x", Mult (Var "x", If (IsZero (Var "x"), False, Num 7))) ))|>snd)
 ));
(print_endline (string_of_exp (multi_step [] 
   (Apply
      ( Lambda ("f", Apply (Var "f", Num 1))
      , Lambda
          ("x", Mult (Var "x", If (IsZero (Var "y"), False, Num 7))) ))|>snd) ));
(print_endline (string_of_exp (multi_step []  
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
                      , Num 1 ) ) ) ) ))|>snd) ));