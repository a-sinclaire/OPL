exception Eval_error
exception Type_error
exception Substitution_error
exception Not_In_Memory

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
    | Lambda of string * typ * exp
    | Apply of exp * exp
    | LambdaRec of string * typ * typ * string * exp
    | Div of exp * exp
    | Try of exp * exp
    | RaiseDivByZero of typ * exp
    | Label of int
    | Malloc of exp
    | Mread of exp
    | Assign of exp * exp
    | Sequence of exp * exp
    | Unit

type memory = (int * exp) list

let rec find e l = match l with
    | [] -> false
    | a :: rest -> (a = e) || (find e rest)

let rec union l1 l2 = match l1 with
    | [] -> l2
    | a :: rest -> if (find a l2) then (union rest l2) else (union rest (a::l2))

let rec remove e l = match l with
    | [] -> []
    | a :: rest -> if a = e then remove e rest else a :: (remove e rest)


let rec read_mem l m = match m with
    | [] -> raise Not_In_Memory
    | a :: rest -> if (fst a = l) then (snd a) else (read_mem l rest)

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
    | Lambda(var, typ, body) -> (remove (Var var) (free_variables body))
    | Apply(func, v) -> (free_variables func)
    | LambdaRec(name, t1, t2, var, body) -> (remove (Var var) (remove (Var name) (free_variables body)))
    | Div(e1, e2) -> union (free_variables e1) (free_variables e2)
    | Try(e1, e2) -> union (free_variables e1) (free_variables e2)
    | RaiseDivByZero(typ, e1) -> (free_variables e1)
    | Label(n) -> []
    | Malloc(v) -> free_variables v
    | Mread(v) -> free_variables v
    | Assign(ae1, ae2) -> union (free_variables ae1) (free_variables ae2)
    | Sequence(se1, se2) -> union (free_variables se1) (free_variables se2)
    | Unit -> []


let not x = match x with
    | true -> false
    | false -> true

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
    | Lambda(var, typ, body) -> if ( (var = x) || (find (Var(var)) (free_variables e2)) ) then Lambda(var, typ, body) else Lambda(var, typ, (substitution body x e2))
    | Apply(ae1, ae2) -> Apply((substitution ae1 x e2), (substitution ae2 x e2))
    | LambdaRec(name, t1, t2, var, body) -> if ( (var = x) || (name = x) ) then (
            LambdaRec(name, t1, t2, var, body) 
        ) else (
            if ( (var != x) && (name != x) ) then (
                if ((not (find (Var(var)) (free_variables e2))) && (not (find (Var(name)) (free_variables e2))) ) then (
                    LambdaRec(name, t1, t2, var, (substitution body x e2))
                ) else (
                    raise Substitution_error
                )
            ) else (
                raise Substitution_error
        )
    )
    | Div(de1, de2) -> Div(substitution de1 x e2, substitution de2 x e2)
    | Try(te1, te2) -> Try(substitution te1 x e2, substitution te2 x e2)
    | RaiseDivByZero(typ, re1) -> RaiseDivByZero(typ, substitution re1 x e2)
    | Label(n) -> Label(n)
    | Malloc(v) -> Malloc(substitution v x e2)
    | Mread(v) -> Mread(substitution v x e2)
    | Assign(ae1, ae2) -> Assign((substitution ae1 x e2),(substitution ae2 x e2))
    | Sequence(se1, se2) -> Sequence((substitution se1 x e2),(substitution se2 x e2))
    | Unit -> Unit


(*
The function step takes in input an
expression and returns the expression that
results from computing one step of the expression
in input, or raises OCaml exception Eval_error if
the computation fails
*)
let rec step (e : exp) (m : memory) = match e with
    | If(e1, e2, e3) -> (
        match e1 with
        | True -> (e2, m)
        | False -> (e3, m)
        | Num(n) -> raise Eval_error
        | RaiseDivByZero(typ, n) -> ((RaiseDivByZero(typ, n)), m)
        | otherwise -> let p = (step e1 m) in ((If(fst p, e2, e3)), union (snd p) m))
    | IsZero(e) ->  (
        match e with
        | Num(n) -> if (n = 0) then (True, m) else (False, m)
        | True -> raise Eval_error
        | False -> raise Eval_error
        | RaiseDivByZero(typ, n) -> ((RaiseDivByZero(typ, n)), m)
        | otherwise -> let p = (step e m) in ((IsZero(fst p)), union (snd p) m))
    | Plus(e1, e2) -> (
        match e1 with
        | Num(n1) -> (
            match e2 with
            | Num(n2) -> ((Num(n1+n2)), m)
            | True -> raise Eval_error
            | False -> raise Eval_error
            | RaiseDivByZero(typ, n) -> ((RaiseDivByZero(typ, n)), m)
            | otherwise -> let p = (step e2 m) in (((Plus(e1, fst p))), union (snd p) m))
        | True -> raise Eval_error
        | False -> raise Eval_error
        | RaiseDivByZero(typ, n) -> ((RaiseDivByZero(typ, n)), m)
        | otherwise -> let p = (step e1 m) in (((Plus(fst p, e2))), union (snd p) m))
    | Mult(e1, e2) -> (
        match e1 with
        | Num(n1) -> (
            match e2 with
            | Num(n2) -> ((Num(n1*n2)), m)
            | True -> raise Eval_error
            | False -> raise Eval_error
            | RaiseDivByZero(typ, n) -> ((RaiseDivByZero(typ, n)), m)
            | otherwise -> let p = (step e2 m) in (((Mult(e1, fst p))), union (snd p) m))
        | True -> raise Eval_error
        | False -> raise Eval_error
        | RaiseDivByZero(typ, n) -> ((RaiseDivByZero(typ, n)), m)
        | otherwise -> let p = (step e1 m) in (((Mult(fst p, e2))), union (snd p) m))
    | Apply(func, arg) -> (
        match func with
        | Lambda(var, typ, body) -> (
            match arg with
            | Num(n) -> ((substitution body var arg), m)
            | True -> ((substitution body var arg), m)
            | False -> ((substitution body var arg), m)
            | Lambda(v,t,b) -> ((substitution body var (Lambda(v,t,b))), m)
            | LambdaRec(name, t1, t2, var, body) -> ((substitution body var arg), m)
            | Var(x) -> raise Eval_error
            | RaiseDivByZero(typ, n) -> ((RaiseDivByZero(typ, n)), m)
            | notValue -> let p = (step arg m) in (Apply(func, fst p)), union (snd p) m)
        | LambdaRec(name, t1, t2, var, body) -> (
            match arg with
            | Num(n) -> ((substitution (substitution body var arg) name (LambdaRec(name, t1, t2, var, body))), m)
            | True -> ((substitution (substitution body var arg) name (LambdaRec(name, t1, t2, var, body))), m)
            | False -> ((substitution (substitution body var arg) name (LambdaRec(name, t1, t2, var, body))), m)
            | Lambda(v,t,b) -> ((substitution (substitution body var arg) name (LambdaRec(name, t1, t2, var, body))), m)
            | LambdaRec(name, t1, t2, var, body) -> ((substitution (substitution body var arg) name (LambdaRec(name, t1, t2, var, body))), m)
            | Var(x) -> raise Eval_error
            | RaiseDivByZero(typ, n) -> ((RaiseDivByZero(typ, n)), m)
            | notValue -> let p = (step arg m) in ((Apply(func, fst p)), union (snd p) m))
        | Var(x) -> raise Eval_error
        | Num(n) -> raise Eval_error
        | True -> raise Eval_error
        | False -> raise Eval_error
        | RaiseDivByZero(typ, n) -> ((RaiseDivByZero(typ, n)), m)
        | notLambda -> let p = (step func m) in ((Apply(fst p, arg)), union (snd p) m))
    | Div(e1, e2) -> (
        match e1 with
        | Num(n1) -> (
            match e2 with
            | Num(n2) -> if e2 = Num(0) then ((RaiseDivByZero(TInt, e1)), m) else ((Num(n1/n2)), m)
            | True -> raise Eval_error
            | False -> raise Eval_error
            | otherwise -> let p = (step e2 m) in (((Div(e1, fst p)), union (snd p) m))
        )
        | True -> raise Eval_error
        | False -> raise Eval_error
        | otherwise -> let p = (step e1 m) in (((Div(fst p, e2)), union (snd p) m))
    )
    | Try(e1, e2) -> (
        match e1 with
        | RaiseDivByZero(typ, v) -> ((Apply(e2, v)), m)
        | Div(a,b) -> let p = (step e1 m) in ((Try(fst p, e2)), union (snd p) m)
        | Mult(a,b) -> let p = (step e1 m) in ((Try(fst p, e2)), union (snd p) m)
        | Plus(a,b) -> let p = (step e1 m) in ((Try(fst p, e2)), union (snd p) m)
        | IsZero(a) -> let p = (step e1 m) in ((Try(fst p, e2)), union (snd p) m)
        | If(a,b,c) -> let p = (step e1 m) in ((Try(fst p, e2)), union (snd p) m)
        | Apply(a,b)-> let p = (step e1 m) in ((Try(fst p, e2)), union (snd p) m)
        | value -> (e1, m)
    )
    | Label(n) -> raise Eval_error
    | Malloc(v) -> let l = (List.length m) in (Label(l), ((l, fst(step v m))::m))
    | Mread(v) -> (
        match v with
        | Label(n) -> (
            match m with
            | [] -> raise Not_In_Memory
            | elem :: rest -> if (fst elem = n) then (snd elem, m) else step (Mread(v)) rest
            )
        | otherwise -> let p = (step v m) in (Mread(fst p), union (snd p) m)
    )
    | Assign(e1, e2) -> (
        match e1 with
        | Label(n) -> (
            match m with
            | [] -> raise Eval_error (*TODO - replace bits of memory*)
            | elem :: rest -> raise Eval_error
        )
        | otherwise -> let p = (step e1 m) in (Assign(fst p, e2), union (snd p) m)
    )
    | Sequence(e1, e2) -> raise Eval_error

    | True -> (e, m)
    | False -> (e, m)
    | Unit -> (e, m)
    | Var(x) -> (e, m)
    | Num(n) -> (e, m)
    | Lambda(a,b,c) -> (e, m)
    | LambdaRec(a,b,c,d,f) -> (e, m)
    | RaiseDivByZero(a,b) -> (e, m)
    (* | otherwise -> raise Eval_error *)


(*
The function multi_step takes in input an
expression and iterates the function step in order
to evaluate the expression one step at a time until
it returns a value, or raises OCaml exception Eval_error
if the computation fails
*)
let rec multi_step (e : exp) (m : memory) = match e with
    | True ->   (e, m)
    | False ->  (e, m)
    | Unit ->   (e, m)
    | Var(x) -> (e, m)
    | Num(n) -> (e, m)
    | Label(n) -> (e, m)
    | Lambda(var, typ, body) -> (e, m)
    | LambdaRec(name, t1, t2, var, body) -> (e, m)
    | RaiseDivByZero(typ, e1) -> (RaiseDivByZero(typ, fst(multi_step e1 m)), m)
    | __ -> let afterstep = step e m in multi_step (fst afterstep) (snd afterstep)
    (* | other -> ((RaiseDivByZero(TInt, Num(-1))), m) *)
    

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
    | Lambda(var, typ, e) -> "(lambda " ^ var ^ ":" ^ (string_of_typ typ) ^ "." ^ (string_of_exp e) ^ ")"
    | Apply(e1, e2) -> "(" ^ (string_of_exp e1) ^ ", " ^ (string_of_exp e2) ^ ")"
    | LambdaRec(name, t1, t2, var, body) -> "(LambdaRec (" ^ name ^ " : " ^ (string_of_typ t1) ^ " -> " ^ (string_of_typ t2) ^ ") " ^ var ^ " = " ^ (string_of_exp body) ^ ")"
    | Div(e1, e2) -> "(" ^ (string_of_exp e1) ^ " / " ^ (string_of_exp e2) ^ ")"
    | Try(e1, e2) -> "try (" ^ (string_of_exp e1) ^ ") with (" ^ (string_of_exp e2) ^ ")"
    | RaiseDivByZero(typ, e1) -> "RaiseDivByZero (" ^ (string_of_typ typ) ^ ", " ^ (string_of_exp e1) ^")"
    | Label(n) -> "(Label " ^ string_of_int n ^ ")"
    | other -> "MISSING STRING_TO_EXP INFO"
    
let () =
    (* References/Memory *)
    (print_endline "\n1-2\n");
    (* 1-2 *)

    (print_endline (string_of_exp ((multi_step (Malloc (Num 1)) [] |> fst))));
    (print_endline (string_of_exp ((multi_step (Mread (Malloc (Malloc (Num 1)))) [] |> fst))));

    (* (print_endline "\n3-4\n");
    (* 3-4 *)

    (print_endline (string_of_exp (multi_step
  (Apply (Lambda ("n", TRef TInt, Mread (Var "n")), Label 0))
  [])));
    (print_endline (string_of_exp (( multi_step
    (Apply
       ( Lambda ("n", TRef TInt, Mread (Var "n"))
       , Malloc (Plus (Num 5, Num 1)) ))
    []
|> fst ))));

    (print_endline "\n5\n");
    (* 5 *)

    (print_endline (string_of_exp (( multi_step
    (Apply
       ( Lambda
           ( "b"
           , TRef TBool
           , Sequence
               ( If (Mread (Var "b"), Assign (Var "b", False), Unit)
               , Mread (Var "b") ) )
       , Malloc True ))
    []
|> fst ))));

    (print_endline "\n6\n");
    (* 6 *)

    (print_endline (string_of_exp (( multi_step
    (Apply
       ( Lambda
           ( "n"
           , TRef TInt
           , Sequence
               ( Assign (Var "n", Plus (Mread (Var "n"), Num 1))
               , Assign (Var "n", Mult (Mread (Var "n"), Num 2)) ) )
       , Malloc (Num 3) ))
    []
|> fst ))));

    (print_endline "\n7\n");
    (* 7 *)
    
    (print_endline (string_of_exp (( multi_step
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
|> fst ))));

    (print_endline "\n8\n");
    (* 8 *)

    (print_endline (string_of_exp (( multi_step
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
|> fst )))); *)
