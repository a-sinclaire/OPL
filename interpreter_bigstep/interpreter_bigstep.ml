type exp =
    | True
    | False
    | If of exp * exp * exp
    | Num of int
    (* On website listed as isZero, but Uppercase required to compile *)
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
    | anything -> "hello world"

let () =
    (*01*)print_endline (string_of_exp (Num(3)));
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
    (*16*)print_endline (string_of_exp (If(True, If(IsZero(Mult(Num(3), Num(5))), Plus(Num(3), Num(2)),  Plus(Num(5), Num(1))), If(True, Mult(Num(3), Num(2)), Mult(Num(2), Plus(Num(3), Num(2)))))));