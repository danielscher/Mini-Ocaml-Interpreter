open String
open List

(*MOCaml abstract syntax and types*)

type ('a,'b) env = ('a * 'b) list;; (*polymorphic environment for evl and typ*)
type ty = Bool | Int | Arrow of ty * ty;;
type con = Bcon of bool | Icon of int;;
type op = Add | Sub | Mul | Leq;;
type var = string;;
type exp = Var of var | Con of con
          |Oapp of op * exp * exp
          |Fapp of exp * exp
          |If of exp * exp * exp
          |Lam of var * exp
          |Lamty of var * ty * exp
          |Let of var * exp * exp
          |Letrec of var * var * exp * exp
          |Letrecty of var * var * ty * ty * exp * exp  (*f (x:t1) :t2*);;

(*~~~~~~~~~~~~~~enviroment functions~~~~~~~~~~~~~~*)

(*an empty environment*)
let empty : ('a,'b) env = [];;

(*updates the type environment with a new type binding*)
let update (env : ('a,'b) env) a b : ('a,'b) env = (a,b)::env;;

(*returns the type of some variable if present in the env*)
let rec lookup (env : ('a,'b) env) a = match env with
|[] -> None
|(v,t)::env' -> if a = v then Some t else lookup env' a;; 


(*~~~~~~~~~~~~~MOCaml type checker~~~~~~~~~~~~~~~*)

let rec check env e : ty = match e with
  |Var x -> check_var env x
  |Con (Bcon b) -> Bool
  |Con (Icon n) -> Int
  |Oapp (o,e1,e2) -> check_op o (check env e1) (check env e2)
  |Fapp (e1,e2) -> check_fun (check env e1) (check env e2)
  |If (e1,e2,e3) -> check_ite (check env e1) (check env e2) (check env e3)
  |Lam (_,_) -> failwith "check: lam is missing type"
  |Lamty (x,t,e) -> Arrow (t,check (update env x t) e)
  |Let (x,e1,e2) -> check (update env x (check env e1)) e2
  |Letrec (f,x,e1,e2) -> failwith "check: letrec is missing type"
  |Letrecty (f,x,t1,t2,e1,e2) -> if check_e1_rec env f x t1 t2 e1 then check (update env f (Arrow(t1,t2))) e2 else failwith "letrec"
                               (*^ first checks if e1 derives to t2 then checks e2*)
  and check_op o t1 t2 = match o,t1,t2 with (*checks if both arguments are ints*)
  |Add, Int, Int -> Int
  |Sub, Int, Int -> Int
  |Mul, Int, Int -> Int
  |Leq, Int, Int -> Bool
  |_,_,_ -> failwith "checkop"
  and check_fun t t' = match t with
  |Arrow (t1,t2) -> if t1 = t' then t2 else failwith "check_fun: type mismatch"
  |_ -> failwith "check_fun: type mismatch"
  and check_var env x =
  let t' = lookup env x in
    begin match t' with 
      |Some a -> a
      |None -> failwith "check_var"
    end
  and check_ite t1 t2 t3 = match t1 with
  |Bool -> if t2 = t3 then t2 else failwith "ite: e2 is not the same type as e3"
  |_-> failwith "ite: e1 bool expected"
  and check_e1_rec env f x t1 t2 e1 =check (update (update env f (Arrow(t1,t2))) x t1 ) e1 = t2 (* extends the env with the types of f then x*);;

(*~~~~~~Type checker tests~~~~~~~*)

(*(fun x -> x*2) 5 :int*)
let test1 = check empty 
(Fapp(
  Lamty(
    "x",
    Int,
    Oapp (Mul,Var("x"),Con(Icon(2)))
  )
  ,
   Con (Icon(5))
)
) = Int;;

(** TODO : THROWS EXCEPTION CHECK OP
(*Let rec fac n = if n<1 then 1 else n*fac(n-1) : int*)
let test2 = check empty (
  Letrecty ("fac", "n", Int, (Arrow(Int,Int)),
    If (Oapp (Leq, Var "n" , (Con(Icon(1)))),
      Con (Icon(1)),
      Oapp(Mul, Var "n" , Fapp(Var "fac" ,Oapp (Sub,Var "n" ,Con(Icon(1)))))),
    Fapp (Var "fac",Con (Icon(5)))
  )
);;*)

let test3 = check empty
  (Letrecty ("fac", "a", Int, Arrow(Int,Int), 
             Lamty ("n", Int,
                    If (Oapp (Leq, Var "n", Con (Icon 1)), Var "a",
                        Fapp (Fapp (Var "fac", Oapp (Mul, Var "n", Var "a")),
                              Oapp (Sub, Var "n", Con (Icon 1))))),
             Fapp (Fapp (Var "fac", Con (Icon 1)), Con (Icon 4))));;

(*~~~~~~~~~~~~~MOCaml evaluator~~~~~~~~~~~~~~~*)

type value = Bval of bool | Ival of int 
            |Closure of var * exp * (var,value) env
            |Rclosure of var * var * exp * (var,value) env;;


let rec eval env e : value = match e with
    |Var x -> 
      begin match lookup env x with
      |Some v -> v
      |None -> failwith "Var x is not present in the environment"
    end
    |Con (Bcon b) -> Bval b
    |Con (Icon n) -> Ival n
    |Oapp (o,e1,e2) -> eval_op o (eval env e1) (eval env e2)
    |Fapp (e1,e2) -> eval_fapp (eval env e1) (eval env e2)
    |If (e1,e2,e3) ->eval_ite (eval env e1) e2 e3 env
    |Lam (x,e) |Lamty (x,_,e) -> Closure(x,e,env)
    |Let (x,e1,e2) -> eval (update env x (eval env e1)) e2
    |Letrec (f,x,e1,e2) |Letrecty (f,x,_,_,e1,e2) -> eval (update env f (Rclosure(f, x, e1, env))) e2
and eval_op o v1 v2 = match o,v1,v2 with
  |Add, Ival(i1), Ival(i2) -> Ival(i1 + i2)
  |Sub, Ival(i1), Ival(i2) -> Ival(i1 - i2)
  |Mul, Ival(i1), Ival(i2) -> Ival(i1 * i2)
  |Leq, Ival(i1), Ival(i2) -> Bval(i1 <= i2)
  |_ -> failwith "eval_op:Illegal operator"
and eval_fapp v1 v2 = match v1 with
  |Closure(x,e,env') -> eval (update env' x v2) e
  |Rclosure(f,x,e,env') -> eval (update (update env' f v1) x v2) e
  |_ -> failwith "eval_fun: cannot apply e2 to e1"
and eval_ite v1 e2 e3 env = match v1 with
  |Bval b -> if b then (eval env e2) else (eval env e3)
  |_-> failwith "eval_ite: expected bool"
and eval_letrec v1 e2 = match v1 with
  |Rclosure(f,x,e,env') -> eval (update env' f v1) e2
  |_-> failwith "eval_letrec: v1 is not a closure";;


(*~~~~~~~~~~~~~Evaluation tests~~~~~~~~~~~~~~~~~*)
(*test If expression evals to false*)
let test4 = eval empty
(Oapp(Leq,Con (Icon(1)),Con(Icon(5))));;


let test4 = eval empty
  (Letrec ("fac", "a",
           Lam ("n",
                If (Oapp (Leq, Var "n", Con (Icon 1)), Var "a",
                    Fapp (Fapp (Var "fac", Oapp (Mul, Var "n", Var "a")),
                          Oapp (Sub, Var "n", Con (Icon 1))))),
           Fapp (Fapp (Var "fac", Con (Icon 1)), Con (Icon 4))));;


(*evals to 25*)
let test5 = eval empty
    (Let ("x" , Con (Icon (5)),
       Oapp(Mul, Con (Icon (5)),Var "x")
          )
    );;




(*~~~~~~~~~~~~~TOKEN CONSTRUCTORS~~~~~~~~~~~~~~~~~*)
type const = BCON of bool | ICON of int
type token = LP | RP | EQ | COL | ARR | ADD 
            | SUB | MUL | LEQ | IF | THEN | ELSE 
            | LAM | LET | IN | REC | CON of const 
            | VAR of string | BOOL | INT ;;

let whitespace c = Char.code c = 32 || Char.code c = 9 || Char.code c = 10|| Char.code c = 95 || Char.code c = 39 || Char.code c = 13
let digit c = let ascii = Char.code c in 
    ascii >= 48 && ascii <= 57;;
let lc_char c = let ascii = Char.code c in 
ascii >= 97 && ascii <= 122;;
let uc_char c = let ascii = Char.code c in 
ascii >= 65 && ascii <= 90;;
let legal_id_char c = digit c || lc_char c || uc_char c 
let num c = match Char.code c with
    |48 -> 0
    |49 -> 1
    |50 -> 2
    |51 -> 3
    |52 -> 4
    |53 -> 5
    |54 -> 6
    |55 -> 7
    |56 -> 8
    |57 -> 9
    |_ -> failwith "num: expected ascii of a digit";;
    
(*~~~~~~~~~~~~~~~~~~~~~Lexer~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
  let lex s : token list =
    let get i = String.get s i in
    let getstr i n = String.sub s (i-n) n  in
    let exhausted i = i >= String.length s in
    let verify i c = not (exhausted i) && get i = c in
    let rec lex i l = if (exhausted i) then List.rev l 
      else match get i with
      |'(' -> lex (i+1) (LP::l)
      |')' -> lex (i+1) (RP::l)
      |'=' -> lex (i+1) (EQ::l)
      |':' -> lex (i+1) (COL::l)
      |'+' -> lex (i+1) (ADD::l)
      |'*' -> lex (i+1) (MUL::l)
      |'-' -> if verify (i+1) '>' then lex (i+2) (ARR::l) else lex (i+1) (SUB::l)
      |'<' -> if verify (i+1) '=' then lex (i+2) (LEQ::l) else failwith "lex_leq: expected a '='"
      |c when whitespace c -> lex (i+1) l
      |c when digit c -> lex_num (num c) (i+1) l
      |c when lc_char c -> lex_id (i+1) 1 l
      |c -> failwith "lex: illegal character"
    and lex_num int_lit i l = if not (exhausted i) then
      begin match get i with
        |c when digit c -> lex_num (int_lit * 10 + (num c)) (i + 1) l
        |c when whitespace c -> lex_num' int_lit (i + 1) l
        |_ -> lex_num' int_lit i l
      end
      else lex_num' int_lit i l
    and lex_num' int_lit i l = lex i (CON (ICON int_lit)::l)
    and lex_id i len l = if exhausted i then lex_id' i len l else
        match get i with 
          |c when legal_id_char c -> lex_id (i+1) (len+1) l
          |c when whitespace c -> lex_id' i len l
          |_ -> lex_id' i len l
    and lex_id' i len l = match getstr i len with
      |"if" -> lex (i) (IF::l)
      |"then" -> lex (i) (THEN::l)
      |"else" -> lex (i) (ELSE::l)
      |"fun" -> lex (i) (LAM::l)
      |"let" -> lex (i) (LET::l)
      |"rec" -> lex (i) (REC::l)
      |"in" -> lex (i) (IN::l)
      |"int" -> lex (i) (INT::l)
      |"bool" -> lex (i) (BOOL::l)
      |"true" -> lex (i) (CON (BCON true)::l)
      |"false" -> lex (i) (CON (BCON false)::l)
      |"\t" | "\n" -> lex (i) l
      |s -> lex (i) (VAR s::l) 
  in lex 0 [];;


(*~~~~~~~~~~~~~~~~~~~~~Lexer Tests~~~~~~~~~~~~~~~~~~~~~~~~*)
let str1 = "x";;
let str2 =
  "let rec pow n e = if e <= 1 then 1 else n * pow n (e-1)";;

let test = lex str1;;

(*~~~~~~~~~~~~~~~~Recursive decent parser~~~~~~~~~~~~~~~~~~~~~~~*)

let verify t l = match l with 
  |t'::l -> if t' = t then l else failwith "Verify: expected Token not found"
  |[]-> failwith "Verify: Token list is empty"

let rec parse l : (exp * token list) = match l with            (*top level parser*)
  |IF::l -> 
    let (e1,l) = parse l in
    let (e2,l) = parse (verify THEN l) in
    let (e3,l) = parse (verify ELSE l) in
    (If(e1,e2,e3),l)
  |LET::VAR(x)::EQ::l -> 
    let (e1,l) = parse l in
    let (e2,l) = parse (verify IN l) in
    (Let(x,e1,e2),l)
  |LET::REC::VAR(f)::VAR(x)::EQ::l ->
    let (e1,l) = parse l in
    let (e2,l) = parse (verify IN l) in
    (Letrec(f,x,e1,e2),l)
  |LET::REC::VAR(f)::LP::VAR(x)::COL::EQ::l ->
    let (t1,l) = tparse l in
    let (t2,l) = tparse (verify RP l) in
    let (e1,l) = parse (verify EQ l) in
    let (e2,l) = parse (verify IN l) in
    (Letrecty(f,x,t1,t2,e1,e2),l)
  |LAM::VAR(x)::ARR::l -> 
    let (e,l) = parse l in (Lam (x,e),l)
  |LAM::VAR(x)::COL::l -> 
    let (t1,l) = tparse l in
    let (e,l) = parse (verify EQ l) in 
    (Lamty(x,t1,e),l)
  |l -> cparse l
  and cparse l = let (e,l) = sparse l in cparse' e l            (*comparison level parsing*)
  and cparse' e l = match l with
  |LEQ::l -> let (e2,l) = sparse l in (Oapp(Leq,e,e2),l)
  |l -> (e,l)
  and sparse l = let (e,l) = mparse l in sparse' e l            (*summation/subtraction level parsing*)
  and sparse' e l = match l with
  |ADD::l -> let (e2,l) = mparse l in sparse' (Oapp(Add,e,e2)) l
  |SUB::l -> let (e2,l) = mparse l in sparse' (Oapp(Sub,e,e2)) l
  |l -> (e,l) 
  and mparse l = let (e,l) = aparse l in mparse' e l            (*multiplication level parsing*)
  and mparse' e l = match l with
  |MUL::l -> let (e2,l) = aparse l in aparse' (Oapp(Mul,e,e2)) l
  |l-> (e,l)
  and aparse l = let (e,l) = pparse l in aparse' e l            (*function application level parsing*)
  and aparse' e l = match l with
  |CON _ :: _ | VAR _ :: _ | LP :: _  -> 
    let (e2,l) = pparse l in aparse' (Fapp(e,e2)) l
  |l -> (e,l)
  and pparse l = match l with                                   (*parentheses & constant level parsing*)
    |CON(c)::l -> 
      begin match c with 
      |BCON(b) -> Con(Bcon(b)),l
      |ICON(i) -> Con(Icon(i)),l
      end
    |VAR(v)::l -> Var (v),l
    |LP::l -> let (e,l) = parse l in (e, verify RP l)
    |_ -> failwith "pparse: could not parse"
and tparse l = let (t,l) = ptparse l in tparse' t l             (*type parser*)
and tparse' t l = match l with                                  (*function type level parsing*)
  |ARR::l -> let (t2,l) = tparse l in (Arrow(t,t2),l)
  |[] -> failwith "tparse' : Arrow type missing t2"
  |_->ptparse l
and ptparse l = match l with                                    (*primitive type level parsing*)
  |BOOL::l -> Bool,l
  |INT::l -> Int,l
  |t::l-> tparse l
  |_-> failwith "ptparse: expected type TOKEN"

let testp1 = parse (lex str1)



let fst (a,b) = a;;

let checkstr s = check empty (fst(parse (lex s)));;
let evalstr s = eval empty (fst(parse (lex s)));;