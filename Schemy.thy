theory Schemy
  imports Main
begin

datatype var = Var string

type_synonym bool_exp = bool

type_synonym intexp = int

datatype exp =
    IntExp intexp
  | VarExp var
  | BoolExp bool_exp
  | Quote exp
  | And exp exp
  | Or exp exp
  | Eql exp exp
  | Less exp exp
  | Greater exp exp
  | Plus exp exp
  | Subtract exp exp
  | If exp exp exp
(* lambda "var list" exp *)

datatype cnd =
    Cnd2 exp exp
  | Cnd1 exp

datatype binding = Binding var exp


fun getVar :: "binding ⇒ var" where 
  "getVar (Binding v e) = v"

fun getExp :: "binding ⇒ exp" where 
  "getExp (Binding v e) = e"

fun getParams :: "binding list ⇒ var list" where
  "getParams [] = []"
| "getParams (bind # xs) = getVar bind # getParams xs"

fun getExps :: "binding list ⇒ exp list" where 
  "getExps [] = []"
| "getExps (bind # xs) = getExp bind # getExps xs"

type_synonym state = "var ⇒ exp"

fun eval :: "exp ⇒ state ⇒ exp" where
  "eval (IntExp n) _ = IntExp n"
| "eval (BoolExp b) _ = BoolExp b"
| "eval (Quote e) _ = e"
| "eval (VarExp v) s = s v"
| "eval (And e1 e2) s =
     (case (eval e1 s, eval e2 s) of
        (BoolExp True, BoolExp True) ⇒ BoolExp True
      | _ ⇒ BoolExp False)"
| "eval (Or e1 e2) s = 
     (case (eval e1 s, eval e2 s) of
        (BoolExp False, BoolExp False) ⇒ BoolExp False 
      | _ ⇒ BoolExp True)"
| "eval (Eql e1 e2) s =
     (case (eval e1 s, eval e2 s) of
        (IntExp n1, IntExp n2) ⇒ BoolExp (n1 = n2)
      | (BoolExp b1, BoolExp b2) ⇒ BoolExp (b1 = b2)
      | _ ⇒ BoolExp False)"
| "eval (Less e1 e2) s =
     (case (eval e1 s, eval e2 s) of
        (IntExp n1, IntExp n2) ⇒ BoolExp (n1 < n2)
      | _ ⇒ BoolExp False)"
| "eval (Greater e1 e2) s =
     (case (eval e1 s, eval e2 s) of
        (IntExp n1, IntExp n2) ⇒ BoolExp (n1 > n2)
      | _ ⇒ BoolExp False)"
| "eval (If cnd thn els) s =
     (case eval cnd s of 
        BoolExp True ⇒ eval thn s 
      | _ ⇒ eval els s)"
| "eval (Plus e1 e2) s =
     (case (eval e1 s, eval e2 s) of
        (IntExp n1, IntExp n2) ⇒ IntExp (n1 + n2)
      | _ ⇒ IntExp 0)"  
| "eval (Subtract e1 e2) s =
     (case (eval e1 s, eval e2 s) of
        (IntExp n1, IntExp n2) ⇒ IntExp (n1 - n2)
      | _ ⇒ IntExp 0)"  

fun desugar :: "exp ⇒ state ⇒ exp" where 
"desugar (And e1 e2) s =
eval (If e1 e2 (BoolExp False)) s"
| "desugar (Or e1 e2) s =
eval (If e1 (BoolExp True) e2) s"
| "desugar e s = e"


lemma "eval (desugar a s) s = eval a s"
  apply (induction a)
             apply (auto split: exp.split)
  done
end 