theory Schemy
  imports Main
begin                  

datatype var = Var string

datatype exp =
    IntExp int
  | VarExp var
  | BoolExp bool
  | Quote exp
  | And exp exp
  | Or exp exp
  | Eql exp exp
  | Less exp exp
  | Greater exp exp
  | Plus exp exp
  | Subtract exp exp
  | If exp exp exp 

(* instruction datatype taken from "concrete semantics" 
i.e., http://concrete-semantics.org/concrete-semantics.pdf *)
datatype instruction =
   LOADI int 
   | LOAD string 
   | ADD 
   | STORE string
   | JMP int 
   | JMPLESS int 
   | JMPGE int   

fun isBool :: "exp  ⇒ bool" where
"isBool (And e1 e2) = True"
| "isBool (Or e1 e2) = True" 
| "isBool (BoolExp e1) = True"
| "isBool (Eql e1 e2) = True"
| "isBool (Less e1 e2) = True" 
| "isBool (Greater e1 e2) = True"
| "isBool _ = False"
                    
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
(if (isBool e1) & (isBool e2) 
then
case (eval e1 s, eval e2 s) of
(BoolExp True, BoolExp True) ⇒ BoolExp True
| _ ⇒ BoolExp False
else e2)"    
| "eval (Or e1 e2) s =               
     (case (eval e1 s, eval e2 s) of
        (BoolExp False, BoolExp False) ⇒ BoolExp False 
      | (IntExp n1, IntExp n2) ⇒ IntExp n1
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
(if (isBool cnd)
then
     (case eval cnd s of             
        BoolExp True ⇒ eval thn s 
      | _ ⇒ eval els s)
else eval thn s)"            
| "eval (Plus e1 e2) s =
     (case (eval e1 s, eval e2 s) of
        (IntExp n1, IntExp n2) ⇒ IntExp (n1 + n2)
      | _ ⇒ IntExp 0)"  
| "eval (Subtract e1 e2) s =
     (case (eval e1 s, eval e2 s) of
        (IntExp n1, IntExp n2) ⇒ IntExp (n1 - n2)
      | _ ⇒ IntExp 0)"  

fun desugar :: "exp ⇒ exp" where 
"desugar (And e1 e2) = 
(if (isBool e1) & (isBool e2) 
then If e1 e2 (BoolExp False)
else e2)"
| "desugar (Or e1 e2)  = If e1 (BoolExp True) e2"
| "desugar (If cnd thn els) = If (desugar cnd) (desugar thn) (desugar els)"
| "desugar (Plus e1 e2) = Plus (desugar e1) (desugar e2)"
| "desugar (Subtract e1 e2) = Subtract (desugar e1) (desugar e2)"
| "desugar (Eql e1 e2) = Eql (desugar e1) (desugar e2)"
| "desugar (Less e1 e2) = Less (desugar e1) (desugar e2)"
| "desugar (Greater e1 e2) = Greater (desugar e1) (desugar e2)"
| "desugar (Quote e) = Quote (desugar e)"
| "desugar (VarExp v) = VarExp v"            
| "desugar (IntExp n) = IntExp n"
| "desugar (BoolExp b) = BoolExp b"

lemma var1: "eval (desugar (VarExp a)) s = eval (VarExp a) s"
  apply (induction a)
  apply(auto) 

lemma bool1: "eval (desugar (BoolExp a)) s = eval (BoolExp a) s"
  apply(induction a)
   apply(auto)  

lemma desugar1: "eval (desugar (Quote a)) s = eval (Quote a) s"
  apply(induction a)
             apply (auto)       

theorem desugarer: "eval (desugar a) s = eval a s" 
  apply (induction a)
             apply (simp)






                             
                




