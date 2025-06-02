theory Schemy
  imports Main
begin

type_synonym vname = string

datatype exp =
    IntExp int
  | VarExp vname
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
  | Unless exp exp 
  | When exp exp  
(* | Begin "exp list" *)
(* | LetStar "binding list" exp *)
(* | LetRec "binding list" exp *)
(* | Let "binding list" exp *)
(* | Lambda "var list" exp *)
(* | Application "exp list" *)

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

fun isNotBool :: "exp ⇒ bool" where 
"isNotBool (IntExp n) = True"
| "isNotBool (VarExp n) = True"
| "isNotBool (Quote q) = True"
| "isNotBool _ = False"

datatype cnd =
    Cnd2 exp exp       
  | Cnd1 exp

datatype binding = Binding vname exp

fun getVar :: "binding ⇒ vname" where 
  "getVar (Binding v e) = v"

fun getExp :: "binding ⇒ exp" where 
  "getExp (Binding v e) = e"

fun getParams :: "binding list ⇒ vname list" where
  "getParams [] = []"
| "getParams (bind # xs) = getVar bind # getParams xs"

fun getExps :: "binding list ⇒ exp list" where 
  "getExps [] = []"
| "getExps (bind # xs) = getExp bind # getExps xs"


fun isTrue :: "bool ⇒ bool" where 
"isTrue True = True"
| "isTrue False = False"

fun isFalse :: "bool ⇒ bool" where 
"isFalse False = True"
| "isFalse True = False"

fun isAtomic :: "exp ⇒ bool" where
"isAtomic (IntExp n) = True"
| "isAtomic (VarExp v) = True"
| "isAtomic (BoolExp b) = True"
| "isAtomic _ = False"

fun isBoolean :: "exp ⇒ bool" where
"isBoolean (BoolExp b) = True"
| "isBoolean _ = False"

(* informal semantics of "Scheme" via an interpreter *)
type_synonym state = "vname ⇒ exp"
fun eval :: "exp ⇒ state ⇒ exp" where
  "eval (IntExp n) _ = IntExp n"
| "eval (BoolExp b) _ = BoolExp b"
| "eval (Quote e) _ = e"
| "eval (VarExp v) s =  s v"
| "eval (And e1 e2) s = 
(case (e1, e2) of 
  (BoolExp b1, BoolExp b2) ⇒
if isTrue b1 & isTrue b2 
then BoolExp True
else BoolExp False
  | (_, _) ⇒
if isNotBool e1 | isNotBool e2 
then e2
else eval (And (eval e1 s) (eval e2 s)) s)"
| "eval (Or e1 e2) s = 
(case (e1, e2) of
   (BoolExp b1, BoolExp b2) ⇒ 
if isFalse b1 & isFalse b2 
then BoolExp False 
else BoolExp True
  | (_, _) ⇒ 
if isNotBool e1 | isNotBool e2 
then e1 
else eval (Or (eval e1 s) (eval e2 s)) s)"                            
| "eval (Eql e1 e2) s = 
(if isAtomic e1 & isAtomic e2
then BoolExp (e1 = e2)
else eval (Eql (eval e1 s) (eval e2 s)) s)"
| "eval (Less e1 e2) s =
(case (e1,e2) of
  (IntExp e3, IntExp e4) ⇒
    (BoolExp (e3 < e4))
  | (_, _) ⇒ eval (Less (eval e1 s) (eval e2 s)) s)"
| "eval (Greater e1 e2) s =             
(case (e1, e2) of 
  (IntExp e3, IntExp e4) ⇒
   BoolExp (e3 > e4)
  | (_, _) ⇒ eval (Greater (eval e1 s) (eval e2 s)) s)"
| "eval (When cnd thn) s = 
(case (eval cnd s) of 
  (BoolExp True) ⇒ eval thn s
  | _ ⇒ 
if isNotBool cnd 
then (eval thn s)
else BoolExp False)" 
| "eval (Unless cnd thn) s =
(case (eval cnd s) of 
   (BoolExp False) ⇒ eval thn s
   | _ ⇒ BoolExp False)"                  
| "eval (If cnd thn els) s = 
(case eval cnd s of             
        BoolExp True ⇒ eval thn s 
      | _ ⇒ eval els s)"            
| "eval (Plus e1 e2) s = 
Plus (eval e1 s) (eval e2 s)"
| "eval (Subtract e1 e2) s =
Subtract (eval e1 s) (eval e2 s)"

fun desugar :: "exp ⇒ exp" where 
"desugar (And e1 e2) = 
(if (isBool e1) & (isBool e2) 
then If e1 e2 (BoolExp False)        
else e2)"
| "desugar (Or e1 e2) = If e1 (BoolExp True) e2"
| "desugar (When cnd thn) = If cnd thn (BoolExp False)"
| "desugar (Unless cnd thn) = If cnd (BoolExp False) thn"
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

(* Now, we need to prove that the desugarer preserves the semantics of
`eval`. We need to prove that the IRs preserve the semantics as well. And then prove 
that the code generator, via the stack machine semantics, preserve the semantics. 
At least this is my intuition.

Formally, you model the semantics using big or small step operational semantics.
Operational semantics and ASTs are the primary ways to model programs as mathematical objects. 
We can then prove properties of such programs.

In the dragon book, second edition, it says that correctness is crucial
for compilers. And it happens that one mathematical property of compilers is correctness.
*)

theorem desugarer: "eval (desugar a) s = eval a s"               
  apply (induction a)    
  apply (simp)
  done

end



                             
                




