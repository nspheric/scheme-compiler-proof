theory Anf
  imports Main
begin

datatype lam =
  IntE int
  | VarE string 
  | BoolE bool
  | Quote lam
  | QuasiQuote lam
  | PrimE string lam lam
  | Lambda "string list" lam
  | Application "lam list"
  | Let string lam lam
  | LetStar string lam lam
  | Begin "lam list"
  | If lam lam lam
  | When lam lam
  | Unless lam lam

datatype core =
  CInt int
  | CVar string
  | CBool bool
  | CQuote core
  | CIf core core core
  | CPrim string core core
  | CLambda "string list" core
  | CApp "core list"

type_synonym vname = string

datatype atm =
  IntExp int
  | Var vname

datatype abool =
  Bool bool

datatype exp =
   Plus atm atm
  | Subtract atm atm
  (*| Let vname exp exp *)
  | Atomic atm
  | Void

type_synonym fvs = "string list"

datatype cmpexp =
   Less atm atm
   | Greater atm atm
   | And abool abool
   | Or abool abool
   | Not abool

datatype cifexp =
   If abool exp exp
  | When abool exp
  | Unless abool exp
 

type_synonym astate = "vname \<Rightarrow> int "

fun member :: "string \<Rightarrow> string list \<Rightarrow> bool" where
  "member v [] = False"
| "member v (x # xs) = (if v = x then True else member v xs)"

lemma mem: "member v (x # xs) = (if v = x then True else member v xs)"
  apply (induction xs)
   apply (auto)
  done

fun freevars:: "exp  \<Rightarrow> string list \<Rightarrow> string list" where 
"freevars (Atomic (Var v1)) vars  =
(if (\<not> member v1 vars)
then v1 # []
else [])"
| "freevars (Atomic (IntExp e1)) vars  = []"
| "freevars (Plus (IntExp e1) (Var e2)) vars =
(if member e2 vars then [] else e2 # [])"
| "freevars (Plus (Var v1) (IntExp e1)) vars =
(if member v1 vars then [] else v1 # [])"
| "freevars (Plus (Var v1) (Var v2)) vars =
(if (\<not> member v1 vars) \<and> (\<not> member v2 vars)
then v1 # v2 # []
else if (\<not> member v1 vars) \<and> (member v2 vars)
then v1 # [] else [])"
| "freevars (Plus (IntExp e1) (IntExp e2)) vars = []"
| "freevars (Subtract (IntExp e1) (Var e2)) vars =
(if member e2 vars then [] else e2 # [])"
| "freevars (Subtract (Var v1) (IntExp e1)) vars =
(if member v1 vars then [] else v1 # [])"
| "freevars (Subtract (Var v1) (Var v2)) vars =
(if (\<not> member v1 vars) \<and> (\<not> member v2 vars)
then v1 # v2 # []
else if (\<not> member v1 vars) \<and> (member v2 vars)
then v1 # [] else [])"
| "freevars (Subtract (IntExp e1) (IntExp e2)) vars = []"
| "freevars Void vars = []"

fun freevarslam :: "alambda \<Rightarrow> string list \<Rightarrow> string list" where
 "freevarslam (Lambda params exp) vars =
freevars exp vars"
(*| "freevarslam (Closure arity name fvs) vars = []"*)

fun booleval :: "abool \<Rightarrow> astate \<Rightarrow> bool" where 
"booleval (Bool b) s = b"

fun aeval :: "atm \<Rightarrow> astate \<Rightarrow> int " where 
"aeval (IntExp e) s = e"
| "aeval (Var v) s = s v"


fun eval :: "exp \<Rightarrow> astate \<Rightarrow> int" where
"eval (Atomic (IntExp e1)) s =  e1"
| "eval (Atomic (Var e1)) s = s e1"
| "eval (Plus e1 e2) s = aeval e1 s + aeval e2 s"
| "eval (Subtract e1 e2) s = aeval e1 s - aeval e2 s"
| "eval Void s = 0"

fun slen :: "string list \<Rightarrow> int \<Rightarrow> int" where 
"slen [] _ = 0"
| "slen (x # xs) n = 1 + slen xs n"

lemma slen: "slen (x # xs) n = 1 + slen xs n"
  apply (induction xs)
   apply (auto)
  done

fun lameval :: "alambda \<Rightarrow> astate \<Rightarrow>  alambda" where 
"lameval (Lambda vars exp) s  = (Lambda vars exp)"
| "lameval def s = def"

fun beval :: "cmpexp \<Rightarrow> astate \<Rightarrow> bool" where
 "beval (Less e1 e2) s =
(aeval e1 s < aeval e2 s)"
| "beval (Greater e1 e2) s =
(aeval e1 s > aeval e2 s)"
| "beval (And e1 e2) s =
(booleval e1 s \<and> booleval e2 s)"
| "beval (Or e1 e2) s =
(booleval e1 s \<or>  booleval e2 s)"
| "beval (Not e1) s =
(\<not> booleval e1 s)"

fun ifeval :: "cifexp \<Rightarrow> astate \<Rightarrow> int" where 
 "ifeval (If cnd thn els) s =
(case cnd of (Bool True) => eval thn s | _ => eval els s)"
| "ifeval (When cnd thn) s =
(case cnd of (Bool True) \<Rightarrow> eval thn s | _ \<Rightarrow> eval Void s)"
| "ifeval (Unless cnd thn) s =
(case cnd of (Bool False) \<Rightarrow> eval thn s | _ \<Rightarrow> eval Void s)"

fun desugarif :: "cifexp \<Rightarrow> cifexp" where 
"desugarif (When cnd thn) = (If cnd thn Void)"
| "desugarif (Unless cnd thn) = (If cnd Void thn)"
| "desugarif (If cnd thn els) = (If cnd thn els)"

lemma ifdesugarer: "ifeval (desugarif e) s = ifeval e s"
  apply (induction e)
    apply(auto)
  done

datatype cifc = CIfC abool exp exp

inductive big_step :: "cifc \<times> astate \<Rightarrow> astate \<Rightarrow> bool" (infix "\<Rightarrow>" 55) where
IfTrue:
  "\<lbrakk> booleval b s = True; (c1, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |
IfFalse:
  "\<lbrakk> booleval b s = False; (c2, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t"


datatype reg = RDI | RSI | RDX | RCX | R8 | R9 | RAX 

datatype inst =
  Loadi int
  | Load string
  | Addq 

fun ecomp :: "exp \<Rightarrow> inst list" where 
"ecomp (Atomic (IntExp e1)) = [Loadi e1]"
| "ecomp (Atomic (Var e1)) =  [Load e1]"
| "ecomp (Plus (IntExp e1) (IntExp e2)) = 
(let imm1 = [Loadi e1] in
 let imm2 = [Loadi e2] in
 imm1 @ imm2 @ [Addq])"
| "ecomp (Plus (IntExp e1) (Var e2)) =
(let imm1 = [Loadi e1] in
 let  stk = [Load e2] in
 imm1  @ stk  @ [Addq])"
| "ecomp (Plus (Var e1) (IntExp e2)) =
(let imm1 = [Loadi e2] in
 let  stk = [Load e1] in
 imm1 @  stk @ [Addq])"
| "ecomp (Plus (Var e1) (Var e2)) =
(let stk1 = [Load e1] in
 let  stk2 = [Load e2] in
 stk1 @  stk2  @ [Addq])"
| "ecomp (Subtract (IntExp e1) (IntExp e2)) = 
(let imm1 = [Loadi e1] in
 let imm2 = [Loadi e2] in
 imm1 @  imm2 @ [Addq])"
| "ecomp (Subtract (IntExp e1) (Var e2)) =
(let imm1 = [Loadi e1] in
 let  stk = [Load e2] in
 imm1  @ stk @ [Addq])"
| "ecomp (Subtract (Var e1) (IntExp e2)) =
(let imm1 = [Loadi e2] in
 let  stk = [Load e1] in
 imm1  @ stk  @ [Addq])"
| "ecomp (Subtract (Var e1) (Var e2)) =
(let stk1 = [Load e1] in
 let  stk2 = [Load e2] in
 stk1 @  stk2  @ [Addq])"
| "ecomp Void = [Loadi 0]"

type_synonym stack = "int list"
type_synonym config = "int \<times> astate \<times> stack"

fun iexec :: "inst \<Rightarrow> config \<Rightarrow> config" where 
"iexec (Loadi n) (i, s, stk) = (i + 1, s, n # stk)"
| "iexec (Load n) (i, s, stk) = (i + 1, s, s n # stk)"
| "iexec Addq (i, s, stk) = 
(let hd2 = hd (tl stk) in
 let tl2 = tl (tl stk) in
   (i + 1, s, (hd2 + hd stk) # tl2))" 


fun exec :: "inst list \<Rightarrow> config \<Rightarrow> int" where 
"exec [] (_, _, stk) = 
(if stk = [] then 0 else hd stk)"
| "exec (x # xs) con =
exec xs (iexec x con)"
   
fun compile :: "exp \<Rightarrow> config \<Rightarrow> int" where 
"compile e con = 
exec (ecomp e) con"

(* nice  exercise here *)
lemma ec2: "exec (ecomp (Plus (IntExp e) e2)) con = e + aval e2 s"
  apply (induction e2)
  apply (auto)
lemma ec: "exec (ecomp (Plus e e2)) con = aeval e s + aeval e2 s"
  apply (induction e)
  apply (auto)
lemma ecomp_correctness: "compile e con = eval e s"
  apply(induction e)
  apply (auto)


fun getmovs' :: "reg list \<Rightarrow> vname list \<Rightarrow> inst list" where
"getmovs' rgs [] = []"
| "getmovs' [] args = []"
| "getmovs' (rg # rgs) (arg # args) =
[Movq  (Register rg) (Stack arg)] @ getmovs' rgs args"

fun getmovs :: "string list \<Rightarrow> inst list" where 
"getmovs vars =
(let regs = [RDI, RSI, RDX, RCX, R8, R9] in
   getmovs' regs vars)"

end