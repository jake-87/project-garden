theory "tycheck-correct"
  imports Main
begin

datatype bop = Eq | Lt

datatype iop = Add | Sub 

datatype type =
    TyInt
  | TyBool
  | TyFun type type 

datatype lang =
  Var string
  | Num int
  | Bool bool
  | BOp bop lang lang
  | IOp iop lang lang
  | ITE lang lang lang
  | Lam string type lang
  | App lang lang

datatype con =
  CNil
  | CCons con string type

fun lookup :: "con \<Rightarrow> string \<Rightarrow> type option" where
"lookup CNil s = None"
| "lookup (CCons rst nm t) s = (if nm = s then Some t else lookup rst s)"

inductive isof :: "con \<Rightarrow> lang \<Rightarrow> type \<Rightarrow> bool" where
isof_var[simp]: "lookup G nm = Some t \<Longrightarrow> isof G (Var nm) t"
| isof_num[simp]: "isof G (Num i) TyInt"
| isof_bool[simp]: "isof G (Bool b) TyBool"
| isof_iop[simp]: "isof G a TyInt \<Longrightarrow> isof G b TyInt \<Longrightarrow> isof G (IOp f a b) TyInt"
| isof_bop[simp]: "isof G a TyInt \<Longrightarrow> isof G b TyInt \<Longrightarrow> isof G (BOp f a b) TyBool"
| isof_ite[simp]: "isof G a TyBool \<Longrightarrow> isof G b t \<Longrightarrow> isof G c t \<Longrightarrow> isof G (ITE a b c) t"
| isof_lam: "isof (CCons G nm ty) a ret \<Longrightarrow> isof G (Lam nm ty a) (TyFun ty ret)"
| isof_app: "isof G f (TyFun t1 t2) \<Longrightarrow> isof G x t1 \<Longrightarrow> isof G (App f x) t2"

fun tycheck :: "con \<Rightarrow> lang \<Rightarrow> type option" where
"tycheck G (Var nm) = lookup G nm"
| "tycheck G (Num i) = Some TyInt"
| "tycheck G (Bool b) = Some TyBool"
| "tycheck G (IOp _ a b) = (case (tycheck G a, tycheck G b) of
 (Some TyInt, Some TyInt) \<Rightarrow> Some TyInt
| (_, _) \<Rightarrow> None)"
| "tycheck G (BOp _ a b) = (case (tycheck G a, tycheck G b) of
 (Some TyInt, Some TyInt) \<Rightarrow> Some TyBool
| (_, _) \<Rightarrow> None)"
| "tycheck G (ITE a b c) = (case tycheck G a of
Some TyBool \<Rightarrow> (let t = tycheck G b in if (t = tycheck G c) then t else None)
| _ \<Rightarrow> None)"
| "tycheck G (App f x) = (case tycheck G f of
Some (TyFun t1 t2) \<Rightarrow> if (Some t1 = tycheck G x) then Some t2 else None
| _ \<Rightarrow> None)"
| "tycheck G (Lam nm ty bd) = (case tycheck (CCons G nm ty) bd of
Some t2 \<Rightarrow> Some (TyFun ty t2)
| None \<Rightarrow> None)"

lemma isof_imp_tycheck: "isof G l t \<Longrightarrow> tycheck G l = Some t"
  apply (induct rule: isof.induct, simp+)
  done

lemma tycheck_imp_isof: "tycheck G l = Some t \<Longrightarrow> isof G l t"
  apply (induct arbitrary: t rule: tycheck.induct)
         apply simp+
(* IOp *)
      apply (case_tac "tycheck G a", force)
      apply (case_tac "tycheck G b")
       apply (case_tac aa, simp+)
      apply (case_tac aa)
        apply (case_tac ab, force+)
(* BOp *)
     apply (case_tac "tycheck G a", force)
     apply (case_tac "tycheck G b")
      apply (case_tac aa, simp+)
     apply (case_tac aa)
       apply (case_tac ab, simp+)
(* ITE *)
    apply (case_tac "tycheck G a", force)
    apply (case_tac "tycheck G b")
     apply (case_tac aa, simp+)
    apply (case_tac aa, force)
     apply (case_tac "tycheck G c", simp)
     apply (case_tac "ab = ac")
      apply simp+
(* App *)
   apply (case_tac "tycheck G f", force)
   apply (case_tac a, force+)
   apply (case_tac "tycheck G x", force)
   apply (case_tac "x31 = aa")
  apply (simp add: isof_app)+
(* Lam *)
  apply (case_tac t)
    apply (case_tac "tycheck (CCons G nm ty) bd", force+)
   apply (case_tac "tycheck (CCons G nm ty) bd", force+)
  apply (case_tac "tycheck (CCons G nm ty) bd", (simp add: isof_lam)+)
  done

lemma tycheck_isof_equiv: "isof G l t = (tycheck G l = Some t)"
  using tycheck_imp_isof isof_imp_tycheck by blast

end