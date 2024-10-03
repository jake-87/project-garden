Require Import Nat.
Require Import String.
Require Import List.
Import ListNotations.

Inductive Ty : Type :=
| Bool : Ty
| Arrow : Ty -> Ty -> Ty.

Inductive Tm : Type :=
| Var : string -> Tm
| App : Tm -> Tm -> Tm
| Lam : string -> Ty -> Tm -> Tm
| Tru : Tm
| Fls : Tm
| Case : Tm -> Tm -> Tm -> Tm.

Fixpoint subst (x: string) (t1: Tm) (t2: Tm): Tm :=
  match t1 with
  | Var s => if String.eqb s x then t2 else t2
  | App a b => App (subst x a t2) (subst x b t2)
  | Lam s t e => if String.eqb s x then t1 else Lam s t (subst x e t2)
  | Tru | Fls => t1
  | Case a b c => Case (subst x a t2) (subst x b t2) (subst x c t2)
  end.

Inductive Step : Tm -> Tm -> Prop :=
| AppLam : forall a t e b, Step (App(Lam a t e) b) (subst a e b)
| App1 : forall a b c, Step a b -> Step (App a c) (App b c)
| App2 : forall a b c, Step b c -> Step (App a b) (App a c)
| Caset : forall a b, Step (Case Tru a b) a
| Casef : forall a b, Step (Case Fls a b) b
| Caser : forall a b c d, Step a b -> Step (Case a c d) (Case b c d).

Inductive MStep : Tm -> Tm -> Prop :=
| Refl : forall a, MStep a a
| Trans : forall a b c, Step a b -> MStep b c -> MStep a c.

Definition Ctx := list (string * Ty).

Inductive Has : Ctx -> Tm -> Ty -> Prop :=
| T_Var : forall c t s, In (s,t) c -> Has c (Var s) t
| T_Lam : forall c s e t t1,
    Has ((s,t) :: c) e t1 ->
    Has c (Lam s t e) (Arrow t t1)
| T_App : forall e e' t1 t2 c, Has c e (Arrow t1 t2) ->
                          Has c e' t1 ->
                          Has c (App e e') t2
| T_Tru : forall c, Has c Tru Bool
| T_Fls : forall c, Has c Fls Bool
| T_Case : forall a b c t1 d, Has c b Bool ->
                             Has c a t1 ->
                             Has c d t1 ->
                             Has c (Case b a d) t1.

Hint Constructors Has : core.

Require Import Coq.Program.Equality.


Lemma no_self_apply : not (exists S T, Has [] (Lam "x" S (App (Var "x") (Var "x"))) T).
Proof.
  unfold not.
  intros.
  destruct H as [S].
  destruct H as [T].
  inversion H.
  clear H1 H0 H3 H4.
  rewrite<- H2 in *.
  clear H2.
  inversion H5.
  clear H2 H0 H1 H4.
  inversion H3.
  clear e0 e' t2 c1 t3 s0 H1 H0 H4.
  destruct H2.
  - inversion H0.
    rewrite H2 in *.
    inversion H6.
    inversion H7.
    + inversion H9.
      clear H5 H3 c0 H6 H0 H2 c1 t2 H8 s0 H7 H4 H1 H7 H9 H.
      induction t0.
      * discriminate H11.
      * inversion H11.
        rewrite H1 in *.
        apply IHt0_1 in H0.
        apply H0.
    + destruct H9.
  - destruct H0.
Qed.

Lemma no_self_apply2 : not (exists S T, Has [] (Lam "x" S (App (Var "x") (Var "x"))) T).
Proof.
  intros [S [T H]].
  repeat dependent destruction H.
  dependent destruction H0; destruct H,H0; try easy.
  inversion H; inversion H0; subst; clear H H0.
  induction t; try easy. inversion H3. now subst.
Qed.
