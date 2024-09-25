Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Bool.
Require Import Logic.

Inductive ty : Type :=
| Ty_Bool : ty
| Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
| tm_var : nat -> tm
| tm_app : tm -> tm -> tm
| tm_abs : nat -> ty -> tm -> tm
| tm_true : tm
| tm_false : tm
| tm_if : tm -> tm -> tm -> tm.

Hint Constructors tm : core.


Inductive value : tm -> Prop :=
| V_abs : forall a b c, value (tm_abs a b c)
| V_true : value (tm_true)
| V_false : value (tm_false).

Hint Constructors value : core.


Fixpoint subst (n : nat) (s : tm) (t : tm): tm :=
  match s with
  | tm_var v => if Nat.eqb v n then t else s
  | tm_app a b => tm_app (subst n a t) (subst n b t)
  | tm_abs v t' b => if Nat.eqb v n then s else tm_abs v t' (subst n b t)
  | tm_if a b c => tm_if (subst n a t) (subst n b t) (subst n c t)
  | _ => s
  end.

Inductive step : tm -> tm -> Prop :=
| Step_absapp : forall x t a b, step (tm_app (tm_abs x t a) b) (subst x b a)
| Step_app1 : forall a b c, step a b -> step (tm_app a c) (tm_app b c)
| Step_app2 : forall a b c, step c b -> step (tm_app a c) (tm_app a b)
| Step_if1 : forall a b, step (tm_if tm_true a b) a
| Step_if2 : forall a b, step (tm_if tm_false a b) b
| Step_if : forall a b c d, step c d -> step (tm_if c a b) (tm_if d a b).

Inductive mstep : tm -> tm -> Prop :=
| Here : forall a b, step a b -> mstep a b
| There : forall a b c, step a b -> step b c -> mstep a c.

Definition Ctx := list (nat * ty).

Reserved Notation "Gamma '⊢' t '∈' T" (at level 40).

Inductive has_type : Ctx -> tm -> ty -> Prop :=
| T_Var : forall G v t, In (v, t) G -> has_type G (tm_var v) t
| T_Abs : forall G v T1 T2 b, ((v, T2) :: G) ⊢ b ∈ T1 -> G ⊢ tm_abs v T2 b ∈ Ty_Arrow T2 T1
| T_App : forall G a b T1 T2, G ⊢ a ∈ Ty_Arrow T1 T2 -> G ⊢ b ∈ T1 -> G ⊢ tm_app a b ∈ T2
| T_True : forall G, G ⊢ tm_true ∈ Ty_Bool
| T_False : forall G, G ⊢ tm_false ∈ Ty_Bool
| T_If : forall G a b c t1,
      G ⊢ a ∈ Ty_Bool
      -> G ⊢ b ∈ t1
      -> G ⊢ c ∈ t1
      -> G ⊢ tm_if a b c ∈ t1
where "Gamma '⊢' t '∈' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Notation "¬ A" := (not A) (at level 40).

Theorem canonical_abs : forall t T1 T2, [] ⊢ t ∈ Ty_Arrow T1 T2 -> value t ->
                                    exists v b, t = tm_abs v T1 b. 
Proof.
  intros.
  destruct H0; auto.  
  - exists a.
    exists c.
    inversion H; subst.    
    reflexivity.
  - inversion H.
  - inversion H.
Qed.
    
Theorem canonical_bool : forall t, [] ⊢ t ∈ Ty_Bool -> value t ->
                              t = tm_true \/ t = tm_false.
Proof.
  intros.

  destruct H0; auto.
  inversion H.
Qed.  


Theorem Progress : forall t T, [] ⊢ t ∈ T -> value t \/ exists t', step t t'.
Proof.
  intros.
  remember [] as G.
  induction H; subst; auto.
  - destruct H.
  - assert (IH1 := IHhas_type1 eq_refl); clear IHhas_type1.
    assert (IH2 := IHhas_type2 eq_refl); clear IHhas_type2.
    destruct IH1.
    + eapply canonical_abs in H; auto.
      destruct H. destruct H.
      rewrite H.
      right.
      exists (subst x b x0); apply Step_absapp.
    + destruct H1.
      right.
      exists (tm_app x b).
      now apply Step_app1.
  - assert (IH1 := IHhas_type1 eq_refl); clear IHhas_type1.
    assert (IH2 := IHhas_type2 eq_refl); clear IHhas_type2.
    assert (IH3 := IHhas_type3 eq_refl); clear IHhas_type3.
    destruct IH1.
    + right.
      eapply canonical_bool in H; auto.
      destruct H; subst.
      * exists b.
        apply Step_if1.
      * exists c.
        apply Step_if2.
    + right.
      destruct H2.
      exists (tm_if x b c).
      now apply Step_if.
Qed.

Theorem in_uniq : forall A (a b : A), In a [b] -> a = b.
Proof.
  intros.
  induction H.
  easy.
  induction H; easy.
Qed.  

Theorem subst_preserves : forall t T a A G x, ((x, A) :: G) ⊢ t ∈ T
                                       -> [] ⊢ a ∈ A
                                       -> G ⊢ subst x t a ∈ T. 
Proof.
  intros.
  generalize dependent G.
  generalize dependent T.
  induction t; intros T G H.
  - destruct (PeanoNat.Nat.eqb_spec x n).
    + rewrite e. simpl. rewrite PeanoNat.Nat.eqb_refl.
      rewrite e in H.
      
      
Theorem Preservation : forall x t T, [] ⊢ t ∈ T -> step t x -> [] ⊢ x ∈ T.
Proof with eauto.
  intros.
  induction H0.
  - 
