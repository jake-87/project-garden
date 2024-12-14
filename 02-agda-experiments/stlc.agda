import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat 
open import Data.Nat.Properties 
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Fin using (Fin; fromℕ; toℕ; fromℕ<)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product using (Σ-syntax; ∃-syntax)
open import Relation.Nullary using (Dec; yes; no; does; proof; _because_; ofʸ; ofⁿ)
open import Data.List using (List; _++_; _∷_; []; [_]; map)
open import Data.List.Properties using (≡-dec)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)

import Data.List.Membership.DecPropositional as DecPropMembership
open DecPropMembership Data.Nat._≟_

open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂) 

infixr 6 _⇒_

data Type : Set where
  Nat : Type
  _⇒_ : Type → Type → Type

infixl 10 _,,_

data Con : Set where
  ∅ : Con
  _,,_ : Con → Type → Con

infix 5 _∋_

data _∋_ : Con → Type → Set where
  here∋ : ∀ {Γ x} → Γ ,, x ∋ x
  there∋ : ∀ {Γ x y} →
           Γ ∋ x →
           Γ ,, y ∋ x

infix 4 _⊢_
infixl 8 _·_
infixr 8 `s_
infixr 8 μ_
infixr 8 ƛ_

data _⊢_ : Con → Type → Set where
  `_ : ∀ {Γ x} →
       Γ ∋ x →
       Γ ⊢ x
  ƛ_ : ∀ {Γ x y} →
       Γ ,, y ⊢ x →
       Γ ⊢ y ⇒ x
  _·_ : ∀ {Γ x y} →
       Γ ⊢ x ⇒ y →
       Γ ⊢ x →
       Γ ⊢ y
  `z : ∀ {Γ} → Γ ⊢ Nat
  `s_ : ∀ {Γ} →
       Γ ⊢ Nat →
       Γ ⊢ Nat
  Case : ∀ {Γ A} →
       Γ ⊢ Nat →
       Γ ⊢ A →
       Γ ,, Nat ⊢ A →
       Γ ⊢ A
  μ_ : ∀ {Γ A} →
       Γ ,, A ⊢ A →
       Γ ⊢ A

length : Con → ℕ
length ∅ = 0
length (Γ ,, x) = 1 + length Γ

lookup : {Γ : Con} → {n : ℕ} → (p : n < length Γ) → Type
lookup {Γ ,, x} {zero} (s≤s z≤n) = x
lookup {Γ ,, x} {suc n} (s≤s p) = lookup {Γ} {n} p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup {Γ} {n} p
count {Γ ,, x} {zero} (s≤s z≤n) = here∋
count {Γ ,, x} {suc n} (s≤s p) = there∋ (count p)

#_ : ∀ {Γ} → (n : ℕ) →
       {n∈Γ : True (suc n ≤? length Γ)} → 
       Γ ⊢ lookup {Γ} (toWitness n∈Γ)
#_ n {n∈Γ} = ` (count (toWitness n∈Γ))

two : ∀ {Γ} → Γ ⊢ Nat
two = `s `s `z

plus : ∀ {Γ} → Γ ⊢ Nat ⇒ Nat ⇒ Nat
plus = μ ƛ ƛ (Case (# 1) (# 0) (`s (# 3 · # 0 · # 1)))

2+2 : ∀ {Γ} → Γ ⊢ Nat
2+2 = plus · two · two

ext : ∀ {Γ Δ} →
      (∀ {A} → Γ ∋ A → Δ ∋ A) →
      (∀ {A B} → Γ ,, B ∋ A → Δ ,, B ∋ A)
ext r here∋ = here∋
ext r (there∋ p) = there∋ (r p)

rename : ∀ {Γ Δ} →
         (∀ {A} → Γ ∋ A → Δ ∋ A) →
         (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename r (` x) = ` r x
rename r (ƛ p) = ƛ rename (ext r) p
rename r (p₁ · p₂) = rename r p₁ · rename r p₂
rename r `z = `z
rename r (`s p) = `s rename r p
rename r (Case c z s) = Case (rename r c) (rename r z) (rename (ext r) s)
rename r (μ p) = μ rename (ext r) p

up : ∀ {Γ x y} → Γ ⊢ x → Γ ,, y ⊢ x
up = rename there∋

exts : ∀ {Γ Δ} →
       (∀ {A} → Γ ∋ A → Δ ⊢ A) →
       (∀ {A B} → Γ ,, B ∋ A → Δ ,, B ⊢ A)
exts r here∋ = ` here∋
exts r (there∋ p) = up (r p)

subst : ∀ {Γ Δ} →
       (∀ {A} → Γ ∋ A → Δ ⊢ A) →
       (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst r (` x) = r x
subst r (ƛ p) = ƛ subst (exts r) p
subst r (p₁ · p₂) = subst r p₁ · subst r p₂
subst r `z = `z
subst r (`s p) = `s (subst r p)
subst r (Case c z s) = Case (subst r c) (subst r z) (subst (exts r) s)
subst r (μ p) = μ (subst (exts r) p)

_s[_] : ∀ {Γ x y} →
       Γ ,, x ⊢ y →
       Γ ⊢ x →
       Γ ⊢ y
_s[_] {Γ} {x} {y} ex ⊢x = subst {Γ ,, x} {Γ} σ {y} ex
  where
    σ : ∀ {A} → Γ ,, x ∋ A → Γ ⊢ A
    σ here∋ = ⊢x
    σ (there∋ x) = ` x

infixl 2 _~>_
data _~>_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where
     ·r : ∀ {Γ T₁ T₂} {A B : Γ ⊢ T₁} {C : Γ ⊢ T₁ ⇒ T₂} →
        A ~> B →
        C · A ~> C · B
     ·l : ∀ {Γ T₁ T₂} {A B : Γ ⊢ T₁ ⇒ T₂} {C : Γ ⊢ T₁} →
        A ~> B →
        A · C ~> B · C
     ƛ-sub : ∀ {Γ A B} {N : Γ ,, B ⊢ A} {M : Γ ⊢ B} →
        (ƛ N) · M ~> N s[ M ]
     `s-in : ∀ {Γ} {A B : Γ ⊢ Nat} →
        A ~> B →
        `s A ~> `s B
     Case-in : ∀ {Γ A} {C C' : Γ ⊢ Nat} {Z : Γ ⊢ A} {S : Γ ,, Nat ⊢ A} →
        C ~> C' →
        Case C Z S ~> Case C' Z S
     Case-z : ∀ {Γ A} {Z : Γ ⊢ A} {S : Γ ,, Nat ⊢ A} →
        Case `z Z S ~> Z
     Case-s : ∀ {Γ A} {C : Γ ⊢ Nat} {Z : Γ ⊢ A} {S : Γ ,, Nat ⊢ A} →
        Case (`s C) Z S ~> S s[ C ]
     μ-μ : ∀ {Γ A} {M : Γ ,, A ⊢ A} →
        μ M ~> M s[ μ M ]

infixr 9 _trans⟨_⟩_
infixr 12 _~>*_

data _~>*_ {Γ A} : Γ ⊢ A → Γ ⊢ A → Set where
     end : ∀ {M : Γ ⊢ A} →
           M ~>* M
     trans : (L : Γ ⊢ A) {L' L''  : Γ ⊢ A} →
           L ~> L' →
           L' ~>* L'' →
           L ~>* L''

pattern _trans⟨_⟩_ a b c = trans a b c

ONE : ∀ {Γ} → Γ ⊢ Nat
ONE = `s `z
TWO : ∀ {Γ} → Γ ⊢ Nat
TWO = `s `s `z
1+1=2 : (plus · ONE · ONE) ~>* TWO
1+1=2 = (plus {∅} · ONE · ONE)
        trans⟨ ·l (·l μ-μ) ⟩
        ((ƛ ƛ Case (# 1) (# 0) (`s (plus · (# 0) · (# 1)))) · ONE · ONE)
        trans⟨ ·l ƛ-sub ⟩
        (((ƛ Case ONE (# 0) (`s (plus · (# 0) · (# 1))))) · ONE)
        trans⟨ ƛ-sub ⟩
        (Case ONE ONE (`s (plus · (# 0) · ONE)))
        trans⟨ Case-s ⟩
        ((`s (plus · `z · ONE)))
        trans⟨ `s-in (·l (·l μ-μ)) ⟩
        (`s
          ((ƛ ƛ Case (# 1) (# 0) (`s (plus · (# 0) · (# 1)))) · `z · ONE))
        trans⟨ `s-in (·l ƛ-sub) ⟩
        (`s
          (((ƛ Case `z (# 0) (`s (plus · (# 0) · (# 1))))) · ONE))
        trans⟨ `s-in ƛ-sub ⟩
        (`s (Case `z ONE (`s (plus · (# 0) · ONE))))
        trans⟨ (`s-in Case-z) ⟩
        end
