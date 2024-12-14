import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; _+_; _∸_; compare; less; equal; greater)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List using (List; _++_; _∷_; []; [_]; map)
open import Data.Maybe using (Maybe; just; nothing)

data Ty : Set where
     -- irrelevant for bug
     
Con = List Ty

index : List Ty → ℕ → Maybe Ty
index _ _ = nothing -- irrelevant

data Tm : Set where
  V : ℕ → Tm

subst-shift : Tm → ℕ → Tm → Tm
subst-shift (V x) n new with compare x n
... | less .x k = V x
... | equal .x = new
... | greater .n k = V (x ∸ 1)

data _⊢_⦂_ : Con → Tm → Ty → Set where
  ⊢V : ∀ {Γ x t} →
    index Γ x Eq.≡ just t →
    Γ ⊢ V x ⦂ t

subst-shift-pres : ∀ {Γ tm sub ty₁ ty₂} →
                   Γ ⊢ tm ⦂ ty₁ →
                   (ty₂ ∷ Γ) ⊢ subst-shift tm 1 sub ⦂ ty₁
subst-shift-pres {Γ} {V x} {sub} {ty₁} {ty₂} ⊢tm with compare x 1 in eq
... | k = {!!}
