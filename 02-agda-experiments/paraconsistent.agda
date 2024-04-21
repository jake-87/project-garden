open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

as-syntax : (A : Set) → A → A
as-syntax _ x = x
infix 0 as-syntax
syntax as-syntax A x = x ∶ A

infix 111 `¬_
infix 110 _∧_
infix 110 _∨_
infix 110 _∘_
infix 109 _⇒_
infixr 108 ↑_
infix 107 _⊂_

Id : Set
Id = String

data Term : Set where
  id : Id → Term
  _∧_ : Term → Term → Term
  -- keeps introduction
  _∨_ : Term → Term → Term
  -- keeps syllogism
  _∘_ : Term → Term → Term
  `¬_ : Term → Term
  _⇒_ : Term → Term → Term
  `true : Term
  `false : Term
  `⊥ : Term

data Value : Term → Set where
  ∧-intro : ∀ {A B} → Value (A ∧ B)
  ∨-intro : ∀ {A B} → Value (A ∨ B)
  `¬-intro : ∀ {A} → Value (`¬ A)

data ↑_∥_ {A B} : Value A → Value B → Set where
  test : ∀ {A B} → ↑ (Value (A ∧ B)) ∥ Value A

