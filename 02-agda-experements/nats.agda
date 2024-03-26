open import Relation.Binary.PropositionalEquality
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s; pred)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_)
open import Relation.Nullary using (¬_)
open import Function using (_∋_; _$_)

as-syntax : (A : Set) → A → A
as-syntax _ x = x
infix 0 as-syntax
syntax as-syntax A x = x ⦂ A

cong₃ : ∀ {A B C D : Set} {x y z a b c} (f : A → B → C → D) → x ≡ a → y ≡ b → z ≡ c
  → f x y z ≡ f a b c
cong₃ _ refl refl refl = refl

record Iso A B : Set where
  constructor _&_left_right_
  field
    left : A → B
    right : B → A
    leftinv : ∀ {x : A} → right (left x) ≡ x
    rightinv : ∀ {x : B} → left (right x) ≡ x

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

id : {A : Set} → A → A
id x = x

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

half~ : ℕ → ℕ
half~ zero = zero
half~ (suc zero) = zero
half~ (suc (suc n)) = suc (half~ n)

if_then_else_ : {A : Set} → 𝔹 → A → A → A
if true then a else _ = a
if false then _ else b = b

if-then-else-simple : {A : Set} {x y z : A} {b : 𝔹}
  → b ≡ true
  → if b then x else y ≡ z
  → x ≡ z
if-then-else-simple {A} {x} {y} {z} {b} bt ite =
  trans (cong₃ if_then_else_ (sym bt) refl refl) ite

even? : ℕ → 𝔹
even? zero = true
even? (suc zero) = false
even? (suc (suc n)) = even? n

even-double : {a : ℕ} → even? (double a) ≡ true
even-double {zero} = refl
even-double {suc zero} = refl
even-double {suc (suc n)} = even-double {n}

even-suc-double : {a : ℕ} → even? (suc (double a)) ≡ false
even-suc-double {zero} = refl
even-suc-double {suc zero} = refl
even-suc-double {suc (suc n)} = even-suc-double {n}

double-refl : {n : ℕ} → double (suc n) ≡ suc (suc (double n))
double-refl = refl

half~-double-ref : {n : ℕ} → half~ (double n) ≡ n
half~-double-ref {zero} = refl
half~-double-ref {suc n} =
  trans (cong half~ refl)
  $ cong suc half~-double-ref

half~-suc-double-ref : {n : ℕ} → half~ (suc (double n)) ≡ n
half~-suc-double-ref {zero} = refl
half~-suc-double-ref {suc n} =
  trans (cong half~ refl) (cong suc half~-suc-double-ref)

to : ℕ → ℤ
to n = if even? n then (+ (half~ n)) else (-[1+ (half~ n)  ])

from : ℤ → ℕ
from (+ n) = double n
from (-[1+ n ]) = suc (double n)

to→from : (n : ℤ) → to (from n) ≡ n
to→from (+_ zero) = refl
to→from (+_ (suc n)) = cong₃ if_then_else_ (even-double {n}) (cong +_ (cong suc half~-double-ref)) refl
to→from (-[1+_] zero) = refl
to→from (-[1+_] (suc n)) = cong₃ if_then_else_ (even-suc-double {n}) refl (cong -[1+_] (cong suc half~-suc-double-ref))
