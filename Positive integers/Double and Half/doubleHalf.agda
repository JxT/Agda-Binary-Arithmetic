
-- Example showing double and half
-- natural numbers, with proof

open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality

double : ℕ → ℕ
double zero = zero
double (suc n) = suc(suc(double n))

half : ℕ → ℕ
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)


-- Proof

lem : (n : ℕ) → half (double n) ≡ n
lem zero = refl
lem (suc n) = cong suc (lem n) -- half (double (suc n)) ≡ suc n

-- This is proof by induction
