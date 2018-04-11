
-- Remainder from division by 2

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Fin hiding (_+_)
open import Relation.Binary.PropositionalEquality

double : ℕ → ℕ
double zero = zero
double (suc n) = suc(suc(double n))

half : ℕ → ℕ
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

rem2 : ℕ → Fin 2
rem2 zero = zero
rem2 (suc zero) = suc zero
rem2 (suc (suc n)) = rem2 n

lem : (i j : ℕ) → i + (suc (suc j)) ≡ suc (suc (i + j))
lem i j = trans (+-suc i (suc j)) (cong suc (+-suc i j))

lemma : (n : ℕ) → toℕ (rem2 n) + double (half n) ≡ n
lemma zero = refl
lemma (suc zero) = refl
lemma (suc (suc n)) = trans (lem (toℕ (rem2 n))  (double (half n))) (cong (λ x → suc(suc x)) (lemma n))

-- toℕ (rem2 (suc (suc n))) + double (half (suc (suc n)))  ≡ suc (suc n)


