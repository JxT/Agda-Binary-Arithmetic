
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

-- Modulus % 2

mod2 : ℕ → Fin 2
mod2 zero = zero
mod2 (suc zero) = suc zero
mod2 (suc (suc n)) = mod2 n

-- Modulus % 3

mod3 : ℕ → Fin 3
mod3 zero = zero
mod3 (suc zero) = suc zero
mod3 (suc (suc zero)) = suc (suc zero)
mod3 (suc (suc (suc x))) = mod3 x

-- Modulus function

mod : ℕ → ℕ → ℕ
mod m zero = zero
mod zero n = zero
mod (suc m) (suc n) = {!!}


-- Proofs

lem : (i j : ℕ) → i + (suc (suc j)) ≡ suc (suc (i + j))
lem i j = trans (+-suc i (suc j)) (cong suc (+-suc i j))

lemma : (n : ℕ) → toℕ (mod2 n) + double (half n) ≡ n
lemma zero = refl
lemma (suc zero) = refl
lemma (suc (suc n)) = trans (lem (toℕ (mod2 n))  (double (half n))) (cong (λ x → suc(suc x)) (lemma n))

-- toℕ (rem2 (suc (suc n))) + double (half (suc (suc n)))  ≡ suc (suc n)


