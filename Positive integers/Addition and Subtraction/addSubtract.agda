
open import Data.Nat
open import Relation.Binary.PropositionalEquality

-- Addition

add : ℕ → ℕ → ℕ
add zero y = y
add (suc x) y = suc (add x y)

-- Subtraction

subtract : ℕ → ℕ → ℕ
subtract n zero = n
subtract zero (suc m) = zero
subtract (suc n) (suc m) = subtract n m


-- Lemma for the associativity
-- property of addition

assocplus : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
assocplus zero n p = refl
assocplus (suc m ) n p = cong suc (assocplus m n p)
