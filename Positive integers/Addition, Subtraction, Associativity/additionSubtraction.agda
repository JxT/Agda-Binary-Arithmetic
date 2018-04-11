
-- Addition and subtraction

open import Data.Nat
open import Relation.Binary.PropositionalEquality

plus : ℕ → ℕ → ℕ  -- \to
plus zero    y = y
plus (suc x) y = suc (plus x y)

minusOne : ℕ → ℕ
minusOne zero = zero
minusOne (suc n) = n


-- Lemma for the associativity
-- property of addition

assocplus : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
assocplus zero n p = refl
assocplus (suc m ) n p = cong suc (assocplus m n p)
