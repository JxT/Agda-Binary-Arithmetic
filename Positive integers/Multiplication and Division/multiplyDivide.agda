
open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality

-- Double

double : ℕ → ℕ
double zero = zero
double (suc n) = suc(suc(double n))

-- Multiply

multiply : ℕ → ℕ → ℕ

multiply zero n = zero
multiply m zero = zero

multiply (suc zero) n = n
multiply n (suc zero) = n

multiply (suc m) (suc n) = (suc m) + multiply (suc m) n

-- Half

half : ℕ → ℕ
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

-- Division

subtract : ℕ → ℕ → ℕ
subtract n zero = n
subtract zero (suc m) = zero
subtract (suc n) (suc m) = subtract n m

divide : ℕ → ℕ → ℕ

divide zero n = zero
divide n zero = zero

divide n (suc zero) = n
divide (suc zero) m = suc zero

divide (suc m) (suc n) = divide (subtract (suc m) (suc n)) (suc n)


-- Proof

lem : (n : ℕ) → half (double n) ≡ n
lem zero = refl
lem (suc n) = cong suc (lem n) -- half (double (suc n)) ≡ suc n

-- This is proof by induction
