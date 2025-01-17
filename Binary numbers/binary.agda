
-- Implementing binary
-- numbers as a list of booleans

open import Data.List
open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality

Binary : Set
Binary = List Bool

zeroB : Binary
zeroB = false ∷ []

oneB : Binary
oneB = true ∷ []

sixB : Binary 
sixB = false ∷ true ∷ true ∷ []


-- Successor

sucB : Binary → Binary
sucB [] = oneB
sucB (false ∷ bs) = true ∷ bs
sucB (true ∷ bs) = false ∷ sucB bs


-- Predecessor

predB : Binary → Binary

predB [] = []
predB (false ∷ []) = zeroB -- Zero also implemented as zeroB

predB (true ∷ []) = []

predB (false ∷ bs) = true ∷ predB bs
predB (true ∷ bs) = false ∷ bs


-- Double

doubleB : Binary → Binary

-- Just need to add a 0 to the end
-- [1 → 10; 101 → 1010]
-- (true ∷ false ∷ true ∷ []) → (false ∷ true ∷ false ∷ true ∷ [])

doubleB [] = []
doubleB (false ∷ []) = zeroB -- Zero also implemented as zeroB

doubleB (false ∷ xs) = false ∷ false ∷ xs
doubleB (true ∷ xs) = false ∷ true ∷ xs


-- Remainder for division by 2
-- You can just use the last bit

rem2 : Binary → Binary
rem2 [] = []
rem2 (false ∷ xs) = zeroB
rem2 (true ∷ xs) = oneB


-- Addition with natural numbers

_b+_ : Bool → ℕ → ℕ 
_b+_ = {!!}
-- prove that: rem2 n +b double (half n) ≡ n 


-- Conversion from ℕ 

nat2bin : ℕ → Binary 
nat2bin zero = zeroB
nat2bin (suc n) = sucB (nat2bin n)


-- Conversion to ℕ 

double : ℕ → ℕ
double zero = zero
double (suc n) = suc(suc(double n))

bin2nat : Binary → ℕ
bin2nat [] = 0
bin2nat (false ∷ bs) = double (bin2nat bs)
bin2nat (true ∷ bs) = suc (double (bin2nat bs))


-- Lemma for conversion functions

sucBlem : (bs : Binary) → bin2nat (sucB bs) ≡ suc (bin2nat bs)
sucBlem [] = refl
sucBlem (false ∷ bs) = refl
sucBlem (true ∷ bs) = trans (cong double (sucBlem bs)) refl

nat2nat : (n : ℕ) → bin2nat (nat2bin n) ≡ n
nat2nat zero = refl
nat2nat (suc n) = trans (sucBlem (nat2bin n)) (cong suc (nat2nat n))

--bin2bin : (bs : Binary) → nat2bin (bin2nat bs) ≡ bs
--bin2bin [] = {!refl!}
--bin2bin (x ∷ bs) = {!!}

prd : ℕ → ℕ
prd zero = zero
prd (suc n) = n

predLem : (xs : Binary) → bin2nat (predB xs) ≡ prd (bin2nat xs)
predLem [] = refl
predLem (false ∷ xs) = {!!}
predLem (true ∷ xs) = {!!}
