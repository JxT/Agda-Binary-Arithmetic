
-- Implementing Diadic numbers
-- as a list of Booleans

{-	Diadic numbers

	0 []
	1 [false]
	2 [true]
	3 [false,false]
	4 [true,false]
	5 [false,true]
	6 [true,true]
	7 [false,false,false]
	8 [true,false,false]
	9 [false,true,false]
	10 [true,true,false]
	11 [false,false,true]
	...
-}

open import Data.Nat
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality

Diadic : Set
Diadic = List Bool

zeroD : Diadic
zeroD = []

oneD : Diadic
oneD = false ∷ []


-- Successor

sucD : Diadic → Diadic
sucD [] = oneD
sucD (false ∷ xs) = true ∷ xs
sucD (true ∷ xs) = false ∷ sucD xs


-- Predecessor

preD : Diadic → Diadic
preD [] = zeroD
preD (true ∷ xs) = false ∷ xs
preD (false ∷ xs) = preD xs


-- Conversion from ℕ

natToD : ℕ → Diadic
natToD zero = zeroD
natToD (suc n) = sucD (natToD n)


-- Conversion to ℕ

diaToNat : Diadic → ℕ
diaToNat [] = zero
diaToNat (false ∷ xs) = 1 + 2 * diaToNat xs
diaToNat (true ∷ xs) = 2 + 2 * diaToNat xs


-- lemma for ntod, dton
nat2nat : (n : ℕ) → diaToNat (natToD n) ≡ n
nat2nat zero = refl
nat2nat (suc n) = {!cong suc (nat2nat n)!}


-- plus in binary

-- prove correct
-- two binary added, conversion natural numbers
-- two nats added, convert to binary

-- CHECK: Proving, etc.
