
-- Remainder from division by 3

open import Data.Nat
open import Data.Fin

rem3 : ℕ → Fin 3
rem3 zero = zero
rem3 (suc zero) = suc zero
rem3 (suc (suc zero)) = suc (suc zero)
rem3 (suc (suc (suc x))) = rem3 x