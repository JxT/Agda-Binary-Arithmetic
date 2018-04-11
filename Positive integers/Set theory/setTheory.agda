
-- Set theory and
-- relations between sets

open import Data.List
open import Relation.Binary.PropositionalEquality


-- Combining Sets
_+++_ : {A : Set} → List A → List A → List A
[] +++ ys = ys
(x ∷ xs) +++ ys = x ∷ (xs +++ ys)


-- Proving symmetric relations in sets

mySym : {A : Set} → (a a' : A) → a ≡ a' → a' ≡ a
mySym a .a refl = refl


-- Proving transitivity

myTrans : {A : Set} → {a1 a2 a3 : A}
  → a1 ≡ a2 → a2 ≡ a3 → a3 ≡ a1

myTrans refl refl = refl

