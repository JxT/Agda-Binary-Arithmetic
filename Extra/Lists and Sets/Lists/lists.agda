
-- Lists

data myList (A : Set) : Set where
    [] : myList A
    _∷_ : A → myList A → myList A

-- Usage examples:
-- []
-- A :: A
-- true :: true
-- 0 :: 0

_‼_ : {A : Set} → List A → ℕ → Maybe A
[] ‼ n = nothing
(x ∷ l) ‼ zero = just x
(x ∷ l) ‼ suc n = l ‼ n