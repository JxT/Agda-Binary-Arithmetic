
-- Vectors and Finite sets

data Vec (A : Set) : ℕ → Set where 
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

data MyFin : ℕ → Set where
  zero : {n : ℕ} → MyFin (suc n)
  suc : {n : ℕ} → MyFin n → MyFin (suc n)

_‼s_ : {A : Set}{n : ℕ} → Vec A n → MyFin n → A
[] ‼s ()
(x ∷ v) ‼s zero = x
(x ∷ v) ‼s suc i = v ‼s i


data 𝕃 {l} (A : Set l) : Set l where
  [] : 𝕃 A
  _::_ : (x : A) (xs : 𝕃 A) → 𝕃 A

mylength : ∀{l}{A : Set l} → 𝕃 A → ℕ
mylength [] = 0
mylength (x :: xs) = suc (mylength xs)

-- Usage examples:
-- mylength []
-- mylength (1 :: [])
-- mylength (1 :: (2 :: []))
