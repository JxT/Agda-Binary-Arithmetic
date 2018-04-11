
-- Defining natural numbers

data myℕ : Set where
   zero : myℕ
   suc : myℕ → myℕ
-- defines nat numbers as zero,
-- and all successors of zero
