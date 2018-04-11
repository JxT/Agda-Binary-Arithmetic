
-- Example implementing binary trees in Agda

open import Data.Nat
open import Data.List

data binTree (A : Set) : Set where
  leaf : A → binTree A
  node : binTree A → binTree A → binTree A

tree : binTree ℕ
tree = node (node (leaf 1) (leaf 2)) (leaf 3)

subTreeA : binTree ℕ
subTreeA = node (leaf 1) (leaf 2)

subTreeB : binTree ℕ
subTreeB = node (subTreeA) (leaf 3)

noLeaves : {A : Set} → binTree A → ℕ
noLeaves (leaf x) = 1
noLeaves (node l r) = noLeaves l + noLeaves r