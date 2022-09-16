module Category.Bool where

open import Category
  using (ChainCategory)
open import Category.Function
  using (DependentFunction)
open import Category.State
  using (DependentStateCategory)
open import Data.Bool
  using (Bool)
open import Data.Nat
  using (ℕ)

-- ## Dependent

DependentBoolFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentStateCategory C
  → Set
DependentBoolFunction C'
  = DependentFunction C' Bool

