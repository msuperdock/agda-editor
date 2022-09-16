module Category.Simple.State.List where

open import Category
  using (ChainCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory; dependent-state-category-simple)
open import Category.State.List
  using (dependent-state-category-list)
open import Category.State.Unit
  using (dependent-state-category-unit)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-simple-state-category-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleStateCategory C
  → DependentSimpleStateCategory C
dependent-simple-state-category-list C'
  = dependent-state-category-simple
  $ dependent-state-category-list
    (dependent-state-category-unit C')

