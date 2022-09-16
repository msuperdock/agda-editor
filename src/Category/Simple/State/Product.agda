module Category.Simple.State.Product where

open import Category
  using (ChainCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory; dependent-state-category-simple)
open import Category.State.Product
  using (dependent-state-category-product)
open import Category.State.Unit
  using (dependent-state-category-unit)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-simple-state-category-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleStateCategory C
  → DependentSimpleStateCategory C
  → DependentSimpleStateCategory C
dependent-simple-state-category-product C₁' C₂'
  = dependent-state-category-simple
  $ dependent-state-category-product
    (dependent-state-category-unit C₁')
    (dependent-state-category-unit C₂')

