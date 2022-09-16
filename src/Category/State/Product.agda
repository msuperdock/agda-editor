module Category.State.Product where

open import Category
  using (ChainCategory)
open import Category.Core.Product
  using (dependent-associative-product; dependent-compose-equal-product;
    dependent-postcompose-product; dependent-precompose-product;
    dependent-simplify-product)
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Category.State.Lift.Product
  using (dependent-state-lift-product)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-state-category-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentStateCategory C
  → DependentStateCategory C
  → DependentStateCategory C
dependent-state-category-product C₁' C₂'
  = record
  { simplify
    = dependent-simplify-product
      (DependentStateCategory.simplify C₁')
      (DependentStateCategory.simplify C₂')
  ; compose-equal
    = dependent-compose-equal-product
      (DependentStateCategory.compose-equal C₁')
      (DependentStateCategory.compose-equal C₂')
  ; precompose
    = dependent-precompose-product
      (DependentStateCategory.precompose C₁')
      (DependentStateCategory.precompose C₂')
  ; postcompose
    = dependent-postcompose-product
      (DependentStateCategory.postcompose C₁')
      (DependentStateCategory.postcompose C₂')
  ; associative
    = dependent-associative-product
      (DependentStateCategory.associative C₁')
      (DependentStateCategory.associative C₂')
  ; lift
    = dependent-state-lift-product
      (DependentStateCategory.lift C₁')
      (DependentStateCategory.lift C₂')
  }

-- ## Nondependent

state-category-product
  : StateCategory
  → StateCategory
  → StateCategory
state-category-product
  = dependent-state-category-product

