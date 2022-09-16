module Category.Sigma where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Core.Sigma
  using (dependent-associative-sigma; dependent-compose-equal-sigma;
    dependent-postcompose-sigma; dependent-precompose-sigma)
open import Category.Lift.Sigma
  using (dependent-lift-sigma)
open import Category.Snoc
  using (chain-category-snoc)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-category-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C₁' : DependentCategory C)
  → DependentCategory (chain-category-snoc C₁')
  → DependentCategory C
dependent-category-sigma C₁' C₂'
  = record
  { compose-equal
    = dependent-compose-equal-sigma
      (DependentCategory.compose-equal C₁')
      (DependentCategory.compose-equal C₂')
  ; precompose
    = dependent-precompose-sigma
      (DependentCategory.precompose C₁')
      (DependentCategory.precompose C₂')
  ; postcompose
    = dependent-postcompose-sigma
      (DependentCategory.postcompose C₁')
      (DependentCategory.postcompose C₂')
  ; associative
    = dependent-associative-sigma
      (DependentCategory.associative C₁')
      (DependentCategory.associative C₂')
  ; lift
    = dependent-lift-sigma
      (DependentCategory.lift C₂')
  }

