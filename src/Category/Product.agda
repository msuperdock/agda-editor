module Category.Product where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.Core.Product
  using (dependent-associative-product; dependent-compose-equal-product;
    dependent-postcompose-product; dependent-precompose-product)
open import Category.Lift.Product
  using (dependent-lift-product)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-category-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → DependentCategory C
  → DependentCategory C
dependent-category-product C₁' C₂'
  = record
  { compose-equal
    = dependent-compose-equal-product
      (DependentCategory.compose-equal C₁')
      (DependentCategory.compose-equal C₂')
  ; precompose
    = dependent-precompose-product
      (DependentCategory.precompose C₁')
      (DependentCategory.precompose C₂')
  ; postcompose
    = dependent-postcompose-product
      (DependentCategory.postcompose C₁')
      (DependentCategory.postcompose C₂')
  ; associative
    = dependent-associative-product
      (DependentCategory.associative C₁')
      (DependentCategory.associative C₂')
  ; lift
    = dependent-lift-product
      (DependentCategory.lift C₁')
      (DependentCategory.lift C₂')
  }

-- ## Nondependent

category-product
  : Category
  → Category
  → Category
category-product
  = dependent-category-product

