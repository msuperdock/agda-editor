module Category.List where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.Core.List
  using (dependent-associative-list; dependent-compose-equal-list;
    dependent-postcompose-list; dependent-precompose-list)
open import Category.Lift.List
  using (dependent-lift-list)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-category-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → DependentCategory C
dependent-category-list C'
  = record
  { compose-equal
    = dependent-compose-equal-list
      (DependentCategory.compose-equal C')
  ; precompose
    = dependent-precompose-list
      (DependentCategory.precompose C')
  ; postcompose
    = dependent-postcompose-list
      (DependentCategory.postcompose C')
  ; associative
    = dependent-associative-list
      (DependentCategory.associative C')
  ; lift
    = dependent-lift-list
      (DependentCategory.lift C')
  }

-- ## Nondependent

category-list
  : Category
  → Category
category-list
  = dependent-category-list

