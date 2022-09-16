module Category.Unit where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.Core.Unit
  using (dependent-associative-unit; dependent-compose-equal-unit;
    dependent-postcompose-unit; dependent-precompose-unit)
open import Category.Lift.Unit
  using (dependent-lift-unit)
open import Category.Simple
  using (DependentSimpleCategory; simple-category)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-category-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentCategory C
dependent-category-unit C'
  = record
  { compose-equal
    = dependent-compose-equal-unit X X X
  ; precompose
    = dependent-precompose-unit X X
  ; postcompose
    = dependent-postcompose-unit X X
  ; associative
    = dependent-associative-unit X X X X
  ; lift
    = dependent-lift-unit l
  }
  where
    X = DependentSimpleCategory.object C'
    l = DependentSimpleCategory.lift C'

-- ## Nondependent

category-unit
  : Set
  → Category
category-unit A
  = dependent-category-unit
    (simple-category A)

