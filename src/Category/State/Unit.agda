module Category.State.Unit where

open import Category
  using (ChainCategory)
open import Category.Core.Unit
  using (dependent-associative-unit; dependent-compose-equal-unit;
    dependent-postcompose-unit; dependent-precompose-unit;
    dependent-simplify-unit)
open import Category.Simple.State
  using (DependentSimpleStateCategory; simple-state-category)
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Category.State.Lift.Unit
  using (dependent-state-lift-unit)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-state-category-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleStateCategory C
  → DependentStateCategory C
dependent-state-category-unit C'
  = record
  { simplify
    = dependent-simplify-unit X X
  ; compose-equal
    = dependent-compose-equal-unit X X X
  ; precompose
    = dependent-precompose-unit X X
  ; postcompose
    = dependent-postcompose-unit X X
  ; associative
    = dependent-associative-unit X X X X
  ; lift
    = dependent-state-lift-unit l
  }
  where
    X = DependentSimpleStateCategory.object C'
    l = DependentSimpleStateCategory.lift C'

-- ## Nondependent

state-category-unit
  : Set
  → StateCategory
state-category-unit A
  = dependent-state-category-unit
    (simple-state-category A)

