module Category.Split.List where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.List
  using (dependent-category-list)
open import Category.Split
  using (DependentSplitFunctor)
open import Category.Split.Core.List
  using (dependent-split-compose-list; dependent-split-identity-list)
open import Category.Split.Lift.List
  using (dependent-split-lift-list)
open import Category.State
  using (DependentStateCategory)
open import Category.State.List
  using (dependent-state-category-list)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-split-functor-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → {D' : DependentCategory C}
  → DependentSplitFunctor C' D'
  → DependentSplitFunctor
    (dependent-state-category-list C')
    (dependent-category-list D')
dependent-split-functor-list {C' = C'} F
  = record
  { identity
    = dependent-split-identity-list
      (DependentSplitFunctor.identity F)
  ; compose
    = dependent-split-compose-list
      (DependentStateCategory.compose-equal C')
      (DependentSplitFunctor.compose F)
  ; lift
    = dependent-split-lift-list
      (DependentSplitFunctor.lift F)
  }

