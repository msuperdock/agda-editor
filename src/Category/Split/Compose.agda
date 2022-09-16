module Category.Split.Compose where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Split
  using (DependentSplitFunctor; DependentSplitFunctor')
open import Category.Split.Core.Compose
  using (dependent-split-compose-compose; dependent-split-identity-compose)
open import Category.Split.Lift.Compose
  using (dependent-split-lift-compose)
open import Category.State
  using (DependentStateCategory)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-split-functor-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → {D' E' : DependentCategory C}
  → DependentSplitFunctor' D' E'
  → DependentSplitFunctor C' D'
  → DependentSplitFunctor C' E'
dependent-split-functor-compose {D' = D'} F G
  = record
  { identity
    = dependent-split-identity-compose
      (DependentCategory.compose-equal D')
      (DependentCategory.precompose D')
      (DependentSplitFunctor'.identity F)
      (DependentSplitFunctor.identity G)
      (DependentSplitFunctor.compose G)
  ; compose
    = dependent-split-compose-compose
      (DependentSplitFunctor'.compose F)
      (DependentSplitFunctor.compose G)
  ; lift
    = dependent-split-lift-compose
      (DependentSplitFunctor'.lift F)
      (DependentSplitFunctor.lift G)
  }

