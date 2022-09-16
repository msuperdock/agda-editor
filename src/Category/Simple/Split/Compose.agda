module Category.Simple.Split.Compose where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Split
  using (DependentSimpleSplitFunctor; DependentSimpleSplitFunctor')
open import Category.Simple.Split.Lift.Compose
  using (dependent-simple-split-lift-compose)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-simple-split-functor-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → {D' E' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor' D' E'
  → DependentSimpleSplitFunctor C' D'
  → DependentSimpleSplitFunctor C' E'
dependent-simple-split-functor-compose F G
  = record
  { lift
    = dependent-simple-split-lift-compose
      (DependentSimpleSplitFunctor'.lift F)
      (DependentSimpleSplitFunctor.lift G)
  }

