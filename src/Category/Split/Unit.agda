module Category.Split.Unit where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Split
  using (DependentSimpleSplitFunctor)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Split
  using (DependentSplitFunctor)
open import Category.Split.Core.Unit
  using (dependent-split-compose-unit; dependent-split-identity-unit)
open import Category.Split.Lift.Unit
  using (dependent-split-lift-unit)
open import Category.State.Unit
  using (dependent-state-category-unit)
open import Category.Unit
  using (dependent-category-unit)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-split-functor-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → {D' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor C' D'
  → DependentSplitFunctor
    (dependent-state-category-unit C')
    (dependent-category-unit D')
dependent-split-functor-unit F
  = record
  { identity
    = dependent-split-identity-unit a
  ; compose
    = dependent-split-compose-unit a a a
  ; lift
    = dependent-split-lift-unit l
  }
  where
    a = DependentSimpleSplitFunctor.base F
    l = DependentSimpleSplitFunctor.lift F

