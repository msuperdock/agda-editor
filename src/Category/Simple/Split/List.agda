module Category.Simple.Split.List where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.List
  using (dependent-simple-category-list)
open import Category.Simple.Split
  using (DependentSimpleSplitFunctor; dependent-split-functor-simple)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.List
  using (dependent-simple-state-category-list)
open import Category.Split.List
  using (dependent-split-functor-list)
open import Category.Split.Unit
  using (dependent-split-functor-unit)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-simple-split-functor-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → {D' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor C' D'
  → DependentSimpleSplitFunctor
    (dependent-simple-state-category-list C')
    (dependent-simple-category-list D')
dependent-simple-split-functor-list F
  = dependent-split-functor-simple
  $ dependent-split-functor-list
    (dependent-split-functor-unit F)

