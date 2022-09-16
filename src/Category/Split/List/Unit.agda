module Category.Split.List.Unit where

open import Category
  using (ChainCategory)
open import Category.List
  using (dependent-category-list)
open import Category.List.Unit
  using (dependent-category-list-unit; dependent-split-prefunctor-list-unit)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Split
  using (DependentSplitFunctor')
open import Category.Split.Induced
  using (dependent-split-functor-induced')
open import Category.Unit
  using (dependent-category-unit)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-split-functor-list-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C' : DependentSimpleCategory C)
  → DependentSplitFunctor'
    (dependent-category-list
      (dependent-category-unit C'))
    (dependent-category-list-unit C')
dependent-split-functor-list-unit C'
  = dependent-split-functor-induced'
  $ dependent-split-prefunctor-list-unit C'

