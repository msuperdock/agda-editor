module Category.Split.Product where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Product
  using (dependent-category-product)
open import Category.Split
  using (DependentSplitFunctor)
open import Category.Split.Core.Product
  using (dependent-split-compose-product; dependent-split-identity-product)
open import Category.Split.Lift.Product
  using (dependent-split-lift-product)
open import Category.State
  using (DependentStateCategory)
open import Category.State.Product
  using (dependent-state-category-product)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-split-functor-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentStateCategory C}
  → {D₁' D₂' : DependentCategory C}
  → DependentSplitFunctor C₁' D₁'
  → DependentSplitFunctor C₂' D₂'
  → DependentSplitFunctor
    (dependent-state-category-product C₁' C₂')
    (dependent-category-product D₁' D₂')
dependent-split-functor-product F₁ F₂
  = record
  { identity
    = dependent-split-identity-product
      (DependentSplitFunctor.identity F₁)
      (DependentSplitFunctor.identity F₂)
  ; compose
    = dependent-split-compose-product
      (DependentSplitFunctor.compose F₁)
      (DependentSplitFunctor.compose F₂)
  ; lift
    = dependent-split-lift-product
      (DependentSplitFunctor.lift F₁)
      (DependentSplitFunctor.lift F₂)
  }

