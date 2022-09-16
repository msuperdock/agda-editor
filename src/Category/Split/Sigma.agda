module Category.Split.Sigma where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Sigma
  using (dependent-category-sigma)
open import Category.Snoc
  using (chain-category-snoc)
open import Category.Split
  using (DependentSplitFunctor)
open import Category.Split.Core.Sigma
  using (dependent-split-compose-sigma; dependent-split-identity-sigma)
open import Category.Split.Lift.Sigma
  using (dependent-split-lift-sigma)
open import Category.State
  using (DependentStateCategory)
open import Category.State.Sigma.Sum
  using (dependent-state-category-sigma-sum)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-split-functor-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentStateCategory C}
  → {D₁' : DependentCategory C}
  → {C₂' : DependentStateCategory (chain-category-snoc D₁')}
  → {D₂' : DependentCategory (chain-category-snoc D₁')}
  → (F₁ : DependentSplitFunctor C₁' D₁')
  → DependentSplitFunctor C₂' D₂'
  → DependentSplitFunctor
    (dependent-state-category-sigma-sum C₂' F₁)
    (dependent-category-sigma D₁' D₂')
dependent-split-functor-sigma F₁ F₂
  = record
  { identity
    = dependent-split-identity-sigma
      (DependentSplitFunctor.identity F₁)
      (DependentSplitFunctor.identity F₂)
  ; compose
    = dependent-split-compose-sigma
      (DependentSplitFunctor.compose F₁)
      (DependentSplitFunctor.compose F₂)
  ; lift
    = dependent-split-lift-sigma
      (DependentSplitFunctor.lift F₁)
      (DependentSplitFunctor.lift F₂)
  }

