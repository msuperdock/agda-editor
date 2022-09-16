module Category.Simple.State.Sigma.Sum where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory; dependent-state-category-simple)
open import Category.Snoc
  using (chain-category-snoc)
open import Category.Split
  using (DependentSplitFunctor)
open import Category.State
  using (DependentStateCategory)
open import Category.State.Sigma.Sum
  using (dependent-state-category-sigma-sum)
open import Category.State.Unit
  using (dependent-state-category-unit)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-simple-state-category-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentStateCategory C}
  → {D₁' : DependentCategory C}
  → DependentSimpleStateCategory (chain-category-snoc D₁')
  → DependentSplitFunctor C₁' D₁'
  → DependentSimpleStateCategory C
dependent-simple-state-category-sigma-sum C₂' F₁
  = dependent-state-category-simple
  $ dependent-state-category-sigma-sum
    (dependent-state-category-unit C₂') F₁

