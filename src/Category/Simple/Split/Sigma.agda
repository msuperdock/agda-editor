module Category.Simple.Split.Sigma where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Sigma
  using (dependent-simple-category-sigma)
open import Category.Simple.Split
  using (DependentSimpleSplitFunctor; dependent-split-functor-simple)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.Sigma.Sum
  using (dependent-simple-state-category-sigma-sum)
open import Category.Snoc
  using (chain-category-snoc)
open import Category.Split
  using (DependentSplitFunctor)
open import Category.Split.Sigma
  using (dependent-split-functor-sigma)
open import Category.Split.Unit
  using (dependent-split-functor-unit)
open import Category.State
  using (DependentStateCategory)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-simple-split-functor-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentStateCategory C}
  → {D₁' : DependentCategory C}
  → {C₂' : DependentSimpleStateCategory (chain-category-snoc D₁')}
  → {D₂' : DependentSimpleCategory (chain-category-snoc D₁')}
  → (F₁ : DependentSplitFunctor C₁' D₁')
  → DependentSimpleSplitFunctor C₂' D₂'
  → DependentSimpleSplitFunctor
    (dependent-simple-state-category-sigma-sum C₂' F₁)
    (dependent-simple-category-sigma D₁' D₂')
dependent-simple-split-functor-sigma F₁ F₂
  = dependent-split-functor-simple
  $ dependent-split-functor-sigma F₁
    (dependent-split-functor-unit F₂)

