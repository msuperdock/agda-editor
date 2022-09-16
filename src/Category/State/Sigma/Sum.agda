module Category.State.Sigma.Sum where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.Core.Sigma.Sum
  using (dependent-associative-sigma-sum; dependent-compose-equal-sigma-sum;
    dependent-postcompose-sigma-sum; dependent-precompose-sigma-sum;
    dependent-simplify-sigma-sum)
open import Category.Snoc
  using (chain-category-snoc)
open import Category.Split
  using (DependentSplitFunctor; SplitFunctor)
open import Category.State
  using (DependentStateCategory; DependentStateCategory₁; StateCategory)
open import Category.State.Lift.Sigma.Sum
  using (dependent-state-lift-sigma-sum)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-state-category-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentStateCategory C}
  → {D₁' : DependentCategory C}
  → DependentStateCategory (chain-category-snoc D₁')
  → DependentSplitFunctor C₁' D₁'
  → DependentStateCategory C
dependent-state-category-sigma-sum {C₁' = C₁'} C₂' F₁
  = record
  { simplify
    = dependent-simplify-sigma-sum
      (DependentStateCategory.simplify C₁')
      (DependentStateCategory.simplify C₂') a₁ a₁
  ; compose-equal
    = dependent-compose-equal-sigma-sum
      (DependentStateCategory.compose-equal C₁')
      (DependentStateCategory.compose-equal C₂') a₁ a₁ a₁
  ; precompose
    = dependent-precompose-sigma-sum
      (DependentStateCategory.precompose C₁')
      (DependentStateCategory.precompose C₂') a₁ a₁
  ; postcompose
    = dependent-postcompose-sigma-sum
      (DependentStateCategory.postcompose C₁')
      (DependentStateCategory.postcompose C₂') a₁ a₁
  ; associative
    = dependent-associative-sigma-sum
      (DependentStateCategory.associative C₁')
      (DependentStateCategory.associative C₂') a₁ a₁ a₁ a₁
  ; lift
    = dependent-state-lift-sigma-sum
      (DependentStateCategory.lift C₂') l₁
  }
  where
    a₁ = DependentSplitFunctor.base F₁
    l₁ = DependentSplitFunctor.lift F₁

-- ## Nondependent

state-category-sigma-sum
  : {C₁ : StateCategory}
  → {D₁ : Category}
  → DependentStateCategory₁ D₁
  → SplitFunctor C₁ D₁
  → StateCategory
state-category-sigma-sum
  = dependent-state-category-sigma-sum

