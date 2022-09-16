module Category.Simple.Partial.Sigma where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Simple
  using (DependentSet)
open import Category.Simple.Partial
  using (DependentSimplePartialFunction)
open import Category.Simple.Sigma
  using (dependent-set-sigma)
open import Category.Simple.State
  using (DependentSimpleStateCategory; DependentSimpleStateCategory₁)
open import Category.Simple.State.Sigma.Sum
  using (dependent-simple-state-category-sigma-sum)
open import Category.Snoc
  using (chain-category-snoc)
open import Category.Split
  using (DependentSplitFunctor)
open import Category.State
  using (DependentStateCategory)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)

-- ## Base

partial-function-sigma
  : {A₁ B₁ : Set}
  → (A₂ B₂ : B₁ → Set)
  → ((x₁ : B₁) → A₂ x₁ → Maybe (B₂ x₁))
  → (A₁ ⊔ Σ B₁ A₂ → Maybe (Σ B₁ B₂))
partial-function-sigma _ _ _ (ι₁ _)
  = nothing
partial-function-sigma _ _ f₂ (ι₂ (x₁ , x₂))
  with f₂ x₁ x₂
... | nothing
  = nothing
... | just x₂'
  = just (x₁ , x₂')

-- ## Dependent

dependent-simple-partial-function-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentStateCategory C}
  → {D₁' : DependentCategory C}
  → {C₂' : DependentSimpleStateCategory (chain-category-snoc D₁')}
  → {D₂' : DependentSet (chain-category-snoc D₁')}
  → (F₁ : DependentSplitFunctor C₁' D₁')
  → DependentSimplePartialFunction C₂' D₂'
  → DependentSimplePartialFunction
    (dependent-simple-state-category-sigma-sum C₂' F₁)
    (dependent-set-sigma D₁' D₂')
dependent-simple-partial-function-sigma {n = zero}
  {D₁' = D₁'} {C₂' = C₂'} {D₂' = D₂'} _ F₂
  = partial-function-sigma
    (DependentSimpleStateCategory₁.Object D₁' C₂')
    (DependentSet.tail D₂')
    (DependentSimplePartialFunction.tail F₂)
dependent-simple-partial-function-sigma {n = suc _} F₁ F₂
  = record
  { tail
    = λ x → dependent-simple-partial-function-sigma
      (DependentSplitFunctor.tail F₁ x)
      (DependentSimplePartialFunction.tail F₂ x)
  }

