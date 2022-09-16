module Category.Simple.Bool.Sigma where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Simple.Bool
  using (DependentSimpleBoolFunction)
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
open import Data.Bool
  using (Bool; false)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)

-- ## Base

bool-function-sigma
  : {A₁ B₁ : Set}
  → (A₂ : B₁ → Set)
  → ((x₁ : B₁) → A₂ x₁ → Bool)
  → (A₁ ⊔ Σ B₁ A₂ → Bool)
bool-function-sigma _ _ (ι₁ _)
  = false
bool-function-sigma _ f₂ (ι₂ (x₁ , x₂))
  = f₂ x₁ x₂

-- ## Dependent

dependent-simple-bool-function-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentStateCategory C}
  → {D₁' : DependentCategory C}
  → {C₂' : DependentSimpleStateCategory (chain-category-snoc D₁')}
  → (F₁ : DependentSplitFunctor C₁' D₁')
  → DependentSimpleBoolFunction C₂'
  → DependentSimpleBoolFunction
    (dependent-simple-state-category-sigma-sum C₂' F₁)
dependent-simple-bool-function-sigma {n = zero} {D₁' = D₁'} {C₂' = C₂'} _ F₂
  = bool-function-sigma
    (DependentSimpleStateCategory₁.Object D₁' C₂')
    (DependentSimpleBoolFunction.tail F₂)
dependent-simple-bool-function-sigma {n = suc _} F₁ F₂
  = record
  { tail
    = λ x → dependent-simple-bool-function-sigma
      (DependentSplitFunctor.tail F₁ x)
      (DependentSimpleBoolFunction.tail F₂ x)
  }

