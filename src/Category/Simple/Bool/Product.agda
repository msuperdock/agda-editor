module Category.Simple.Bool.Product where

open import Category
  using (ChainCategory)
open import Category.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.Product
  using (dependent-simple-state-category-product)
open import Data.Bool
  using (Bool; _∧_)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (_×_; _,_)

-- ## Base

bool-function-product
  : {A₁ A₂ : Set}
  → (A₁ → Bool)
  → (A₂ → Bool)
  → (A₁ × A₂ → Bool)
bool-function-product f₁ f₂ (x₁ , x₂)
  = f₁ x₁ ∧ f₂ x₂

-- ## Dependent

dependent-simple-bool-function-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleStateCategory C}
  → DependentSimpleBoolFunction C₁'
  → DependentSimpleBoolFunction C₂'
  → DependentSimpleBoolFunction
    (dependent-simple-state-category-product C₁' C₂')
dependent-simple-bool-function-product {n = zero} F₁ F₂
  = bool-function-product F₁ F₂
dependent-simple-bool-function-product {n = suc _} F₁ F₂
  = record
  { tail
    = λ x → dependent-simple-bool-function-product
      (DependentSimpleBoolFunction.tail F₁ x)
      (DependentSimpleBoolFunction.tail F₂ x)
  }

