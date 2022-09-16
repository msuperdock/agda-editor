module Category.Simple.Partial.Product where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSet)
open import Category.Simple.Partial
  using (DependentSimplePartialFunction)
open import Category.Simple.Product
  using (dependent-set-product)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.Product
  using (dependent-simple-state-category-product)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (_×_; _,_)

-- ## Base

partial-function-product
  : {A₁ A₂ B₁ B₂ : Set}
  → (A₁ → Maybe B₁)
  → (A₂ → Maybe B₂)
  → (A₁ × A₂ → Maybe (B₁ × B₂))
partial-function-product f₁ f₂ (x₁ , x₂)
  with f₁ x₁
  | f₂ x₂
... | nothing | _
  = nothing
... | _ | nothing
  = nothing
... | just x₁' | just x₂'
  = just (x₁' , x₂')

-- ## Dependent

dependent-simple-partial-function-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleStateCategory C}
  → {D₁' D₂' : DependentSet C}
  → DependentSimplePartialFunction C₁' D₁'
  → DependentSimplePartialFunction C₂' D₂'
  → DependentSimplePartialFunction
    (dependent-simple-state-category-product C₁' C₂')
    (dependent-set-product D₁' D₂')
dependent-simple-partial-function-product {n = zero} F₁ F₂
  = partial-function-product F₁ F₂
dependent-simple-partial-function-product {n = suc _} F₁ F₂
  = record
  { tail
    = λ x → dependent-simple-partial-function-product
      (DependentSimplePartialFunction.tail F₁ x)
      (DependentSimplePartialFunction.tail F₂ x)
  }

