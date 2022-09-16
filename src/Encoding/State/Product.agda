module Encoding.State.Product where

open import Category
  using (ChainCategory)
open import Category.State
  using (DependentStateCategory)
open import Category.State.Product
  using (dependent-state-category-product)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (_×_)
open import Encoding.Product
  using (encoding-product)
open import Encoding.State
  using (DependentStateEncoding)

-- ## Dependent

dependent-state-encoding-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentStateCategory C}
  → {C₂' : DependentStateCategory C}
  → {A₁ A₂ : Set}
  → DependentStateEncoding C₁' A₁
  → DependentStateEncoding C₂' A₂
  → DependentStateEncoding
    (dependent-state-category-product C₁' C₂')
    (A₁ × A₂)
dependent-state-encoding-product {n = zero} e₁ e₂
  = encoding-product e₁ e₂
dependent-state-encoding-product {n = suc _} e₁ e₂
  = record
  { tail
    = λ x → dependent-state-encoding-product
      (DependentStateEncoding.tail e₁ x)
      (DependentStateEncoding.tail e₂ x)
  }

