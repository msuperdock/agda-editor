module Encoding.Product where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Product
  using (dependent-category-product)
open import Category.Split.Core.Product
  using (split-base-product)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (_×_)
open import Encoding
  using (DependentEncoding; Encoding; split-base-encoding)

-- ## Base

encoding-product
  : {A₁ A₂ B₁ B₂ : Set}
  → Encoding A₁ B₁
  → Encoding A₂ B₂
  → Encoding (A₁ × A₂) (B₁ × B₂)
encoding-product e₁ e₂
  = split-base-encoding
  $ split-base-product
    (Encoding.split-base e₁)
    (Encoding.split-base e₂)

-- ## Dependent

dependent-encoding-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → {A₁ A₂ : Set}
  → DependentEncoding C₁' A₁
  → DependentEncoding C₂' A₂
  → DependentEncoding
    (dependent-category-product C₁' C₂')
    (A₁ × A₂)
dependent-encoding-product {n = zero} e₁ e₂
  = encoding-product e₁ e₂
dependent-encoding-product {n = suc _} e₁ e₂
  = record
  { tail
    = λ x → dependent-encoding-product
      (DependentEncoding.tail e₁ x)
      (DependentEncoding.tail e₂ x)
  }

