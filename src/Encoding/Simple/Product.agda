module Encoding.Simple.Product where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Product
  using (dependent-simple-category-product)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)
open import Data.Sigma
  using (_×_)
open import Encoding.Product
  using (dependent-encoding-product)
open import Encoding.Simple
  using (DependentSimpleEncoding; dependent-encoding-simple)
open import Encoding.Unit
  using (dependent-encoding-unit)

-- ## Dependent

dependent-simple-encoding-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleCategory C}
  → {A₁ A₂ : Set}
  → DependentSimpleEncoding C₁' A₁
  → DependentSimpleEncoding C₂' A₂
  → DependentSimpleEncoding
    (dependent-simple-category-product C₁' C₂')
    (A₁ × A₂)
dependent-simple-encoding-product e₁ e₂
  = dependent-encoding-simple
  $ dependent-encoding-product
    (dependent-encoding-unit e₁)
    (dependent-encoding-unit e₂)

