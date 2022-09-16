module Encoding.Simple.State.Product where

open import Category
  using (ChainCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.Product
  using (dependent-simple-state-category-product)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)
open import Data.Sigma
  using (_×_)
open import Encoding.Simple.State
  using (DependentSimpleStateEncoding; dependent-state-encoding-simple)
open import Encoding.State.Product
  using (dependent-state-encoding-product)
open import Encoding.State.Unit
  using (dependent-state-encoding-unit)

-- ## Dependent

dependent-simple-state-encoding-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleStateCategory C}
  → {A₁ A₂ : Set}
  → DependentSimpleStateEncoding C₁' A₁
  → DependentSimpleStateEncoding C₂' A₂
  → DependentSimpleStateEncoding
    (dependent-simple-state-category-product C₁' C₂')
    (A₁ × A₂)
dependent-simple-state-encoding-product e₁ e₂
  = dependent-state-encoding-simple
  $ dependent-state-encoding-product
    (dependent-state-encoding-unit e₁)
    (dependent-state-encoding-unit e₂)

