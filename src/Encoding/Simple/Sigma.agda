module Encoding.Simple.Sigma where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Sigma
  using (dependent-simple-category-sigma)
open import Category.Snoc
  using (chain-category-snoc)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)
open import Data.Sigma
  using (_×_)
open import Encoding
  using (DependentEncoding)
open import Encoding.Sigma
  using (dependent-encoding-sigma)
open import Encoding.Simple
  using (DependentSimpleEncoding; dependent-encoding-simple)
open import Encoding.Unit
  using (dependent-encoding-unit)

-- ## Dependent

dependent-simple-encoding-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentSimpleCategory (chain-category-snoc C₁')}
  → {A₁ A₂ : Set}
  → DependentEncoding C₁' A₁
  → DependentSimpleEncoding C₂' A₂
  → DependentSimpleEncoding
    (dependent-simple-category-sigma C₁' C₂')
    (A₁ × A₂)
dependent-simple-encoding-sigma e₁ e₂
  = dependent-encoding-simple
  $ dependent-encoding-sigma e₁
    (dependent-encoding-unit e₂)

