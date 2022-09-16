module Encoding.Simple.State.Sigma.Sum where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.Sigma.Sum
  using (dependent-simple-state-category-sigma-sum)
open import Category.Snoc
  using (chain-category-snoc)
open import Category.Split
  using (DependentSplitFunctor)
open import Category.State
  using (DependentStateCategory)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)
open import Data.Sigma
  using (_×_)
open import Data.Sum
  using (_⊔_)
open import Encoding
  using (DependentEncoding)
open import Encoding.Simple.State
  using (DependentSimpleStateEncoding; dependent-state-encoding-simple)
open import Encoding.State
  using (DependentStateEncoding)
open import Encoding.State.Sigma.Sum
  using (dependent-state-encoding-sigma-sum)
open import Encoding.State.Unit
  using (dependent-state-encoding-unit)

-- ## Dependent

dependent-simple-state-encoding-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentStateCategory C}
  → {D₁' : DependentCategory C}
  → {C₂' : DependentSimpleStateCategory (chain-category-snoc D₁')}
  → {A₁ A₂ B₁ : Set}
  → (F₁ : DependentSplitFunctor C₁' D₁')
  → DependentStateEncoding C₁' A₁
  → DependentEncoding D₁' B₁
  → DependentSimpleStateEncoding C₂' A₂
  → DependentSimpleStateEncoding
    (dependent-simple-state-category-sigma-sum C₂' F₁)
    (A₁ ⊔ B₁ × A₂)
dependent-simple-state-encoding-sigma-sum F₁ e₁ f₁ e₂
  = dependent-state-encoding-simple
  $ dependent-state-encoding-sigma-sum F₁ e₁ f₁
    (dependent-state-encoding-unit e₂)

