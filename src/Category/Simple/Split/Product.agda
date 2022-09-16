module Category.Simple.Split.Product where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Product
  using (dependent-simple-category-product)
open import Category.Simple.Split
  using (DependentSimpleSplitFunctor; dependent-split-functor-simple)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.Product
  using (dependent-simple-state-category-product)
open import Category.Split.Product
  using (dependent-split-functor-product)
open import Category.Split.Unit
  using (dependent-split-functor-unit)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-simple-split-functor-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleStateCategory C}
  → {D₁' D₂' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor C₁' D₁'
  → DependentSimpleSplitFunctor C₂' D₂'
  → DependentSimpleSplitFunctor
    (dependent-simple-state-category-product C₁' C₂')
    (dependent-simple-category-product D₁' D₂')
dependent-simple-split-functor-product F₁ F₂
  = dependent-split-functor-simple
  $ dependent-split-functor-product
    (dependent-split-functor-unit F₁)
    (dependent-split-functor-unit F₂)

