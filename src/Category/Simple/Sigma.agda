module Category.Simple.Sigma where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.Sigma
  using (dependent-category-sigma)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory; dependent-category-simple)
open import Category.Snoc
  using (chain-category-snoc)
open import Category.Unit
  using (dependent-category-unit)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ)

-- ## Dependent

-- ### DependentSet

dependent-set-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C₁' : DependentCategory C)
  → DependentSet (chain-category-snoc C₁')
  → DependentSet C
dependent-set-sigma {n = zero} C₁' C₂'
  = Σ (Category.Object C₁') (DependentSet.tail C₂')
dependent-set-sigma {n = suc _} C₁' C₂'
  = record
  { tail
    = λ x → dependent-set-sigma
      (DependentCategory.tail C₁' x)
      (DependentSet.tail C₂' x)
  }

-- ### DependentSimpleCategory

dependent-simple-category-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C₁' : DependentCategory C)
  → DependentSimpleCategory (chain-category-snoc C₁')
  → DependentSimpleCategory C
dependent-simple-category-sigma C₁' C₂'
  = dependent-category-simple
  $ dependent-category-sigma C₁'
    (dependent-category-unit C₂')

