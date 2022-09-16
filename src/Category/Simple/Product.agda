module Category.Simple.Product where

open import Category
  using (ChainCategory)
open import Category.Product
  using (dependent-category-product)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory; dependent-category-simple)
open import Category.Unit
  using (dependent-category-unit)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (_×_)

-- ## Dependent

-- ### DependentSet

dependent-set-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSet C
  → DependentSet C
  → DependentSet C
dependent-set-product {n = zero} C₁' C₂'
  = C₁' × C₂'
dependent-set-product {n = suc _} C₁' C₂'
  = record
  { tail
    = λ x → dependent-set-product
      (DependentSet.tail C₁' x)
      (DependentSet.tail C₂' x)
  }

-- ### DependentSimpleCategory

dependent-simple-category-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentSimpleCategory C
  → DependentSimpleCategory C
dependent-simple-category-product C₁' C₂'
  = dependent-category-simple
  $ dependent-category-product
    (dependent-category-unit C₁')
    (dependent-category-unit C₂')

