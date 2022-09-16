module Category.Simple.List where

open import Category
  using (ChainCategory)
open import Category.List
  using (dependent-category-list)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory; dependent-category-simple)
open import Category.Unit
  using (dependent-category-unit)
open import Data.Function
  using (_$_)
open import Data.List
  using (List)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Dependent

-- ### DependentSet

dependent-set-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSet C
  → DependentSet C
dependent-set-list {n = zero} C'
  = List C'
dependent-set-list {n = suc _} C'
  = record
  { tail
    = λ x → dependent-set-list
      (DependentSet.tail C' x)
  }

-- ### DependentSimpleCategory

dependent-simple-category-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentSimpleCategory C
dependent-simple-category-list C'
  = dependent-category-simple
  $ dependent-category-list
    (dependent-category-unit C')

