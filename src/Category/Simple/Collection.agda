module Category.Simple.Collection where

open import Category
  using (ChainCategory)
open import Category.Collection
  using (dependent-category-collection)
open import Category.Relation.Unit
  using (dependent-decidable-unit)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory; dependent-category-simple)
open import Category.Simple.Relation
  using (DependentRelation; DependentSimpleDecidable; DependentSimpleRelation)
open import Data.Collection
  using (Collection)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Dependent

-- ### DependentSet

dependent-set-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → DependentRelation C'
  → DependentSet C
dependent-set-collection {n = zero} R
  = Collection R
dependent-set-collection {n = suc _} R
  = record
  { tail
    = λ x → dependent-set-collection
      (DependentRelation.tail R x)
  }

-- ### DependentSimpleCategory

dependent-simple-category-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → DependentSimpleDecidable R
  → DependentSimpleCategory C
dependent-simple-category-collection d
  = dependent-category-simple
  $ dependent-category-collection
    (dependent-decidable-unit d)

