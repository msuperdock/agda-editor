module Category.Simple.Partial.Collection where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSet)
open import Category.Simple.Collection
  using (dependent-set-collection)
open import Category.Simple.List
  using (dependent-set-list)
open import Category.Simple.Partial
  using (DependentSimplePartialFunction')
open import Category.Simple.Relation
  using (DependentDecidable; DependentRelation)
open import Data.Collection
  using (Collection)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Dependent

dependent-simple-partial-function-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → {R : DependentRelation C'}
  → DependentDecidable C' R
  → DependentSimplePartialFunction'
    (dependent-set-list C')
    (dependent-set-collection R)
dependent-simple-partial-function-collection {n = zero} {R = R} d
  = Collection.from-list R d
dependent-simple-partial-function-collection {n = suc _} d
  = record
  { tail
    = λ x → dependent-simple-partial-function-collection
      (DependentDecidable.tail d x)
  }

