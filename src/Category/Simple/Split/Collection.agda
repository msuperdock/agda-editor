module Category.Simple.Split.Collection where

open import Category
  using (ChainCategory)
open import Category.Relation.Unit
  using (dependent-decidable-unit)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Collection
  using (dependent-simple-category-collection)
open import Category.Simple.List
  using (dependent-simple-category-list)
open import Category.Simple.Relation
  using (DependentSimpleDecidable; DependentSimpleRelation)
open import Category.Simple.Split
  using (DependentSimpleSplitFunctor'; dependent-split-functor-simple')
open import Category.Split.Collection
  using (dependent-split-functor-collection)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-simple-split-functor-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → (d : DependentSimpleDecidable R)
  → DependentSimpleSplitFunctor'
    (dependent-simple-category-list C')
    (dependent-simple-category-collection d)
dependent-simple-split-functor-collection d
  = dependent-split-functor-simple'
  $ dependent-split-functor-collection
    (dependent-decidable-unit d)

