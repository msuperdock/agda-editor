module Category.Split.Collection.Unit where

open import Category
  using (ChainCategory)
open import Category.Collection.Unit
  using (dependent-category-collection-unit;
    dependent-split-prefunctor-collection-unit)
open import Category.List.Unit
  using (dependent-category-list-unit)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Relation
  using (DependentSimpleDecidable; DependentSimpleRelation)
open import Category.Split
  using (DependentSplitFunctor')
open import Category.Split.Induced
  using (dependent-split-functor-induced')
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-split-functor-collection-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → (d : DependentSimpleDecidable R)
  → DependentSplitFunctor'
    (dependent-category-list-unit C')
    (dependent-category-collection-unit d)
dependent-split-functor-collection-unit d
  = dependent-split-functor-induced'
    (dependent-split-prefunctor-collection-unit d)

