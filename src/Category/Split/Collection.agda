module Category.Split.Collection where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Collection
  using (dependent-category-collection; dependent-split-prefunctor-collection)
open import Category.List
  using (dependent-category-list)
open import Category.Relation
  using (DependentDecidable; DependentRelation)
open import Category.Split
  using (DependentSplitFunctor')
open import Category.Split.Induced
  using (dependent-split-functor-induced')
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-split-functor-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {R : DependentRelation C'}
  → (d : DependentDecidable R)
  → DependentSplitFunctor'
    (dependent-category-list C')
    (dependent-category-collection d)
dependent-split-functor-collection d
  = dependent-split-functor-induced'
    (dependent-split-prefunctor-collection d)

