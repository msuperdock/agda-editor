module Category.Relation.Unit where

open import Category
  using (ChainCategory)
open import Category.Relation
  using (DependentDecidable; DependentRelation)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Relation
  using (DependentSimpleDecidable; DependentSimpleRelation)
open import Category.Unit
  using (dependent-category-unit)
open import Data.Nat
  using (ℕ)

-- ## Dependent

-- ### DependentRelation

dependent-relation-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → DependentSimpleRelation C'
  → DependentRelation
    (dependent-category-unit C')
dependent-relation-unit R
  = record {DependentSimpleRelation R}

-- ### DependentDecidable

dependent-decidable-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → DependentSimpleDecidable R
  → DependentDecidable
    (dependent-relation-unit R)
dependent-decidable-unit d
  = record {DependentSimpleDecidable d}

