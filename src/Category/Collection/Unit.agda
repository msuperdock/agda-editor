module Category.Collection.Unit where

open import Category
  using (Category; ChainCategory; DependentCategory; DependentPrecategory')
open import Category.Core.Collection.Unit
  using (dependent-compose-collection-unit; dependent-identity-collection-unit)
open import Category.Induced
  using (dependent-category-induced')
open import Category.Lift.Collection.Unit
  using (dependent-prelift-collection-unit)
open import Category.List.Unit
  using (dependent-category-list-unit)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Relation
  using (DependentSimpleDecidable; DependentSimpleRelation; simple-decidable)
open import Category.Split
  using (DependentSplitPrefunctor')
open import Category.Split.Core.Collection.Unit
  using (dependent-split-compose-collection-unit;
    dependent-split-identity-collection-unit)
open import Category.Split.Lift.Collection.Unit
  using (dependent-split-prelift-collection-unit)
open import Data.Nat
  using (ℕ)
open import Data.Relation
  using (Decidable; Relation)

-- ## Dependent

-- ### DependentPrecategory'

dependent-precategory-collection-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → DependentSimpleDecidable R
  → DependentPrecategory' C
dependent-precategory-collection-unit {C' = C'} {R = R} d
  = record
  { identity
    = dependent-identity-collection-unit R'
  ; compose
    = dependent-compose-collection-unit R' R' R'
  ; lift
    = dependent-prelift-collection-unit d'
      (DependentSimpleCategory.lift C')
  }
  where
    R' = DependentSimpleRelation.object R
    d' = DependentSimpleDecidable.object d

-- ### DependentSplitPrefunctor'

dependent-split-prefunctor-collection-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → (d : DependentSimpleDecidable R)
  → DependentSplitPrefunctor'
    (dependent-category-list-unit C')
    (dependent-precategory-collection-unit d)
dependent-split-prefunctor-collection-unit {C' = C'} d
  = record
  { identity
    = dependent-split-identity-collection-unit d'
  ; compose
    = dependent-split-compose-collection-unit d' d' d'
  ; lift
    = dependent-split-prelift-collection-unit C' d'
  }
  where
    d' = DependentSimpleDecidable.object d

-- ### DependentCategory

dependent-category-collection-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → DependentSimpleDecidable R
  → DependentCategory C
dependent-category-collection-unit d
  = dependent-category-induced'
    (dependent-split-prefunctor-collection-unit d)

-- ## Nondependent

-- ### Category

category-collection-unit
  : {A : Set}
  → (R : Relation A)
  → Decidable R
  → Category
category-collection-unit R d
  = dependent-category-collection-unit (simple-decidable R d)

