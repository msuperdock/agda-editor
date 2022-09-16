module Category.Collection where

open import Category
  using (Category; ChainCategory; DependentCategory; DependentPrecategory')
open import Category.Core.Collection
  using (dependent-compose-collection; dependent-identity-collection)
open import Category.Induced
  using (dependent-category-induced')
open import Category.Lift.Collection
  using (dependent-prelift-collection)
open import Category.List
  using (dependent-category-list)
open import Category.Relation
  using (DependentDecidable; DependentRelation; decidable)
open import Category.Split
  using (DependentSplitPrefunctor')
open import Category.Split.Core.Collection
  using (dependent-split-compose-collection;
    dependent-split-identity-collection)
open import Category.Split.Lift.Collection
  using (dependent-split-prelift-collection)
open import Data.Nat
  using (ℕ)
open import Data.Relation
  using (Decidable; Relation)

-- ## Dependent

-- ### DependentPrecategory'

dependent-precategory-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {R : DependentRelation C'}
  → DependentDecidable R
  → DependentPrecategory' C
dependent-precategory-collection {C' = C'} {R = R} d
  = record
  { identity
    = dependent-identity-collection R'
      (DependentCategory.identity C')
  ; compose
    = dependent-compose-collection R' R' R'
      (DependentCategory.compose C')
  ; lift
    = dependent-prelift-collection d'
      (DependentCategory.lift C')
  }
  where
    R' = DependentRelation.object R
    d' = DependentDecidable.object d

-- ### DependentSplitPrefunctor'

dependent-split-prefunctor-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {R : DependentRelation C'}
  → (d : DependentDecidable R)
  → DependentSplitPrefunctor'
    (dependent-category-list C')
    (dependent-precategory-collection d)
dependent-split-prefunctor-collection {C' = C'} d
  = record
  { identity
    = dependent-split-identity-collection d'
      (DependentCategory.identity C')
  ; compose
    = dependent-split-compose-collection d' d' d'
      (DependentCategory.compose C')
  ; lift
    = dependent-split-prelift-collection d'
      (DependentCategory.lift C')
  }
  where
    d' = DependentDecidable.object d

-- ### DependentCategory

dependent-category-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {R : DependentRelation C'}
  → DependentDecidable R
  → DependentCategory C
dependent-category-collection d
  = dependent-category-induced'
    (dependent-split-prefunctor-collection d)

-- ## Nondependent

-- ### Category

category-collection
  : (C : Category)
  → (R : Relation (Category.Object C))
  → Decidable R
  → Category
category-collection C R d
  = dependent-category-collection (decidable C R d)

