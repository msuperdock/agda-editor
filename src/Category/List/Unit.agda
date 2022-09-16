module Category.List.Unit where

open import Category
  using (Category; ChainCategory; DependentCategory; DependentPrecategory')
open import Category.Core.List.Unit
  using (dependent-compose-list-unit; dependent-identity-list-unit)
open import Category.Induced
  using (dependent-category-induced')
open import Category.Lift.List.Unit
  using (dependent-prelift-list-unit)
open import Category.List
  using (dependent-category-list)
open import Category.Simple
  using (DependentSimpleCategory; simple-category)
open import Category.Split
  using (DependentSplitPrefunctor')
open import Category.Split.Core.List.Unit
  using (dependent-split-compose-list-unit; dependent-split-identity-list-unit)
open import Category.Split.Lift.List.Unit
  using (dependent-split-prelift-list-unit)
open import Category.Unit
  using (dependent-category-unit)
open import Data.Nat
  using (ℕ)

-- ## Dependent

-- ### DependentPrecategory'

dependent-precategory-list-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentPrecategory' C
dependent-precategory-list-unit C'
  = record
  { identity
    = dependent-identity-list-unit X
  ; compose
    = dependent-compose-list-unit X X X
  ; lift
    = dependent-prelift-list-unit
      (DependentSimpleCategory.lift C')
  }
  where
    X = DependentSimpleCategory.object C'

-- ### DependentSplitPrefunctor'

dependent-split-prefunctor-list-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C' : DependentSimpleCategory C)
  → DependentSplitPrefunctor'
    (dependent-category-list
      (dependent-category-unit C'))
    (dependent-precategory-list-unit C')
dependent-split-prefunctor-list-unit C'
  = record
  { identity
    = dependent-split-identity-list-unit X
  ; compose
    = dependent-split-compose-list-unit X X X
  ; lift
    = dependent-split-prelift-list-unit l
  }
  where
    X = DependentSimpleCategory.object C'
    l = DependentSimpleCategory.lift C'

-- ### DependentCategory

dependent-category-list-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentCategory C
dependent-category-list-unit C'
  = dependent-category-induced'
    (dependent-split-prefunctor-list-unit C')

-- ## Nondependent

-- ### Category

category-list-unit
  : Set
  → Category
category-list-unit A
  = dependent-category-list-unit
    (simple-category A)

