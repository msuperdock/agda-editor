module Category.Simple.Induced where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSimpleCategory; DependentSimplePrecategory;
    DependentSimplePrecategory')
open import Category.Simple.Lift.Induced
  using (dependent-simple-lift-induced; dependent-simple-lift-induced')
open import Category.Simple.Split
  using (DependentSimpleSplitPrefunctor; DependentSimpleSplitPrefunctor')
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Data.Nat
  using (ℕ)

-- ## Dependent

-- ### DependentSimpleCategory

dependent-simple-category-induced
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → {D' : DependentSimplePrecategory C}
  → DependentSimpleSplitPrefunctor C' D'
  → DependentSimpleCategory C
dependent-simple-category-induced F
  = record
  { lift
    = dependent-simple-lift-induced
      (DependentSimpleSplitPrefunctor.lift F)
  }

-- ### DependentSimpleCategory'

dependent-simple-category-induced'
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimplePrecategory' C}
  → DependentSimpleSplitPrefunctor' C' D'
  → DependentSimpleCategory C
dependent-simple-category-induced' F
  = record
  { lift
    = dependent-simple-lift-induced'
      (DependentSimpleSplitPrefunctor'.lift F)
  }

