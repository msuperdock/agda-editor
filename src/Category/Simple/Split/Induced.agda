module Category.Simple.Split.Induced where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSimpleCategory; DependentSimplePrecategory;
    DependentSimplePrecategory')
open import Category.Simple.Induced
  using (dependent-simple-category-induced; dependent-simple-category-induced')
open import Category.Simple.Split
  using (DependentSimpleSplitFunctor; DependentSimpleSplitFunctor';
    DependentSimpleSplitPrefunctor; DependentSimpleSplitPrefunctor')
open import Category.Simple.Split.Lift.Induced
  using (dependent-simple-split-lift-induced;
    dependent-simple-split-lift-induced')
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Data.Nat
  using (ℕ)

-- ## Dependent

-- ### DependentSimpleSplitFunctor

dependent-simple-split-functor-induced
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → {D' : DependentSimplePrecategory C}
  → (F : DependentSimpleSplitPrefunctor C' D')
  → DependentSimpleSplitFunctor C'
    (dependent-simple-category-induced F)
dependent-simple-split-functor-induced F
  = record
  { lift
    = dependent-simple-split-lift-induced
      (DependentSimpleSplitPrefunctor.lift F)
  }

-- ### DependentSimpleSplitFunctor'

dependent-simple-split-functor-induced'
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimplePrecategory' C}
  → (F : DependentSimpleSplitPrefunctor' C' D')
  → DependentSimpleSplitFunctor' C'
    (dependent-simple-category-induced' F)
dependent-simple-split-functor-induced' F
  = record
  { lift
    = dependent-simple-split-lift-induced'
      (DependentSimpleSplitPrefunctor'.lift F)
  }

