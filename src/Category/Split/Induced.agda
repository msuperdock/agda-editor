module Category.Split.Induced where

open import Category
  using (Category; ChainCategory; DependentCategory; DependentPrecategory;
    DependentPrecategory'; Precategory; Precategory')
open import Category.Induced
  using (category-induced; category-induced'; dependent-category-induced;
    dependent-category-induced')
open import Category.Split
  using (DependentSplitFunctor; DependentSplitFunctor';
    DependentSplitPrefunctor; DependentSplitPrefunctor'; SplitFunctor;
    SplitFunctor'; SplitPrefunctor; SplitPrefunctor')
open import Category.Split.Lift.Induced
  using (dependent-split-lift-induced; dependent-split-lift-induced')
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Data.Nat
  using (ℕ)

-- ## Dependent

-- ### DependentSplitFunctor

dependent-split-functor-induced
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → {D' : DependentPrecategory C}
  → (F : DependentSplitPrefunctor C' D')
  → DependentSplitFunctor C'
    (dependent-category-induced F)
dependent-split-functor-induced F
  = record
  { DependentSplitPrefunctor F
  ; lift
    = dependent-split-lift-induced
      (DependentSplitPrefunctor.identity F)
      (DependentSplitPrefunctor.lift F)
  }

-- ### DependentSplitFunctor'

dependent-split-functor-induced'
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentPrecategory' C}
  → (F : DependentSplitPrefunctor' C' D')
  → DependentSplitFunctor' C'
    (dependent-category-induced' F)
dependent-split-functor-induced' {C' = C'} F
  = record
  { DependentSplitPrefunctor' F
  ; lift
    = dependent-split-lift-induced'
      (DependentCategory.compose-equal C')
      (DependentSplitPrefunctor'.identity F)
      (DependentSplitPrefunctor'.compose F)
      (DependentSplitPrefunctor'.lift F)
  }

-- ## Nondependent

-- ### SplitFunctor

split-functor-induced
  : {C : StateCategory}
  → {D : Precategory}
  → (F : SplitPrefunctor C D)
  → SplitFunctor C
    (category-induced F)
split-functor-induced
  = dependent-split-functor-induced

-- ### SplitFunctor'

split-functor-induced'
  : {C : Category}
  → {D : Precategory'}
  → (F : SplitPrefunctor' C D)
  → SplitFunctor' C
    (category-induced' F)
split-functor-induced'
  = dependent-split-functor-induced'

