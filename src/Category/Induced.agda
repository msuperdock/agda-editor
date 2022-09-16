module Category.Induced where

open import Category
  using (Category; ChainCategory; DependentCategory; DependentPrecategory;
    DependentPrecategory'; Precategory; Precategory')
open import Category.Core.Induced
  using (dependent-associative-induced; dependent-compose-equal-induced;
    dependent-postcompose-induced; dependent-precompose-induced)
open import Category.Lift.Induced
  using (dependent-lift-induced; dependent-lift-induced')
open import Category.Split
  using (DependentSplitPrefunctor; DependentSplitPrefunctor'; SplitPrefunctor;
    SplitPrefunctor')
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Data.Nat
  using (ℕ)

-- ## Dependent

-- ### DependentCategory

dependent-category-induced
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → {D' : DependentPrecategory C}
  → DependentSplitPrefunctor C' D'
  → DependentCategory C
dependent-category-induced {C' = C'} F
  = record
  { compose-equal
    = dependent-compose-equal-induced
      (DependentStateCategory.compose-equal C')
      (DependentSplitPrefunctor.compose F)
  ; precompose
    = dependent-precompose-induced
      (DependentStateCategory.compose-equal C')
      (DependentStateCategory.precompose C')
      (DependentSplitPrefunctor.identity F)
      (DependentSplitPrefunctor.compose F)
  ; postcompose
    = dependent-postcompose-induced
      (DependentStateCategory.compose-equal C')
      (DependentStateCategory.postcompose C')
      (DependentSplitPrefunctor.identity F)
      (DependentSplitPrefunctor.compose F)
  ; associative
    = dependent-associative-induced
      (DependentStateCategory.compose-equal C')
      (DependentStateCategory.compose-equal C')
      (DependentStateCategory.associative C')
      (DependentSplitPrefunctor.compose F)
      (DependentSplitPrefunctor.compose F)
      (DependentSplitPrefunctor.compose F)
      (DependentSplitPrefunctor.compose F)
  ; lift
    = dependent-lift-induced
      (DependentSplitPrefunctor.identity F)
      (DependentSplitPrefunctor.lift F)
  }

-- ### DependentCategory'

dependent-category-induced'
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentPrecategory' C}
  → DependentSplitPrefunctor' C' D'
  → DependentCategory C
dependent-category-induced' {C' = C'} F
  = record
  { compose-equal
    = dependent-compose-equal-induced
      (DependentCategory.compose-equal C')
      (DependentSplitPrefunctor'.compose F)
  ; precompose
    = dependent-precompose-induced
      (DependentCategory.compose-equal C')
      (DependentCategory.precompose C')
      (DependentSplitPrefunctor'.identity F)
      (DependentSplitPrefunctor'.compose F)
  ; postcompose
    = dependent-postcompose-induced
      (DependentCategory.compose-equal C')
      (DependentCategory.postcompose C')
      (DependentSplitPrefunctor'.identity F)
      (DependentSplitPrefunctor'.compose F)
  ; associative
    = dependent-associative-induced
      (DependentCategory.compose-equal C')
      (DependentCategory.compose-equal C')
      (DependentCategory.associative C')
      (DependentSplitPrefunctor'.compose F)
      (DependentSplitPrefunctor'.compose F)
      (DependentSplitPrefunctor'.compose F)
      (DependentSplitPrefunctor'.compose F)
  ; lift
    = dependent-lift-induced'
      (DependentCategory.compose-equal C')
      (DependentSplitPrefunctor'.identity F)
      (DependentSplitPrefunctor'.compose F)
      (DependentSplitPrefunctor'.lift F)
  }

-- ## Nondependent

-- ### Category

category-induced
  : {C : StateCategory}
  → {D : Precategory}
  → SplitPrefunctor C D
  → Category
category-induced
  = dependent-category-induced

-- ### Category'

category-induced'
  : {C : Category}
  → {D : Precategory'}
  → SplitPrefunctor' C D
  → Category
category-induced'
  = dependent-category-induced'

