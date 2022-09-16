module Editor.Map where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.Split
  using (DependentSplitFunctor'; SplitFunctor')
open import Category.Split.Compose
  using (dependent-split-functor-compose)
open import Data.Nat
  using (ℕ)
open import Editor
  using (DependentInnerEditor; DependentSplitEditor; DependentSplitEditor';
    InnerEditor; SplitEditor)
open import Encoding.Compose
  using (dependent-encoding-compose')
open import Stack
  using (EventStack; ViewStack)

-- ## Dependent

-- ### DependentSplitEditor

dependent-split-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentCategory C}
  → DependentSplitFunctor' C' D'
  → DependentSplitEditor V E C'
  → DependentSplitEditor V E D'
dependent-split-editor-map F e
  = record
  { DependentSplitEditor' e
  ; split-functor
    = dependent-split-functor-compose F
      (DependentSplitEditor.split-functor e)
  }

-- ### DependentInnerEditor

dependent-inner-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentCategory C}
  → DependentSplitFunctor' C' D'
  → DependentInnerEditor V E S P C'
  → DependentInnerEditor V E S P D'
dependent-inner-editor-map F e
  = record
  { DependentInnerEditor e
  ; encoding
    = dependent-encoding-compose' F
      (DependentInnerEditor.encoding e)
  ; split-functor
    = dependent-split-functor-compose F
      (DependentInnerEditor.split-functor e)
  }

-- ## Nondependent

-- ### SplitEditor

split-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {C D : Category}
  → SplitFunctor' C D
  → SplitEditor V E C
  → SplitEditor V E D
split-editor-map
  = dependent-split-editor-map

-- ### InnerEditor

inner-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C D : Category}
  → SplitFunctor' C D
  → InnerEditor V E S P C
  → InnerEditor V E S P D
inner-editor-map
  = dependent-inner-editor-map

