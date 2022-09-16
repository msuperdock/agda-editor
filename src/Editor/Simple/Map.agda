module Editor.Simple.Map where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory)
open import Category.Simple.Partial
  using (DependentSimplePartialFunction')
open import Category.Simple.Partial.Compose
  using (dependent-simple-partial-function-compose)
open import Category.Simple.Split
  using (DependentSimpleSplitFunctor'; SimpleSplitFunctor')
open import Category.Simple.Split.Compose
  using (dependent-simple-split-functor-compose)
open import Data.Maybe
  using (Maybe)
open import Data.Nat
  using (ℕ)
open import Editor.Simple
  using (DependentSimpleInnerEditor; DependentSimplePartialEditor;
    DependentSimpleSplitEditor; SimpleInnerEditor; SimplePartialEditor;
    SimpleSplitEditor)
open import Encoding.Simple.Compose
  using (dependent-simple-encoding-compose')
open import Stack
  using (EventStack; ViewStack)

-- ## Dependent

-- ### DependentSimplePartialEditor

dependent-simple-partial-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentSet C}
  → DependentSimplePartialFunction' C' D'
  → DependentSimplePartialEditor V E C'
  → DependentSimplePartialEditor V E D'
dependent-simple-partial-editor-map F e
  = record
  { DependentSimplePartialEditor e
  ; partial-function
    = dependent-simple-partial-function-compose F
      (DependentSimplePartialEditor.partial-function e)
  }

-- ### DependentSimpleSplitEditor

dependent-simple-split-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor' C' D'
  → DependentSimpleSplitEditor V E C'
  → DependentSimpleSplitEditor V E D'
dependent-simple-split-editor-map F e
  = record
  { DependentSimpleSplitEditor e
  ; split-functor
    = dependent-simple-split-functor-compose F
      (DependentSimpleSplitEditor.split-functor e)
  }

-- ### DependentSimpleInnerEditor

dependent-simple-inner-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor' C' D'
  → DependentSimpleInnerEditor V E S P C'
  → DependentSimpleInnerEditor V E S P D'
dependent-simple-inner-editor-map F e
  = record
  { DependentSimpleInnerEditor e
  ; encoding
    = dependent-simple-encoding-compose' F
      (DependentSimpleInnerEditor.encoding e)
  ; split-functor
    = dependent-simple-split-functor-compose F
      (DependentSimpleInnerEditor.split-functor e)
  }

-- ## Nondependent

-- ### SimplePartialEditor

simple-partial-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {A B : Set}
  → (A → Maybe B)
  → SimplePartialEditor V E A
  → SimplePartialEditor V E B
simple-partial-editor-map
  = dependent-simple-partial-editor-map

-- ### SimpleSplitEditor

simple-split-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {A B : Set}
  → SimpleSplitFunctor' A B
  → SimpleSplitEditor V E A
  → SimpleSplitEditor V E B
simple-split-editor-map
  = dependent-simple-split-editor-map

-- ### SimpleInnerEditor

simple-inner-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {S P A B : Set}
  → SimpleSplitFunctor' A B
  → SimpleInnerEditor V E S P A
  → SimpleInnerEditor V E S P B
simple-inner-editor-map
  = dependent-simple-inner-editor-map

