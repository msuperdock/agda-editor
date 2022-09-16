module Editor.Simple.Map.State where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSimpleCategory)
open import Data.Nat
  using (ℕ)
open import Editor.Simple
  using (DependentSimpleInnerEditor; DependentSimpleMainEditor;
    SimpleInnerEditor; SimpleMainEditor)
open import Encoding
  using (Encoding)
open import Encoding.Simple.State.Compose
  using (dependent-simple-state-encoding-compose)
open import Stack
  using (EventStack; ViewStack)

-- ## Dependent

-- ### DependentSimpleMainEditor

dependent-simple-main-editor-map-state
  : {V : ViewStack}
  → {E : EventStack}
  → {S T : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → Encoding S T
  → DependentSimpleMainEditor V E S C
  → DependentSimpleMainEditor V E T C
dependent-simple-main-editor-map-state e e'
  = record
  { DependentSimpleMainEditor e'
  ; state-encoding
    = dependent-simple-state-encoding-compose e
      (DependentSimpleMainEditor.state-encoding e')
  }

-- ### DependentSimpleInnerEditor

dependent-simple-inner-editor-map-state
  : {V : ViewStack}
  → {E : EventStack}
  → {S T P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → Encoding S T
  → DependentSimpleInnerEditor V E S P C'
  → DependentSimpleInnerEditor V E T P C'
dependent-simple-inner-editor-map-state e e'
  = record
  { DependentSimpleInnerEditor e'
  ; state-encoding
    = dependent-simple-state-encoding-compose e
      (DependentSimpleInnerEditor.state-encoding e')
  }

-- ## Nondependent

-- ### SimpleMainEditor

simple-main-editor-map-state
  : {V : ViewStack}
  → {E : EventStack}
  → {S T : Set}
  → Encoding S T
  → SimpleMainEditor V E S
  → SimpleMainEditor V E T
simple-main-editor-map-state
  = dependent-simple-main-editor-map-state

-- ### SimpleInnerEditor

simple-inner-editor-map-state
  : {V : ViewStack}
  → {E : EventStack}
  → {S T P A : Set}
  → Encoding S T
  → SimpleInnerEditor V E S P A
  → SimpleInnerEditor V E T P A
simple-inner-editor-map-state
  = dependent-simple-inner-editor-map-state

