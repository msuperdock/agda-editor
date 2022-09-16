module Editor.Map.State where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Data.Nat
  using (ℕ)
open import Editor
  using (DependentInnerEditor; InnerEditor)
open import Encoding
  using (Encoding)
open import Encoding.State.Compose
  using (dependent-state-encoding-compose)
open import Stack
  using (EventStack; ViewStack)

-- ## Dependent

-- ### DependentInnerEditor

dependent-inner-editor-map-state
  : {V : ViewStack}
  → {E : EventStack}
  → {S T P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → Encoding S T
  → DependentInnerEditor V E S P C'
  → DependentInnerEditor V E T P C'
dependent-inner-editor-map-state e e'
  = record
  { DependentInnerEditor e'
  ; state-encoding
    = dependent-state-encoding-compose e
      (DependentInnerEditor.state-encoding e')
  }

-- ## Nondependent

-- ### InnerEditor

inner-editor-map-state
  : {V : ViewStack}
  → {E : EventStack}
  → {S T P : Set}
  → {C : Category}
  → Encoding S T
  → InnerEditor V E S P C
  → InnerEditor V E T P C
inner-editor-map-state
  = dependent-inner-editor-map-state

