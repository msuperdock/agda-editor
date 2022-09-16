module Editor.Map.Pure where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Data.Nat
  using (ℕ)
open import Editor
  using (DependentInnerEditor; InnerEditor)
open import Encoding
  using (Encoding)
open import Encoding.Compose
  using (dependent-encoding-compose)
open import Stack
  using (EventStack; ViewStack)

-- ## Dependent

-- ### DependentInnerEditor

dependent-inner-editor-map-pure
  : {V : ViewStack}
  → {E : EventStack}
  → {S P Q : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → Encoding P Q
  → DependentInnerEditor V E S P C'
  → DependentInnerEditor V E S Q C'
dependent-inner-editor-map-pure e e'
  = record
  { DependentInnerEditor e'
  ; encoding
    = dependent-encoding-compose e
      (DependentInnerEditor.encoding e')
  }

-- ## Nondependent

-- ### InnerEditor

inner-editor-map-pure
  : {V : ViewStack}
  → {E : EventStack}
  → {S P Q : Set}
  → {C : Category}
  → Encoding P Q
  → InnerEditor V E S P C
  → InnerEditor V E S Q C
inner-editor-map-pure
  = dependent-inner-editor-map-pure

