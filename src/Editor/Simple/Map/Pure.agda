module Editor.Simple.Map.Pure where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSimpleCategory)
open import Data.Nat
  using (ℕ)
open import Editor.Simple
  using (DependentSimpleInnerEditor; SimpleInnerEditor)
open import Encoding
  using (Encoding)
open import Encoding.Simple.Compose
  using (dependent-simple-encoding-compose)
open import Stack
  using (EventStack; ViewStack)

-- ## Dependent

-- ### DependentSimpleInnerEditor

dependent-simple-inner-editor-map-pure
  : {V : ViewStack}
  → {E : EventStack}
  → {S P Q : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → Encoding P Q
  → DependentSimpleInnerEditor V E S P C'
  → DependentSimpleInnerEditor V E S Q C'
dependent-simple-inner-editor-map-pure e e'
  = record
  { DependentSimpleInnerEditor e'
  ; encoding
    = dependent-simple-encoding-compose e
      (DependentSimpleInnerEditor.encoding e')
  }

-- ## Nondependent

-- ### SimpleInnerEditor

simple-inner-editor-map-pure
  : {V : ViewStack}
  → {E : EventStack}
  → {S P Q A : Set}
  → Encoding P Q
  → SimpleInnerEditor V E S P A
  → SimpleInnerEditor V E S Q A
simple-inner-editor-map-pure
  = dependent-simple-inner-editor-map-pure

