module Editor.Simple.Map.Event where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Data.Function
  using (_∘_)
open import Data.Nat
  using (ℕ; suc; zero)
open import Editor.Map.Event
  using (editor-map-event)
open import Editor.Simple
  using (DependentSimpleEditor; DependentSimpleInnerEditor;
    DependentSimpleMainEditor; DependentSimplePartialEditor;
    DependentSimpleSplitEditor; SimpleEditor; SimpleInnerEditor;
    SimpleMainEditor; SimplePartialEditor; SimpleSplitEditor; editor-simple)
open import Editor.Unit
  using (editor-unit)
open import Stack
  using (EventStack; EventStackMap; ViewStack)

-- ## Base

-- ### SimpleEditor

simple-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {A : Set}
  → EventStackMap E F
  → SimpleEditor V E A
  → SimpleEditor V F A
simple-editor-map-event G
  = editor-simple
  ∘ editor-map-event G
  ∘ editor-unit

-- ## Dependent

-- ### DependentSimpleEditor

dependent-simple-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → EventStackMap E F
  → DependentSimpleEditor V E C'
  → DependentSimpleEditor V F C'
dependent-simple-editor-map-event {n = zero} G e
  = simple-editor-map-event G e
dependent-simple-editor-map-event {n = suc _} G e
  = record
  { tail
    = λ x → dependent-simple-editor-map-event G
      (DependentSimpleEditor.tail e x)
  }

-- ### DependentSimplePartialEditor

dependent-simple-partial-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → EventStackMap E F
  → DependentSimplePartialEditor V E C'
  → DependentSimplePartialEditor V F C'
dependent-simple-partial-editor-map-event G e
  = record
  { DependentSimplePartialEditor e
  ; editor
    = dependent-simple-editor-map-event G
      (DependentSimplePartialEditor.editor e)
  }

-- ### DependentSimpleSplitEditor

dependent-simple-split-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → EventStackMap E F
  → DependentSimpleSplitEditor V E C'
  → DependentSimpleSplitEditor V F C'
dependent-simple-split-editor-map-event G e
  = record
  { DependentSimpleSplitEditor e
  ; editor
    = dependent-simple-editor-map-event G
      (DependentSimpleSplitEditor.editor e)
  }

-- ### DependentSimpleMainEditor

dependent-simple-main-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {S : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → EventStackMap E F
  → DependentSimpleMainEditor V E S C
  → DependentSimpleMainEditor V F S C
dependent-simple-main-editor-map-event G e
  = record
  { DependentSimpleMainEditor e
  ; editor
    = dependent-simple-editor-map-event G
      (DependentSimpleMainEditor.editor e)
  }

-- ### DependentSimpleInnerEditor

dependent-simple-inner-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {S P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → EventStackMap E F
  → DependentSimpleInnerEditor V E S P C'
  → DependentSimpleInnerEditor V F S P C'
dependent-simple-inner-editor-map-event G e
  = record
  { DependentSimpleInnerEditor e
  ; editor
    = dependent-simple-editor-map-event G
      (DependentSimpleInnerEditor.editor e)
  }

-- ## Nondependent

-- ### SimplePartialEditor

simple-partial-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {A : Set}
  → EventStackMap E F
  → SimplePartialEditor V E A
  → SimplePartialEditor V F A
simple-partial-editor-map-event
  = dependent-simple-partial-editor-map-event

-- ### SimpleSplitEditor

simple-split-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {A : Set}
  → EventStackMap E F
  → SimpleSplitEditor V E A
  → SimpleSplitEditor V F A
simple-split-editor-map-event
  = dependent-simple-split-editor-map-event

-- ### SimpleMainEditor

simple-main-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {S : Set}
  → EventStackMap E F
  → SimpleMainEditor V E S
  → SimpleMainEditor V F S
simple-main-editor-map-event
  = dependent-simple-main-editor-map-event

-- ### SimpleInnerEditor

simple-inner-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {S P A : Set}
  → EventStackMap E F
  → SimpleInnerEditor V E S P A
  → SimpleInnerEditor V F S P A
simple-inner-editor-map-event
  = dependent-simple-inner-editor-map-event

