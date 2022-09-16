module Editor.Map.Event where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Data.Nat
  using (ℕ; suc; zero)
open import Editor as _
  using (DependentEditor; DependentInnerEditor; DependentSplitEditor;
    DependentSplitEditor'; Editor; InnerEditor; SplitEditor)
open import Stack
  using (EventStack; EventStackMap; ViewStack)

-- ## Base

-- ### Editor

editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {C : StateCategory}
  → EventStackMap E F
  → Editor V E C
  → Editor V F C
editor-map-event G e
  = record
  { Editor e
  ; mode
    = λ s sp → EventStackMap.mode G
      (Editor.mode e s sp)
  ; mode-inner
    = λ s sp s' sp' → EventStackMap.mode-inner G
      (Editor.mode-inner e s sp s' sp')
  ; handle
    = λ s sp e' → Editor.handle e s sp
      (EventStackMap.event G (Editor.mode e s sp) e')
  ; handle-inner
    = λ s sp s' sp' e' → Editor.handle-inner e s sp s' sp'
      (EventStackMap.event-inner G (Editor.mode-inner e s sp s' sp') e')
  }

-- ## Dependent

-- ### DependentEditor

dependent-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → EventStackMap E F
  → DependentEditor V E C'
  → DependentEditor V F C'
dependent-editor-map-event {n = zero} G e
  = editor-map-event G e
dependent-editor-map-event {n = suc _} G e
  = record
  { tail
    = λ x → dependent-editor-map-event G
      (DependentEditor.tail e x)
  }

-- ### DependentSplitEditor

dependent-split-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → EventStackMap E F
  → DependentSplitEditor V E C'
  → DependentSplitEditor V F C'
dependent-split-editor-map-event G e
  = record
  { DependentSplitEditor' e
  ; editor
    = dependent-editor-map-event G
      (DependentSplitEditor.editor e)
  }

-- ### DependentInnerEditor

dependent-inner-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {S P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → EventStackMap E F
  → DependentInnerEditor V E S P C'
  → DependentInnerEditor V F S P C'
dependent-inner-editor-map-event G e
  = record
  { DependentInnerEditor e
  ; editor
    = dependent-editor-map-event G
      (DependentInnerEditor.editor e)
  }

-- ## Nondependent

-- ### SplitEditor

split-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {C : Category}
  → EventStackMap E F
  → SplitEditor V E C
  → SplitEditor V F C
split-editor-map-event
  = dependent-split-editor-map-event

-- ### InnerEditor

inner-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {S P : Set}
  → {C : Category}
  → EventStackMap E F
  → InnerEditor V E S P C
  → InnerEditor V F S P C
inner-editor-map-event
  = dependent-inner-editor-map-event

