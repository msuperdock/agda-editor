module Editor.Simple.Flatten where

open import Category.State.Unit
  using (state-category-unit)
open import Data.Function
  using (_$_; _∘_)
open import Data.Maybe
  using (just; nothing)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Sum
  using (ι₁; ι₂)
open import Editor
  using (Editor)
open import Editor.Flat
  using (FlatEditor; FlatMainEditor)
open import Editor.Flat.Map
  using (flat-editor-map)
open import Editor.Flatten
  using (editor-flatten)
open import Editor.Simple
  using (SimpleEditor; SimpleInnerEditor; SimpleMainEditor; SimplePartialEditor;
    SimpleSplitEditor)
open import Editor.Unit
  using (editor-unit)
open import Stack
  using (EventStack; ViewStack)
open import Stack.Flatten
  using (event-stack-flatten; view-stack-flatten)

-- ## Base

-- ### SimpleEditor 

simple-editor-flatten
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → SimpleEditor V E A
  → FlatEditor
    (view-stack-flatten V)
    (event-stack-flatten E) A
simple-editor-flatten
  = editor-flatten
  ∘ editor-unit

-- ## Nondependent

-- ### SimplePartialEditor

simple-partial-editor-flatten
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → SimplePartialEditor V E A
  → FlatEditor
    (view-stack-flatten V)
    (event-stack-flatten E) A
simple-partial-editor-flatten e
  = flat-editor-map (SimplePartialEditor.partial-function e)
  $ simple-editor-flatten (SimplePartialEditor.editor e)

-- ### SimpleSplitEditor

simple-split-editor-flatten
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → SimpleSplitEditor V E A
  → FlatEditor
    (view-stack-flatten V)
    (event-stack-flatten E) A
simple-split-editor-flatten e
  = flat-editor-map (SimpleSplitEditor.base' e)
  $ simple-editor-flatten (SimpleSplitEditor.editor e)

-- ### SimpleMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S : Set}
  where

  module SimpleMainEditorFlatten
    (e : SimpleMainEditor V E S)
    where

    editor
      : Editor V E
        (state-category-unit (SimpleMainEditor.State e))
    editor
      = editor-unit
        (SimpleMainEditor.editor e)

    flat-editor
      : FlatEditor
        (view-stack-flatten V)
        (event-stack-flatten E)
        (SimpleMainEditor.State e)
    flat-editor
      = editor-flatten editor

    open FlatEditor flat-editor public
      hiding (handle-escape; handle-return)

    initial-with
      : S
      → State
    initial-with s
      with SimpleMainEditor.state-decode e s
    ... | nothing
      = initial
    ... | just s'
      = (s' , nothing)

    initial-path-with
      : (s : S)
      → StatePath (initial-with s)
    initial-path-with s
      with SimpleMainEditor.state-decode e s
    ... | nothing
      = initial-path
    ... | just s'
      = Editor.initial-path editor s'

    handle-escape
      : (s : State)
      → StatePath s
      → Σ State StatePath
    handle-escape s sp
      with FlatEditor.handle-escape flat-editor s sp
    ... | nothing
      = (s , sp)
    ... | just s'
      = s'

    handle-return
      : (s : State)
      → StatePath s
      → Σ State StatePath
    handle-return s sp
      with FlatEditor.handle-return flat-editor s sp
    ... | ι₁ _
      = (s , sp)
    ... | ι₂ s'
      = s'

    handle-save
      : State
      → S
    handle-save (s , _)
      = SimpleMainEditor.state-encode e s

  simple-main-editor-flatten
    : SimpleMainEditor V E S
    → FlatMainEditor
      (view-stack-flatten V)
      (event-stack-flatten E) S
  simple-main-editor-flatten e
    = record {SimpleMainEditorFlatten e}

-- ### SimpleInnerEditor

simple-inner-editor-flatten
  : {V : ViewStack}
  → {E : EventStack}
  → {S P A : Set}
  → SimpleInnerEditor V E S P A
  → FlatEditor
    (view-stack-flatten V)
    (event-stack-flatten E) A
simple-inner-editor-flatten e
  = flat-editor-map (SimpleInnerEditor.base' e)
  $ simple-editor-flatten (SimpleInnerEditor.editor e)

