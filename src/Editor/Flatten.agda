module Editor.Flatten where

open import Category
  using (Category)
open import Category.State
  using (StateCategory)
open import Data.Direction
  using (Direction)
open import Data.Function
  using (_$_; id)
open import Data.Maybe
  using (Maybe; just; maybe; nothing)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Editor
  using (Editor; InnerEditor; SplitEditor)
open import Editor.Flat
  using (FlatEditor)
open import Editor.Flat.Map
  using (flat-editor-map)
open import Stack
  using (EventStack; ViewStack)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack; FlatViewStackMap)
open import Stack.Flatten
  using (event-stack-flatten; view-stack-flatten; view-stack-map-flatten)

-- ## Base

-- ### Editor

module _
  {V : ViewStack}
  {E : EventStack}
  {C : StateCategory}
  where

  -- #### Module

  module EditorFlatten
    (e : Editor V E C)
    where

    -- ##### Types

    open FlatEventStack (event-stack-flatten E)

    -- ##### State
  
    StateStack
      : FlatViewStack
    StateStack
      = view-stack-flatten
        (Editor.StateStack e)
  
    open FlatViewStack StateStack public
      using () renaming
      ( View
        to State
      ; ViewPath
        to StatePath
      )
  
    initial
      : State
    initial
      = (Editor.initial e , nothing)
  
    initial-path
      : StatePath initial
    initial-path
      = Editor.initial-path' e

    -- ##### Draw

    draw-stack
      : FlatViewStackMap StateStack (view-stack-flatten V)
    draw-stack
      = view-stack-map-flatten
        (Editor.draw-stack e)

    -- ##### Mode

    mode
      : (s : State)
      → StatePath s
      → Mode
    mode (s , nothing) sp
      = ι₁ (Editor.mode e s sp)
    mode (s , just (sp , s')) sp'
      = ι₂ (Editor.mode-inner e s sp s' sp')

    -- ##### Handle

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → Σ State StatePath
    handle (s , nothing) sp e'
      with Editor.handle e s sp e'
    ... | ι₁ (s' , sp' , _)
      = ((s' , nothing) , sp')
    ... | ι₂ (s' , sp')
      = ((s , just (sp , s')) , sp')
    handle (s , just (sp , s')) sp' e'
      with Editor.handle-inner e s sp s' sp' e'
    ... | (s'' , sp'')
      = ((s , just (sp , s'')) , sp'')

    handle-escape
      : (s : State)
      → StatePath s
      → Maybe (Σ State StatePath)
    handle-escape (s , nothing) sp
      with Editor.handle-escape e s sp
    ... | nothing
      = nothing
    ... | just (ι₁ (s' , sp' , _))
      = just ((s' , nothing) , sp')
    ... | just (ι₂ (s' , sp'))
      = just ((s , just (sp , s')) , sp')
    handle-escape (s , just (sp , s')) sp'
      with Editor.handle-inner-escape e s sp s' sp'
    ... | nothing
      = just ((s , nothing) , sp)
    ... | just (s'' , sp'')
      = just ((s , just (sp , s'')) , sp'')

    handle-return
      : (s : State)
      → StatePath s
      → StateCategory.Object C ⊔ Σ State StatePath
    handle-return (s , nothing) sp
      with Editor.handle-return e s sp
    ... | nothing
      = ι₁ s
    ... | just (ι₁ (s' , sp' , _))
      = ι₂ ((s' , nothing) , sp')
    ... | just (ι₂ (s' , sp'))
      = ι₂ ((s , just (sp , s')) , sp')
    handle-return (s , just (sp , s')) sp'
      with Editor.handle-inner-return e s sp s' sp'
    ... | ι₁ (s'' , sp'' , _)
      = ι₂ ((s'' , nothing) , sp'')
    ... | ι₂ (s'' , sp'')
      = ι₂ ((s , just (sp , s'')) , sp'')

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → StatePath s
    handle-direction (s , nothing) sp d
      = maybe (Editor.handle-direction e s sp d) sp id
    handle-direction (s , just (sp , s')) sp' d
      = Editor.handle-inner-direction e s sp s' sp' d

  -- #### Function

  editor-flatten
    : Editor V E C
    → FlatEditor
      (view-stack-flatten V)
      (event-stack-flatten E)
      (StateCategory.Object C)
  editor-flatten e
    = record {EditorFlatten e}

-- ## Nondependent

-- ### SplitEditor

split-editor-flatten
  : {V : ViewStack}
  → {E : EventStack}
  → {C : Category}
  → SplitEditor V E C
  → FlatEditor
    (view-stack-flatten V)
    (event-stack-flatten E)
    (Category.Object C)
split-editor-flatten e
  = flat-editor-map (SplitEditor.base' e)
  $ editor-flatten (SplitEditor.editor e)

-- ### InnerEditor

inner-editor-flatten
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C : Category}
  → InnerEditor V E S P C
  → FlatEditor
    (view-stack-flatten V)
    (event-stack-flatten E)
    (Category.Object C)
inner-editor-flatten e
  = flat-editor-map (InnerEditor.base' e)
  $ editor-flatten (InnerEditor.editor e)

