module Editor.Lift where

open import Category.State
  using (StateCategory)
open import Data.Direction
  using (Direction)
open import Data.Maybe
  using (Maybe; nothing)
open import Data.Sigma
  using (Σ)
open import Data.Sum
  using (_⊔_; ι₁)
open import Data.Unit
  using (tt)
open import Editor
  using (Editor)
open import Editor.Base
  using (BaseEditor)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)
open import Stack.Base
  using (BaseEventStack; BaseViewStack)
open import Stack.Lift
  using (event-stack-lift; view-stack-lift; view-stack-map-lift)

-- ## Editor

module _
  {V : BaseViewStack}
  {E : BaseEventStack}
  {C : StateCategory}
  where

  -- ### Module

  module EditorLift
    (e : BaseEditor V E C)
    where

    -- #### Types

    open EventStack (event-stack-lift E)

    open StateCategory C
      using () renaming
      ( Object
        to State
      ; Arrow
        to StateArrow
      )

    -- #### State

    open BaseEditor e public
      using (initial; initial-path; initial-path-with)

    StateStack
      : ViewStack
    StateStack
      = view-stack-lift
        (BaseEditor.StateStack e)

    open ViewStack StateStack public
      using () renaming
      ( ViewPath
        to StatePath
      ; ViewInner
        to StateInner
      ; ViewInnerPath
        to StateInnerPath
      )

    -- #### Draw

    draw-stack
      : ViewStackMap StateStack (view-stack-lift V)
    draw-stack
      = view-stack-map-lift
        (BaseEditor.draw-stack e)

    -- #### Mode

    mode
      : (s : State)
      → StatePath s
      → Mode
    mode _ _
      = tt

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner
    mode-inner _ _ ()

    -- #### Handle

    open BaseEditor e public
      using (handle-direction; handle-direction-valid)

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle s sp e'
      = ι₁ (BaseEditor.handle e s sp e')

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-escape _ _
      = nothing

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-return _ _
      = nothing

    handle-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → EventInner (mode-inner s sp s' sp')
      → Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner _ _ ()

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))
    handle-inner-escape _ _ ()

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return _ _ ()

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'
    handle-inner-direction _ _ ()

  -- ### Function

  editor-lift
    : BaseEditor V E C
    → Editor
      (view-stack-lift V)
      (event-stack-lift E) C
  editor-lift e
    = record {EditorLift e}

