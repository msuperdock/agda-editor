module Editor.Parent where

open import Category.State
  using (StateCategory)
open import Data.Direction
  using (Direction)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Data.Unit
  using (tt)
open import Editor
  using (Editor)
open import Editor.Base
  using (BaseEditor)
open import Editor.Flat
  using (FlatEditor)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)
open import Stack.Base
  using (BaseEventStack; BaseViewStack)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack)
open import Stack.Parent
  using (event-stack-parent; view-stack-parent)

-- ## Editor

module _
  {K : Set}
  where

  -- ### Module

  module EditorParent
    {V : BaseViewStack}
    (V' : K → FlatViewStack)
    {E : BaseEventStack}
    (E' : K → FlatEventStack)
    {C : StateCategory}
    (e : BaseEditor V E C)
    (e' : (k : K) → FlatEditor (V' k) (E' k) (BaseEventStack.Event E))
    where

    -- #### Types

    open ViewStack (view-stack-parent V V')
    open EventStack (event-stack-parent E E')

    open StateCategory C
      using () renaming
      ( Object
        to State
      ; Arrow
        to StateArrow
      )

    -- #### State

    open BaseEditor e public
      using (StatePath; initial; initial-path; initial-path-with)

    StateInner
      : (s : State)
      → StatePath s
      → Set
    StateInner _ _
      = k ∈ K × FlatEditor.State (e' k)

    StateInnerPath
      : (s : State)
      → (sp : StatePath s)
      → StateInner s sp
      → Set
    StateInnerPath _ _ (k , s')
      = FlatEditor.StatePath (e' k) s'

    StateStack
      : ViewStack
    StateStack
      = record
      { View
        = State
      ; ViewPath
        = StatePath
      ; ViewInner
        = StateInner
      ; ViewInnerPath
        = StateInnerPath
      }

    -- #### Draw
  
    open BaseEditor e public
      using (draw; draw-with; draw-path)

    draw-inner-with
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ViewInner
        (draw-with s sp)
        (draw-path s sp)
    draw-inner-with _ _ (k , s') sp'
      = (k , FlatEditor.draw-with (e' k) s' sp')

    draw-inner-path
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → ViewInnerPath
        (draw-with s sp)
        (draw-path s sp)
        (draw-inner-with s sp s' sp')
    draw-inner-path _ _ (k , s') sp'
      = FlatEditor.draw-path (e' k) s' sp'

    draw-stack
      : ViewStackMap StateStack (view-stack-parent V V')
    draw-stack
      = record
      { view
        = draw
      ; view-with
        = draw-with
      ; view-path
        = draw-path
      ; view-inner-with
        = draw-inner-with
      ; view-inner-path
        = draw-inner-path
      }

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
    mode-inner _ _ (k , s') sp'
      = (k , FlatEditor.mode (e' k) s' sp')

    -- #### Handle
  
    open BaseEditor e public
      using (handle-direction; handle-direction-valid)

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle s sp (ι₁ e'')
      = ι₁ (BaseEditor.handle e s sp e'')
    handle _ _ (ι₂ k)
      = ι₂ ((k , FlatEditor.initial (e' k)) , FlatEditor.initial-path (e' k))

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
    handle-inner _ _ (k , s') sp' e''
      with FlatEditor.handle (e' k) s' sp' e''
    ... | (s'' , sp'')
      = ((k , s'') , sp'')

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))
    handle-inner-escape _ _ (k , s') sp'
      with FlatEditor.handle-escape (e' k) s' sp'
    ... | nothing
      = nothing
    ... | just (s'' , sp'')
      = just ((k , s'') , sp'')

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return s sp (k , s') sp'
      with FlatEditor.handle-return (e' k) s' sp'
    ... | ι₁ e''
      = ι₁ (BaseEditor.handle e s sp e'')
    ... | ι₂ (s'' , sp'')
      = ι₂ ((k , s'') , sp'')

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'
    handle-inner-direction _ _ (k , s')
      = FlatEditor.handle-direction (e' k) s'

  -- ### Function

  editor-parent
    : {V : BaseViewStack}
    → (V' : K → FlatViewStack)
    → {E : BaseEventStack}
    → (E' : K → FlatEventStack)
    → {C : StateCategory}
    → BaseEditor V E C
    → ((k : K) → FlatEditor (V' k) (E' k) (BaseEventStack.Event E))
    → Editor
      (view-stack-parent V V')
      (event-stack-parent E E') C
  editor-parent V' E' e e'
    = record {EditorParent V' E' e e'}

