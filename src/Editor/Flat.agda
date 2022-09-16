module Editor.Flat where

open import Data.Direction
  using (Direction)
open import Data.Maybe
  using (Maybe)
open import Data.Sigma
  using (Σ)
open import Data.Sum
  using (_⊔_)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack; FlatViewStackMap)

-- ## FlatEditor

record FlatEditor
  (V : FlatViewStack)
  (E : FlatEventStack)
  (A : Set)
  : Set₁
  where

  -- ### Types

  open FlatEventStack E

  -- ### State

  field

    StateStack
      : FlatViewStack

  open FlatViewStack StateStack public
    using () renaming
    ( View
      to State
    ; ViewPath
      to StatePath
    )

  field

    initial
      : State

    initial-path
      : StatePath initial

  -- ### Draw

  field

    draw-stack
      : FlatViewStackMap StateStack V

  open FlatViewStackMap draw-stack public
    using () renaming
    ( view-with
      to draw-with
    ; view-path
      to draw-path
    )

  -- ### Mode

  field

    mode
      : (s : State)
      → StatePath s
      → Mode

  -- ### Handle

  field

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → Σ State StatePath

    handle-escape
      : (s : State)
      → StatePath s
      → Maybe (Σ State StatePath)

    handle-return
      : (s : State)
      → StatePath s
      → A ⊔ Σ State StatePath

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → StatePath s

-- ## FlatMainEditor

record FlatMainEditor
  (V : FlatViewStack)
  (E : FlatEventStack)
  (S : Set)
  : Set₁
  where

  -- ### Types

  open FlatEventStack E

  -- ### State

  field

    StateStack
      : FlatViewStack

  open FlatViewStack StateStack public
    using () renaming
    ( View
      to State
    ; ViewPath
      to StatePath
    )

  field

    initial
      : State

    initial-path
      : StatePath initial

    initial-with
      : S
      → State

    initial-path-with
      : (s : S)
      → StatePath (initial-with s)

  -- ### Draw

  field

    draw-stack
      : FlatViewStackMap StateStack V

  open FlatViewStackMap draw-stack public
    using () renaming
    ( view-with
      to draw-with
    ; view-path
      to draw-path
    )

  -- ### Mode

  field

    mode
      : (s : State)
      → StatePath s
      → Mode

  -- ### Handle

  field

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → Σ State StatePath

    handle-escape
      : (s : State)
      → StatePath s
      → Σ State StatePath

    handle-return
      : (s : State)
      → StatePath s
      → Σ State StatePath

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → StatePath s

    handle-save
      : State
      → S

