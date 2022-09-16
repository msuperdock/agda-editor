module Editor.Simple.Base where

open import Data.Direction
  using (Direction)
open import Data.Equal
  using (_≡_)
open import Data.Maybe
  using (Maybe; nothing)
open import Data.Sigma
  using (Σ)
open import Stack.Base
  using (BaseEventStack; BaseViewStack; BaseViewStackMap)

-- ## SimpleBaseEditor

record SimpleBaseEditor
  (V : BaseViewStack)
  (E : BaseEventStack)
  (A : Set)
  : Set₁
  where

  -- ### Types

  open BaseViewStack V
  open BaseEventStack E

  private

    State
      : Set
    State
      = A

  -- ### State

  field

    StatePath
      : State
      → Set

  StateStack
    : BaseViewStack
  StateStack
    = record
    { View
      = State
    ; ViewPath
      = StatePath
    }

  field

    initial
      : State

    initial-path
      : (s : State)
      → StatePath s

    -- The initial path when entering from the given direction.
    initial-path-with
      : (s : State)
      → Direction
      → StatePath s

  -- ### Draw

  field

    draw
      : State
      → View

    draw-with
      : (s : State)
      → StatePath s
      → View

    draw-path
      : (s : State)
      → (sp : StatePath s)
      → ViewPath (draw-with s sp)

  draw-stack
    : BaseViewStackMap StateStack V
  draw-stack
    = record
    { view
      = draw
    ; view-with
      = draw-with
    ; view-path
      = draw-path
    }

  -- ### Handle

  field

    handle
      : (s : State)
      → StatePath s
      → Event
      → Σ State StatePath

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → Maybe (StatePath s)

    handle-direction-valid
      : (s : State)
      → (d : Direction)
      → handle-direction s (initial-path-with s d) d ≡ nothing

