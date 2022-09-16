module Client where

open import Client.Brick
  using (Attribute; AttributeName; InputEvent; Widget)
open import Client.Event
  using (SpecialEvent)
open import Data.List
  using (List)
open import Data.Maybe
  using (Maybe)
open import Data.Sigma
  using (_×_)
open import Data.Sum
  using (_⊔_)
open import Stack
  using (EventStack; ViewStack)

-- ## Client

record Client
  (V : ViewStack)
  (E : EventStack)
  : Set
  where

  open ViewStack V
  open EventStack E

  field

    attributes
      : List (AttributeName × Attribute)

    draw
      : (v : View)
      → ViewPath v
      → Widget

    draw-inner
      : (v : View)
      → (vp : ViewPath v)
      → (v' : ViewInner v vp)
      → ViewInnerPath v vp v'
      → Widget

    handle
      : (m : Mode)
      → InputEvent
      → Maybe (Event m ⊔ SpecialEvent)

    handle-inner
      : (m : ModeInner)
      → InputEvent
      → Maybe (EventInner m ⊔ SpecialEvent)

