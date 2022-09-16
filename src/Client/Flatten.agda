module Client.Flatten where

open import Client as _
  using (Client)
open import Client.Brick
  using (InputEvent; Widget)
open import Client.Event
  using (SpecialEvent)
open import Client.Flat
  using (FlatClient)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Sigma
  using (_,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Stack
  using (EventStack; ViewStack)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack)
open import Stack.Flatten
  using (event-stack-flatten; view-stack-flatten)

-- ## Client

module _
  {V : ViewStack}
  {E : EventStack}
  where

  module ClientFlatten
    (c : Client V E)
    where

    open FlatViewStack (view-stack-flatten V)
    open FlatEventStack (event-stack-flatten E)

    open Client c public
      using (attributes)

    draw
      : (v : View)
      → ViewPath v
      → Widget
    draw (v , nothing)
      = Client.draw c v
    draw (v , just (vp , v'))
      = Client.draw-inner c v vp v'

    handle
      : (m : Mode)
      → InputEvent
      → Maybe (Event m ⊔ SpecialEvent)
    handle (ι₁ m)
      = Client.handle c m
    handle (ι₂ m)
      = Client.handle-inner c m

  client-flatten
    : Client V E
    → FlatClient
      (view-stack-flatten V)
      (event-stack-flatten E)
  client-flatten c
    = record {ClientFlatten c}

