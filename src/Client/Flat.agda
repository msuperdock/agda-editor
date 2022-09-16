module Client.Flat where

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
open import Stack.Flat
  using (FlatEventStack; FlatViewStack)

-- ## FlatClient

record FlatClient
  (V : FlatViewStack)
  (E : FlatEventStack)
  : Set
  where

  open FlatViewStack V
  open FlatEventStack E

  field

    attributes
      : List (AttributeName × Attribute)

    draw
      : (v : View)
      → ViewPath v
      → Widget

    handle
      : (m : Mode)
      → InputEvent
      → Maybe (Event m ⊔ SpecialEvent)

