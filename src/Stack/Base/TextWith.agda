module Stack.Base.TextWith where

open import Data.Bool
  using (Bool)
open import Data.Char
  using (Char)
open import Event.TextWith
  using (TextWithEvent)
open import Stack.Base
  using (BaseEventStack)

-- ## Stacks

-- ### BaseEventStack

base-event-stack-text-with
  : (Char → Bool)
  → BaseEventStack
base-event-stack-text-with p
  = record
  { Event
    = TextWithEvent p
  }

