module Stack.Base.Text where

open import Data.Bool
  using (true)
open import Data.CharWith
  using (char-with)
open import Data.Equal
  using (refl)
open import Data.Fin
  using (Fin)
open import Data.Function
  using (const)
open import Data.Maybe
  using (Maybe)
open import Data.Text
  using (Text)
open import Event.Text
  using (TextEvent)
open import Event.TextWith
  using (TextWithEvent)
open import Stack.Base
  using (BaseEventStack; BaseEventStackMap; BaseViewStack)
open import Stack.Base.TextWith
  using (base-event-stack-text-with)

-- ## Stacks

-- ### BaseViewStack

base-view-stack-text
  : BaseViewStack
base-view-stack-text
  = record
  { View
    = Text
  ; ViewPath
    = λ t → Maybe (Fin (Text.length t))
  }

-- ### BaseEventStack

base-event-stack-text
  : BaseEventStack
base-event-stack-text
  = record
  { Event
    = TextEvent
  }

-- ## StackMaps

-- ### BaseEventStackMap

module BaseEventStackMapText where

  event
    : BaseEventStack.Event base-event-stack-text
    → BaseEventStack.Event (base-event-stack-text-with (const true))
  event TextEvent.delete-previous
    = TextWithEvent.delete-previous
  event TextEvent.delete-next
    = TextWithEvent.delete-next
  event (TextEvent.insert c)
    = TextWithEvent.insert (char-with c refl)

base-event-stack-map-text
  : BaseEventStackMap
    (base-event-stack-text-with (const true))
    base-event-stack-text
base-event-stack-map-text
  = record {BaseEventStackMapText}

