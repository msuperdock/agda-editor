module Stack.Base.Nat where

open import Event.Nat
  using (NatEvent)
open import Stack.Base
  using (BaseEventStack)

-- ## Stacks

-- ### BaseEventStack

base-event-stack-nat
  : BaseEventStack
base-event-stack-nat
  = record
  { Event
    = NatEvent
  }

