module Stack.Nat where

open import Stack
  using (EventStack)
open import Stack.Base.Nat
  using (base-event-stack-nat)
open import Stack.Lift
  using (event-stack-lift)

-- ## Stacks

-- ### EventStack

event-stack-nat
  : EventStack
event-stack-nat
  = event-stack-lift
    base-event-stack-nat

