module Stack.TextWith where

open import Data.Bool
  using (Bool)
open import Data.Char
  using (Char)
open import Stack
  using (EventStack)
open import Stack.Base.TextWith
  using (base-event-stack-text-with)
open import Stack.Lift
  using (event-stack-lift)

-- ## Stacks

-- ### EventStack

event-stack-text-with
  : (Char → Bool)
  → EventStack
event-stack-text-with p
  = event-stack-lift
    (base-event-stack-text-with p)

