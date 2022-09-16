module Stack.Text where

open import Data.Bool
  using (true)
open import Data.Function
  using (const)
open import Stack
  using (EventStack; EventStackMap; ViewStack)
open import Stack.Base.Text
  using (base-event-stack-text; base-event-stack-map-text; base-view-stack-text)
open import Stack.Lift
  using (event-stack-lift; event-stack-map-lift; view-stack-lift)
open import Stack.TextWith
  using (event-stack-text-with)

-- ## Stacks

-- ### ViewStack

view-stack-text
  : ViewStack
view-stack-text
  = view-stack-lift
    base-view-stack-text

-- ### EventStack

event-stack-text
  : EventStack
event-stack-text
  = event-stack-lift
    base-event-stack-text

-- ## StackMaps

-- ### EventStackMap

event-stack-map-text
  : EventStackMap
    (event-stack-text-with (const true))
    event-stack-text
event-stack-map-text
  = event-stack-map-lift
    base-event-stack-map-text

