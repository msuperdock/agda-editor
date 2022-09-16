module Stack.Flat.Text where

open import Stack.Base.Flatten
  using (base-event-stack-flatten; base-view-stack-flatten)
open import Stack.Base.Text
  using (base-event-stack-text; base-view-stack-text)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack)

-- ## Stacks

-- ### FlatViewStack

flat-view-stack-text
  : FlatViewStack
flat-view-stack-text
  = base-view-stack-flatten
    base-view-stack-text

-- ### FlatEventStack

flat-event-stack-text
  : FlatEventStack
flat-event-stack-text
  = base-event-stack-flatten
    base-event-stack-text

