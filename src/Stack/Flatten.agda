module Stack.Flatten where

open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack; FlatViewStackMap)

-- ## Stacks

-- ### ViewStack

module ViewStackFlatten
  (V : ViewStack)
  where

  View
    : Set
  View
    = v ∈ ViewStack.View V
    × Maybe (Σ (ViewStack.ViewPath V v) (ViewStack.ViewInner V v))

  ViewPath
    : View
    → Set
  ViewPath (v , nothing)
    = ViewStack.ViewPath V v
  ViewPath (v , just (vp , v'))
    = ViewStack.ViewInnerPath V v vp v'

view-stack-flatten
  : ViewStack
  → FlatViewStack
view-stack-flatten V
  = record {ViewStackFlatten V}

-- ### EventStack

module EventStackFlatten
  (E : EventStack)
  where

  Mode
    : Set
  Mode
    = EventStack.Mode E
    ⊔ EventStack.ModeInner E

  Event
    : Mode
    → Set
  Event (ι₁ m)
    = EventStack.Event E m
  Event (ι₂ m)
    = EventStack.EventInner E m

event-stack-flatten
  : EventStack
  → FlatEventStack
event-stack-flatten E
  = record {EventStackFlatten E}

-- ## StackMaps

-- ### ViewStackMap

module _
  {V W : ViewStack}
  where

  module ViewStackMapFlatten
    (F : ViewStackMap V W)
    where

    view-with
      : (v : FlatViewStack.View (view-stack-flatten V))
      → FlatViewStack.ViewPath (view-stack-flatten V) v
      → FlatViewStack.View (view-stack-flatten W)
    view-with (v , nothing) vp
      = (ViewStackMap.view-with F v vp , nothing)
    view-with (v , just (vp , v')) vp'
      = (ViewStackMap.view-with F v vp
        , just (ViewStackMap.view-path F v vp
          , ViewStackMap.view-inner-with F v vp v' vp'))

    view-path
      : (v : FlatViewStack.View (view-stack-flatten V))
      → (vp : FlatViewStack.ViewPath (view-stack-flatten V) v)
      → FlatViewStack.ViewPath (view-stack-flatten W) (view-with v vp)
    view-path (v , nothing)
      = ViewStackMap.view-path F v
    view-path (v , just (vp , v'))
      = ViewStackMap.view-inner-path F v vp v'

  view-stack-map-flatten
    : ViewStackMap V W
    → FlatViewStackMap
      (view-stack-flatten V)
      (view-stack-flatten W)
  view-stack-map-flatten F
    = record {ViewStackMapFlatten F}

