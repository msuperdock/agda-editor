module Stack.Base.Flatten where

open import Data.Function
  using (id)
open import Data.Maybe
  using (nothing)
open import Data.Sigma
  using (_,_)
open import Data.Sum
  using (ι₁)
open import Data.Unit
  using (⊤)
open import Stack.Base
  using (BaseEventStack; BaseViewStack)
open import Stack.Flat
  using (FlatEventStack; FlatEventStackMap; FlatViewStack; FlatViewStackMap)
open import Stack.Flatten
  using (event-stack-flatten; view-stack-flatten)
open import Stack.Lift
  using (event-stack-lift; view-stack-lift)

-- ## Stacks

-- ### BaseViewStack

base-view-stack-flatten
  : BaseViewStack
  → FlatViewStack
base-view-stack-flatten V
  = record {BaseViewStack V}

-- ### BaseEventStack

base-event-stack-flatten
  : BaseEventStack
  → FlatEventStack
base-event-stack-flatten E
  = record
  { Mode
    = ⊤
  ; Event
    = λ _ → BaseEventStack.Event E
  }

-- ## StackMaps

-- ### ViewStackMap

module BaseViewStackFlattenLift
  (V : BaseViewStack)
  where

  view-with
    : (v : FlatViewStack.View (view-stack-flatten (view-stack-lift V)))
    → FlatViewStack.ViewPath (view-stack-flatten (view-stack-lift V)) v
    → FlatViewStack.View (base-view-stack-flatten V)
  view-with (v , nothing) _
    = v
  
  view-path
    : (v : FlatViewStack.View (view-stack-flatten (view-stack-lift V)))
    → (vp : FlatViewStack.ViewPath (view-stack-flatten (view-stack-lift V)) v)
    → FlatViewStack.ViewPath (base-view-stack-flatten V) (view-with v vp)
  view-path (_ , nothing) vp
    = vp

base-view-stack-flatten-lift
  : (V : BaseViewStack)
  → FlatViewStackMap
    (view-stack-flatten (view-stack-lift V))
    (base-view-stack-flatten V)
base-view-stack-flatten-lift V
  = record {BaseViewStackFlattenLift V}

-- ### EventStackMap

module BaseEventStackFlattenLift
  (E : BaseEventStack)
  where

  mode
    : FlatEventStack.Mode (event-stack-flatten (event-stack-lift E))
    → FlatEventStack.Mode (base-event-stack-flatten E)
  mode (ι₁ e)
    = e

  event
    : (m : FlatEventStack.Mode (event-stack-flatten (event-stack-lift E)))
    → FlatEventStack.Event (base-event-stack-flatten E) (mode m)
    → FlatEventStack.Event (event-stack-flatten (event-stack-lift E)) m
  event (ι₁ _)
    = id

base-event-stack-flatten-lift
  : (E : BaseEventStack)
  → FlatEventStackMap
    (event-stack-flatten (event-stack-lift E))
    (base-event-stack-flatten E)
base-event-stack-flatten-lift E
  = record {BaseEventStackFlattenLift E}

