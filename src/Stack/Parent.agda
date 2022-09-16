module Stack.Parent where

open import Data.Function
  using (id)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Data.Unit
  using (⊤)
open import Stack
  using (EventStack; EventStackMap; ViewStack)
open import Stack.Base
  using (BaseEventStack; BaseEventStackMap; BaseViewStack)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack)

-- ## Stacks

-- ### ViewStack

module _
  {K : Set}
  where

  module ViewStackParent
    (V : BaseViewStack)
    (V' : K → FlatViewStack)
    where

    open BaseViewStack V public
      using (View; ViewPath)

    ViewInner
      : (v : View)
      → ViewPath v
      → Set
    ViewInner _ _
      = k ∈ K × FlatViewStack.View (V' k)

    ViewInnerPath
      : (v : View)
      → (vp : ViewPath v)
      → ViewInner v vp
      → Set
    ViewInnerPath _ _ (k , v)
      = FlatViewStack.ViewPath (V' k) v

  view-stack-parent
    : BaseViewStack
    → (K → FlatViewStack)
    → ViewStack
  view-stack-parent V V'
    = record {ViewStackParent V V'}

-- ### EventStack

module _
  {K : Set}
  where

  module EventStackParent
    (E : BaseEventStack)
    (E' : K → FlatEventStack)
    where

    Mode
      : Set
    Mode
      = ⊤

    Event
      : Mode
      → Set
    Event _
      = BaseEventStack.Event E ⊔ K

    ModeInner
      : Set
    ModeInner
      = k ∈ K × FlatEventStack.Mode (E' k)

    EventInner
      : ModeInner
      → Set
    EventInner (k , m)
      = FlatEventStack.Event (E' k) m

  event-stack-parent
    : BaseEventStack
    → (K → FlatEventStack)
    → EventStack
  event-stack-parent E E'
    = record {EventStackParent E E'}

-- ## StackMaps

-- ### EventStackMap

module _
  {K : Set}
  {E F : BaseEventStack}
  where

  module EventStackMapParent
    (E' : K → FlatEventStack)
    (G : BaseEventStackMap E F)
    where

    mode
      : EventStack.Mode (event-stack-parent E E')
      → EventStack.Mode (event-stack-parent F E')
    mode
      = id

    mode-inner
      : EventStack.ModeInner (event-stack-parent E E')
      → EventStack.ModeInner (event-stack-parent F E')
    mode-inner
      = id

    event
      : (m : EventStack.Mode (event-stack-parent E E'))
      → EventStack.Event (event-stack-parent F E') (mode m)
      → EventStack.Event (event-stack-parent E E') m
    event _ (ι₁ e)
      = ι₁ (BaseEventStackMap.event G e)
    event _ (ι₂ k)
      = ι₂ k

    event-inner
      : (m : EventStack.ModeInner (event-stack-parent E E'))
      → EventStack.EventInner (event-stack-parent F E') (mode-inner m)
      → EventStack.EventInner (event-stack-parent E E') m
    event-inner _
      = id

  event-stack-map-parent
    : (E' : K → FlatEventStack)
    → BaseEventStackMap E F
    → EventStackMap
      (event-stack-parent E E')
      (event-stack-parent F E')
  event-stack-map-parent E' G
    = record {EventStackMapParent E' G}

