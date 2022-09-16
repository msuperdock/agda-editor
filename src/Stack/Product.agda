module Stack.Product where

open import Data.Sigma
  using (_×_; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)

-- ## Stacks

-- ### ViewStack

module ViewStackProduct
  (V₁ V₂ : ViewStack)
  where

  View
    : Set
  View
    = ViewStack.View V₁
    × ViewStack.View V₂

  ViewPath
    : View
    → Set
  ViewPath (v₁ , v₂)
    = ViewStack.ViewPath V₁ v₁
    ⊔ ViewStack.ViewPath V₂ v₂
  
  ViewInner
    : (v : View)
    → ViewPath v
    → Set
  ViewInner (v₁ , _) (ι₁ vp₁)
    = ViewStack.ViewInner V₁ v₁ vp₁
  ViewInner (_ , v₂) (ι₂ vp₂)
    = ViewStack.ViewInner V₂ v₂ vp₂

  ViewInnerPath
    : (v : View)
    → (vp : ViewPath v)
    → ViewInner v vp
    → Set
  ViewInnerPath (v₁ , _) (ι₁ vp₁)
    = ViewStack.ViewInnerPath V₁ v₁ vp₁
  ViewInnerPath (_ , v₂) (ι₂ vp₂)
    = ViewStack.ViewInnerPath V₂ v₂ vp₂

view-stack-product
  : ViewStack
  → ViewStack
  → ViewStack
view-stack-product V₁ V₂
  = record {ViewStackProduct V₁ V₂}

-- ### EventStack

module EventStackProduct
  (E₁ E₂ : EventStack)
  where

  Mode
    : Set
  Mode
    = EventStack.Mode E₁
    ⊔ EventStack.Mode E₂

  ModeInner
    : Set
  ModeInner
    = EventStack.ModeInner E₁
    ⊔ EventStack.ModeInner E₂

  Event
    : Mode
    → Set
  Event (ι₁ m₁)
    = EventStack.Event E₁ m₁
  Event (ι₂ m₂)
    = EventStack.Event E₂ m₂

  EventInner
    : ModeInner
    → Set
  EventInner (ι₁ m₁)
    = EventStack.EventInner E₁ m₁
  EventInner (ι₂ m₂)
    = EventStack.EventInner E₂ m₂

event-stack-product
  : EventStack
  → EventStack
  → EventStack
event-stack-product E₁ E₂
  = record {EventStackProduct E₁ E₂}

-- ## StackMaps

-- ### ViewStackMap

module _
  {V₁ V₂ W₁ W₂ : ViewStack}
  where

  module ViewStackMapProduct
    (F₁ : ViewStackMap V₁ W₁)
    (F₂ : ViewStackMap V₂ W₂)
    where

    view
      : ViewStack.View (view-stack-product V₁ V₂)
      → ViewStack.View (view-stack-product W₁ W₂)
    view (v₁ , v₂)
      = ViewStackMap.view F₁ v₁
      , ViewStackMap.view F₂ v₂

    view-with
      : (v : ViewStack.View (view-stack-product V₁ V₂))
      → ViewStack.ViewPath (view-stack-product V₁ V₂) v
      → ViewStack.View (view-stack-product W₁ W₂)
    view-with (v₁ , v₂) (ι₁ vp₁)
      = ViewStackMap.view-with F₁ v₁ vp₁
      , ViewStackMap.view F₂ v₂
    view-with (v₁ , v₂) (ι₂ vp₂)
      = ViewStackMap.view F₁ v₁
      , ViewStackMap.view-with F₂ v₂ vp₂
    
    view-path
      : (v : ViewStack.View (view-stack-product V₁ V₂))
      → (vp : ViewStack.ViewPath (view-stack-product V₁ V₂) v)
      → ViewStack.ViewPath (view-stack-product W₁ W₂)
        (view-with v vp)
    view-path (v₁ , _) (ι₁ vp₁)
      = ι₁ (ViewStackMap.view-path F₁ v₁ vp₁)
    view-path (_ , v₂) (ι₂ vp₂)
      = ι₂ (ViewStackMap.view-path F₂ v₂ vp₂)

    view-inner-with
      : (v : ViewStack.View (view-stack-product V₁ V₂))
      → (vp : ViewStack.ViewPath (view-stack-product V₁ V₂) v)
      → (v' : ViewStack.ViewInner (view-stack-product V₁ V₂) v vp)
      → ViewStack.ViewInnerPath (view-stack-product V₁ V₂) v vp v'
      → ViewStack.ViewInner (view-stack-product W₁ W₂)
        (view-with v vp)
        (view-path v vp)
    view-inner-with (v₁ , _) (ι₁ vp₁)
      = ViewStackMap.view-inner-with F₁ v₁ vp₁
    view-inner-with (_ , v₂) (ι₂ vp₂)
      = ViewStackMap.view-inner-with F₂ v₂ vp₂

    view-inner-path
      : (v : ViewStack.View (view-stack-product V₁ V₂))
      → (vp : ViewStack.ViewPath (view-stack-product V₁ V₂) v)
      → (v' : ViewStack.ViewInner (view-stack-product V₁ V₂) v vp)
      → (vp' : ViewStack.ViewInnerPath (view-stack-product V₁ V₂) v vp v')
      → ViewStack.ViewInnerPath (view-stack-product W₁ W₂)
        (view-with v vp)
        (view-path v vp)
        (view-inner-with v vp v' vp')
    view-inner-path (v₁ , _) (ι₁ vp₁)
      = ViewStackMap.view-inner-path F₁ v₁ vp₁
    view-inner-path (_ , v₂) (ι₂ vp₂)
      = ViewStackMap.view-inner-path F₂ v₂ vp₂

  view-stack-map-product
    : ViewStackMap V₁ W₁
    → ViewStackMap V₂ W₂
    → ViewStackMap
      (view-stack-product V₁ V₂)
      (view-stack-product W₁ W₂)
  view-stack-map-product F₁ F₂
    = record {ViewStackMapProduct F₁ F₂}

