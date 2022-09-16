module Stack.Sigma where

open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Sigma
  using (Σ; _×_; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Stack
  using (EventStack; ViewStack)

-- ## Stacks

-- ### ViewStack

module ViewStackSigma
  (V₁ V₂ : ViewStack)
  where

  View
    : Set
  View
    = ViewStack.View V₁
    × Maybe (ViewStack.View V₂)

  ViewPath
    : View
    → Set
  ViewPath (v₁ , nothing)
    = ViewStack.ViewPath V₁ v₁
  ViewPath (v₁ , just v₂)
    = ViewStack.ViewPath V₁ v₁
    ⊔ ViewStack.ViewPath V₂ v₂
  
  ViewInner
    : (v : View)
    → ViewPath v
    → Set
  ViewInner (v₁ , nothing) vp₁
    = ViewStack.ViewInner V₁ v₁ vp₁
  ViewInner (_ , just _) (ι₁ _)
    = v₁ ∈ ViewStack.View V₁
    × Maybe (Σ (ViewStack.ViewPath V₁ v₁) (ViewStack.ViewInner V₁ v₁))
  ViewInner (_ , just v₂) (ι₂ vp₂)
    = ViewStack.ViewInner V₂ v₂ vp₂
  
  ViewInnerPath
    : (v : View)
    → (vp : ViewPath v)
    → ViewInner v vp
    → Set
  ViewInnerPath (v₁ , nothing) vp₁ v₁'
    = ViewStack.ViewInnerPath V₁ v₁ vp₁ v₁'
  ViewInnerPath (_ , just _) (ι₁ _) (v₁ , nothing)
    = ViewStack.ViewPath V₁ v₁
  ViewInnerPath (_ , just _) (ι₁ _) (v₁ , just (vp₁ , v₁'))
    = ViewStack.ViewInnerPath V₁ v₁ vp₁ v₁'
  ViewInnerPath (_ , just v₂) (ι₂ vp₂) v₂'
    = ViewStack.ViewInnerPath V₂ v₂ vp₂ v₂'

view-stack-sigma
  : ViewStack
  → ViewStack
  → ViewStack
view-stack-sigma V₁ V₂
  = record {ViewStackSigma V₁ V₂}

-- ### EventStack

module EventStackSigma
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
    = EventStack.Mode E₁
    ⊔ EventStack.ModeInner E₁
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
    = EventStack.Event E₁ m₁
  EventInner (ι₂ (ι₁ m₁))
    = EventStack.EventInner E₁ m₁
  EventInner (ι₂ (ι₂ m₂))
    = EventStack.EventInner E₂ m₂

event-stack-sigma
  : EventStack
  → EventStack
  → EventStack
event-stack-sigma E₁ E₂
  = record {EventStackSigma E₁ E₂}

