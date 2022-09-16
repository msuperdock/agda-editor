module Stack.Lift where

open import Data.Empty
  using (⊥)
open import Data.Function
  using (id)
open import Data.Unit
  using (⊤)
open import Stack
  using (EventStack; EventStackMap; ViewStack; ViewStackMap)
open import Stack.Base
  using (BaseEventStack; BaseEventStackMap; BaseViewStack; BaseViewStackMap)

-- ## Stacks

-- ### ViewStack

view-stack-lift
  : BaseViewStack
  → ViewStack
view-stack-lift V
  = record
  { BaseViewStack V
  ; ViewInner
    = λ _ _ → ⊥
  ; ViewInnerPath
    = λ _ _ ()
  }

-- ### EventStack

event-stack-lift
  : BaseEventStack
  → EventStack
event-stack-lift E
  = record
  { Mode
    = ⊤
  ; Event
    = λ _ → BaseEventStack.Event E
  ; ModeInner
    = ⊥
  ; EventInner
    = λ ()
  }

-- ## StackMaps

-- ### ViewStackMap

view-stack-map-lift
  : {V W : BaseViewStack}
  → BaseViewStackMap V W
  → ViewStackMap
    (view-stack-lift V)
    (view-stack-lift W)
view-stack-map-lift F
  = record
  { BaseViewStackMap F
  ; view-inner-with
    = λ _ _ ()
  ; view-inner-path
    = λ _ _ ()
  }

-- ### EventStackMap

event-stack-map-lift
  : {E F : BaseEventStack}
  → BaseEventStackMap E F
  → EventStackMap
    (event-stack-lift E)
    (event-stack-lift F)
event-stack-map-lift G
  = record
  { mode
    = id
  ; event
    = λ _ → BaseEventStackMap.event G
  ; mode-inner
    = λ ()
  ; event-inner
    = λ ()
  }

