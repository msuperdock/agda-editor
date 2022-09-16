module Stack.Base where

-- ## Stacks

-- ### BaseViewStack

record BaseViewStack
  : Set₁
  where

  field

    View
      : Set

    ViewPath
      : View
      → Set

-- ### BaseEventStack

record BaseEventStack
  : Set₁
  where

  field

    Event
      : Set

-- ## StackMaps

-- ### BaseViewStackMap

record BaseViewStackMap
  (V W : BaseViewStack)
  : Set
  where

  field

    view
      : BaseViewStack.View V
      → BaseViewStack.View W

    view-with
      : (v : BaseViewStack.View V)
      → BaseViewStack.ViewPath V v
      → BaseViewStack.View W
    
    view-path
      : (v : BaseViewStack.View V)
      → (vp : BaseViewStack.ViewPath V v)
      → BaseViewStack.ViewPath W (view-with v vp)

-- ### BaseEventStackMap

record BaseEventStackMap
  (E F : BaseEventStack)
  : Set
  where

  constructor

    base-event-stack-map

  field

    event
      : BaseEventStack.Event F
      → BaseEventStack.Event E

