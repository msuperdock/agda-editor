module Stack where

-- ## Stacks

-- ### ViewStack

record ViewStack
  : Set₁
  where

  field

    View
      : Set

    ViewPath
      : View
      → Set
    
    ViewInner
      : (v : View)
      → ViewPath v
      → Set

    ViewInnerPath
      : (v : View)
      → (vp : ViewPath v)
      → ViewInner v vp
      → Set

-- ### EventStack

record EventStack
  : Set₁
  where

  field

    Mode
      : Set

    ModeInner
      : Set

    Event
      : Mode
      → Set

    EventInner
      : ModeInner
      → Set

-- ## StackMaps

-- ### ViewStackMap

record ViewStackMap
  (V W : ViewStack)
  : Set
  where

  field

    view
      : ViewStack.View V
      → ViewStack.View W

    view-with
      : (v : ViewStack.View V)
      → ViewStack.ViewPath V v
      → ViewStack.View W
    
    view-path
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → ViewStack.ViewPath W
        (view-with v vp)

    view-inner-with
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → (v' : ViewStack.ViewInner V v vp)
      → ViewStack.ViewInnerPath V v vp v'
      → ViewStack.ViewInner W
        (view-with v vp)
        (view-path v vp)

    view-inner-path
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → (v' : ViewStack.ViewInner V v vp)
      → (vp' : ViewStack.ViewInnerPath V v vp v')
      → ViewStack.ViewInnerPath W
        (view-with v vp)
        (view-path v vp)
        (view-inner-with v vp v' vp')

-- ### EventStackMap

record EventStackMap
  (E F : EventStack)
  : Set
  where

  field

    mode
      : EventStack.Mode E
      → EventStack.Mode F

    mode-inner
      : EventStack.ModeInner E
      → EventStack.ModeInner F

    event
      : (m : EventStack.Mode E)
      → EventStack.Event F (mode m)
      → EventStack.Event E m

    event-inner
      : (m : EventStack.ModeInner E)
      → EventStack.EventInner F (mode-inner m)
      → EventStack.EventInner E m

