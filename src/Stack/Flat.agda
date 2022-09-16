module Stack.Flat where

-- ## Stacks

-- ### FlatViewStack

record FlatViewStack
  : Set₁
  where

  field

    View
      : Set

    ViewPath
      : View
      → Set

-- ### FlatEventStack

record FlatEventStack
  : Set₁
  where

  field

    Mode
      : Set

    Event
      : Mode
      → Set

-- ## StackMaps

-- ### FlatViewStackMap

record FlatViewStackMap
  (V W : FlatViewStack)
  : Set
  where

  field

    view-with
      : (v : FlatViewStack.View V)
      → FlatViewStack.ViewPath V v
      → FlatViewStack.View W
    
    view-path
      : (v : FlatViewStack.View V)
      → (vp : FlatViewStack.ViewPath V v)
      → FlatViewStack.ViewPath W (view-with v vp)

-- ### FlatEventStackMap

record FlatEventStackMap
  (E F : FlatEventStack)
  : Set
  where

  field

    mode
      : FlatEventStack.Mode E
      → FlatEventStack.Mode F

    event
      : (m : FlatEventStack.Mode E)
      → FlatEventStack.Event F (mode m)
      → FlatEventStack.Event E m

