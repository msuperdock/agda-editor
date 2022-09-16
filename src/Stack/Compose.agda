module Stack.Compose where

open import Stack
  using (ViewStack; ViewStackMap)

-- ## StackMaps

-- ### ViewStackMap

module _
  {V W X : ViewStack}
  where

  module ViewStackMapComposeWith
    (F : ViewStack.View V → ViewStackMap W X)
    (G : ViewStackMap V W)
    where

    view
      : ViewStack.View V
      → ViewStack.View X
    view v
      = ViewStackMap.view (F v)
        (ViewStackMap.view G v)

    view-with
      : (v : ViewStack.View V)
      → ViewStack.ViewPath V v
      → ViewStack.View X
    view-with v vp
      = ViewStackMap.view-with (F v)
        (ViewStackMap.view-with G v vp)
        (ViewStackMap.view-path G v vp)
    
    view-path
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → ViewStack.ViewPath X
        (view-with v vp)
    view-path v vp
      = ViewStackMap.view-path (F v)
        (ViewStackMap.view-with G v vp)
        (ViewStackMap.view-path G v vp)

    view-inner-with
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → (v' : ViewStack.ViewInner V v vp)
      → ViewStack.ViewInnerPath V v vp v'
      → ViewStack.ViewInner X
        (view-with v vp)
        (view-path v vp)
    view-inner-with v vp v' vp'
      = ViewStackMap.view-inner-with (F v)
        (ViewStackMap.view-with G v vp)
        (ViewStackMap.view-path G v vp)
        (ViewStackMap.view-inner-with G v vp v' vp')
        (ViewStackMap.view-inner-path G v vp v' vp')

    view-inner-path
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → (v' : ViewStack.ViewInner V v vp)
      → (vp' : ViewStack.ViewInnerPath V v vp v')
      → ViewStack.ViewInnerPath X
        (view-with v vp)
        (view-path v vp)
        (view-inner-with v vp v' vp')
    view-inner-path v vp v' vp'
      = ViewStackMap.view-inner-path (F v)
        (ViewStackMap.view-with G v vp)
        (ViewStackMap.view-path G v vp)
        (ViewStackMap.view-inner-with G v vp v' vp')
        (ViewStackMap.view-inner-path G v vp v' vp')

  view-stack-map-compose-with
    : (ViewStack.View V → ViewStackMap W X)
    → ViewStackMap V W
    → ViewStackMap V X
  view-stack-map-compose-with F G
    = record {ViewStackMapComposeWith F G}

