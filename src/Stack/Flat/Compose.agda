module Stack.Flat.Compose where

open import Stack.Flat
  using (FlatViewStack; FlatViewStackMap)

-- ## StackMaps

-- ### FlatViewStackMap

flat-view-stack-map-compose
  : {V W X : FlatViewStack}
  → FlatViewStackMap W X
  → FlatViewStackMap V W
  → FlatViewStackMap V X
flat-view-stack-map-compose F G
  = record
  { view-with
    = λ v vp → FlatViewStackMap.view-with F
      (FlatViewStackMap.view-with G v vp)
      (FlatViewStackMap.view-path G v vp)
  ; view-path
    = λ v vp → FlatViewStackMap.view-path F
      (FlatViewStackMap.view-with G v vp)
      (FlatViewStackMap.view-path G v vp)
  }

