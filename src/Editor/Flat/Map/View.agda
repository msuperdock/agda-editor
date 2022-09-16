module Editor.Flat.Map.View where

open import Editor.Flat
  using (FlatEditor)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack; FlatViewStackMap)
open import Stack.Flat.Compose
  using (flat-view-stack-map-compose)

-- ## FlatEditor

flat-editor-map-view
  : {V W : FlatViewStack}
  → {E : FlatEventStack}
  → {A : Set}
  → FlatViewStackMap V W
  → FlatEditor V E A
  → FlatEditor W E A
flat-editor-map-view F e
  = record
  { FlatEditor e
  ; draw-stack
    = flat-view-stack-map-compose F
      (FlatEditor.draw-stack e)
  }

