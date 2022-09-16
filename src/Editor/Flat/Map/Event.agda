module Editor.Flat.Map.Event where

open import Editor.Flat
  using (FlatEditor)
open import Stack.Flat
  using (FlatEventStack; FlatEventStackMap; FlatViewStack)

-- ## FlatEditor

flat-editor-map-event
  : {V : FlatViewStack}
  → {E F : FlatEventStack}
  → {A : Set}
  → FlatEventStackMap E F
  → FlatEditor V E A
  → FlatEditor V F A
flat-editor-map-event G e
  = record
  { FlatEditor e
  ; mode
    = λ s sp → FlatEventStackMap.mode G
      (FlatEditor.mode e s sp)
  ; handle
    = λ s sp e' → FlatEditor.handle e s sp
      (FlatEventStackMap.event G (FlatEditor.mode e s sp) e')
  }

