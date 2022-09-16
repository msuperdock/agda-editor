module Editor.Flat.Map where

open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Editor.Flat
  using (FlatEditor)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack)

-- ## FlatEditor

module _
  {V : FlatViewStack}
  {E : FlatEventStack}
  {A B : Set}
  where

  module FlatEditorMap
    (f : A → Maybe B)
    (e : FlatEditor V E A)
    where

    open FlatEditor e public
      hiding (handle-return)

    handle-return
      : (s : State)
      → StatePath s
      → B ⊔ Σ State StatePath
    handle-return s sp
      with FlatEditor.handle-return e s sp
    ... | ι₂ s'
      = ι₂ s'
    ... | ι₁ x
      with f x
    ... | nothing
      = ι₂ (s , sp)
    ... | just y
      = ι₁ y

  flat-editor-map
    : (A → Maybe B)
    → FlatEditor V E A
    → FlatEditor V E B
  flat-editor-map f e
    = record {FlatEditorMap f e}

