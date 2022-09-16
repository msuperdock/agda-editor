module Editor.Simple.Base.TextWith where

open import Data.Bool
  using (Bool)
open import Data.Char
  using (Char)
open import Data.CharWith
  using (CharWith)
open import Data.Direction
  using (Direction)
open import Data.Equal
  using (_≡_; refl)
open import Data.Fin
  using (Fin; suc; zero)
open import Data.List
  using (List; []; _∷_)
open import Data.Maybe
  using (Maybe; nothing)
open import Data.Nat
  using (suc)
open import Data.Sigma
  using (Σ; _,_)
open import Data.TextWith
  using (TextWith)
open import Editor.Simple.Base
  using (SimpleBaseEditor)
open import Event.TextWith
  using (TextWithEvent)
open import Stack.Base
  using (BaseEventStack; BaseViewStack)
open import Stack.Base.Text
  using (base-view-stack-text)
open import Stack.Base.TextWith
  using (base-event-stack-text-with)

-- ## SimpleBaseEditor

-- ### Module

module SimpleBaseEditorTextWith
  (p : Char → Bool)
  where

  -- #### Types

  open BaseViewStack base-view-stack-text
  open BaseEventStack (base-event-stack-text-with p)

  State
    : Set
  State
    = List (CharWith p)

  -- #### State

  StatePath
    : State
    → Set
  StatePath cs
    = Fin (suc (List.length cs))

  initial
    : State
  initial
    = []

  initial-path
    : (s : State)
    → StatePath s
  initial-path cs
    = Fin.maximum (List.length cs)

  initial-path-with
    : (s : State)
    → Direction
    → StatePath s
  initial-path-with _ Direction.up
    = zero
  initial-path-with _ Direction.down
    = zero
  initial-path-with _ Direction.left
    = zero
  initial-path-with cs Direction.right
    = Fin.maximum (List.length cs)

  -- #### Draw

  draw
    : State
    → View
  draw
    = List.map CharWith.char

  draw-with
    : (s : State)
    → StatePath s
    → View
  draw-with s _
    = draw s

  draw-path
    : (s : State)
    → (sp : StatePath s)
    → ViewPath (draw-with s sp)
  draw-path _
    = Fin.drop

  -- #### Handle

  handle
    : (s : State)
    → StatePath s
    → Event
    → Σ State StatePath
  handle cs zero TextWithEvent.delete-previous
    = (cs , zero)
  handle cs@(_ ∷ _) (suc k) TextWithEvent.delete-previous
    = (List.delete cs k , k)
  handle [] _ TextWithEvent.delete-next
    = ([] , zero)
  handle (_ ∷ cs) zero TextWithEvent.delete-next
    = (cs , zero)
  handle (c ∷ cs) (suc k) TextWithEvent.delete-next
    with handle cs k TextWithEvent.delete-next
  ... | (cs' , k')
    = (c ∷ cs' , suc k')
  handle cs k (TextWithEvent.insert c)
    = (List.insert cs k c , suc k)

  handle-direction
    : (s : State)
    → StatePath s
    → Direction
    → Maybe (StatePath s)
  handle-direction _ _ Direction.up
    = nothing
  handle-direction _ _ Direction.down
    = nothing
  handle-direction _ k Direction.left
    = Fin.decrement k
  handle-direction _ k Direction.right
    = Fin.increment k

  handle-direction-valid
    : (s : State)
    → (d : Direction)
    → handle-direction s (initial-path-with s d) d ≡ nothing
  handle-direction-valid _ Direction.up
    = refl
  handle-direction-valid _ Direction.down
    = refl
  handle-direction-valid _ Direction.left
    = refl
  handle-direction-valid cs Direction.right
    = Fin.increment-maximum (List.length cs)

-- ### Function

simple-base-editor-text-with
  : (p : Char → Bool)
  → SimpleBaseEditor
    base-view-stack-text
    (base-event-stack-text-with p)
    (TextWith p)
simple-base-editor-text-with p
  = record {SimpleBaseEditorTextWith p}

