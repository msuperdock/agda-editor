module Client.Run where

open import Client
  using (Client)
open import Client.Aeson
  using (Value; decode; encode; is-file; read-file; write-file)
open import Client.Brick
  using (App; AttributeMap; BrickEvent; CursorLocation; EventM; Next; Widget;
    app; attribute-map; continue; default-main; event-bind; event-pure;
    from-brick-event; halt; liftIO)
open import Client.Event
  using (SpecialEvent)
open import Client.Flat
  using (FlatClient)
open import Client.Flatten
  using (client-flatten)
open import Data.Bool
  using (Bool; false; true)
open import Data.Function
  using (_∘_; const)
open import Data.IO
  using (IO; _>>=_)
open import Data.List
  using (List; List'; []; _∷_)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Sigma
  using (Σ; _,_)
open import Data.String
  using (String)
open import Data.Sum
  using (ι₁; ι₂)
open import Data.Unit
  using (⊤; tt)
open import Editor.Flat
  using (FlatMainEditor)
open import Editor.Simple
  using (SimpleMainEditor)
open import Editor.Simple.Flatten
  using (simple-main-editor-flatten)
open import Stack
  using (EventStack; ViewStack)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack)

-- ## FlatMainEditor

module _
  {V : FlatViewStack}
  {E : FlatEventStack}
  where

  module FlatMainEditorRun
    (p : String)
    (e : FlatMainEditor V E Value)
    (c : FlatClient V E)
    where

    State
      : Set
    State
      = s ∈ FlatMainEditor.State e
      × FlatMainEditor.StatePath e s

    initial
      : Maybe Value
      → State
    initial nothing
      = FlatMainEditor.initial e
      , FlatMainEditor.initial-path e
    initial (just s)
      = FlatMainEditor.initial-with e s
      , FlatMainEditor.initial-path-with e s

    draw
      : State
      → List Widget
    draw (s , sp)
      = FlatClient.draw c
        (FlatMainEditor.draw-with e s sp)
        (FlatMainEditor.draw-path e s sp)
      ∷ []

    draw'
      : State
      → List' Widget
    draw' s
      = List.to-builtin (draw s)

    cursor
      : List CursorLocation
      → Maybe CursorLocation
    cursor []
      = nothing
    cursor (c ∷ _)
      = just c

    cursor'
      : State
      → List' CursorLocation
      → Maybe CursorLocation
    cursor' _ cs
      = cursor (List.from-builtin cs)

    write
      : State
      → IO ⊤
    write (s , _)
      = write-file p (encode (FlatMainEditor.handle-save e s))

    handle
      : State
      → BrickEvent
      → EventM (Next State)
    handle (s , sp) e'
      with from-brick-event e'
    ... | nothing
      = continue (s , sp)
    ... | just e''
      with FlatClient.handle c (FlatMainEditor.mode e s sp) e''
    ... | nothing
      = continue (s , sp)
    ... | just (ι₁ e''')
      = continue (FlatMainEditor.handle e s sp e''')
    ... | just (ι₂ SpecialEvent.quit)
      = halt (s , sp)
    ... | just (ι₂ SpecialEvent.write)
      = event-bind (liftIO (write (s , sp))) (const (continue (s , sp)))
    ... | just (ι₂ SpecialEvent.escape)
      = continue (FlatMainEditor.handle-escape e s sp)
    ... | just (ι₂ SpecialEvent.return)
      = continue (FlatMainEditor.handle-return e s sp)
    ... | just (ι₂ (SpecialEvent.direction d))
      = continue (s , FlatMainEditor.handle-direction e s sp d)

    start
      : State
      → EventM State
    start
      = event-pure

    attributes'
      : State
      → AttributeMap
    attributes' _
      = attribute-map (FlatClient.attributes c)

    app'
      : App State
    app'
      = app draw' cursor' handle start attributes'

    decode-file
      : Bool
      → IO (Maybe Value)
    decode-file false
      = IO.return nothing
    decode-file true
      = read-file p
      >>= IO.return ∘ decode

    main
      : IO ⊤
    main
      = is-file p
      >>= decode-file
      >>= default-main app' ∘ initial
      >>= const (IO.return tt)

  flat-main-editor-run
    : String
    → FlatMainEditor V E Value
    → FlatClient V E
    → IO ⊤
  flat-main-editor-run
    = FlatMainEditorRun.main

-- ## MainEditor

simple-main-editor-run
  : {V : ViewStack}
  → {E : EventStack}
  → String
  → SimpleMainEditor V E Value
  → Client V E
  → IO ⊤
simple-main-editor-run p e c
  = flat-main-editor-run p
    (simple-main-editor-flatten e)
    (client-flatten c)

