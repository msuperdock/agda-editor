module Editor.Flat.Text where

open import Data.Function
  using (_$_)
open import Data.Text
  using (Text)
open import Editor.Flat
  using (FlatEditor)
open import Editor.Flat.Map.Event
  using (flat-editor-map-event)
open import Editor.Flat.Map.View
  using (flat-editor-map-view)
open import Editor.Simple.Flatten
  using (simple-inner-editor-flatten)
open import Editor.Simple.Text
  using (simple-inner-editor-text)
open import Stack.Base.Flatten
  using (base-event-stack-flatten-lift; base-view-stack-flatten-lift)
open import Stack.Base.Text
  using (base-event-stack-text; base-view-stack-text)
open import Stack.Flat.Text
  using (flat-event-stack-text; flat-view-stack-text)

-- ## FlatEditor

flat-editor-text
  : FlatEditor
    flat-view-stack-text
    flat-event-stack-text
    Text
flat-editor-text
  = flat-editor-map-view (base-view-stack-flatten-lift base-view-stack-text)
  $ flat-editor-map-event (base-event-stack-flatten-lift base-event-stack-text)
  $ simple-inner-editor-flatten
  $ simple-inner-editor-text

