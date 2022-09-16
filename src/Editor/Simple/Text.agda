module Editor.Simple.Text where

open import Category.Simple.Split.Text
  using (simple-split-functor-text)
open import Data.Bool
  using (true)
open import Data.Function
  using (_$_; const)
open import Data.Text
  using (Text)
open import Data.TextWith
  using (TextWith)
open import Editor.Simple
  using (SimpleEditor; SimpleInnerEditor; SimpleMainEditor; SimplePartialEditor;
    SimpleSplitEditor)
open import Editor.Simple.Map.Event
  using (simple-editor-map-event)
open import Editor.Simple.TextWith
  using (simple-editor-text-with)
open import Encoding.Identity
  using (encoding-identity)
open import Encoding.Text
  using (encoding-text)
open import Stack.Text
  using (event-stack-text; event-stack-map-text; view-stack-text)

-- ## Base

-- ### SimpleEditor

simple-editor-text
  : SimpleEditor
    view-stack-text
    event-stack-text
    (TextWith (const true))
simple-editor-text
  = simple-editor-map-event event-stack-map-text
  $ simple-editor-text-with (const true)

-- ## Nondependent

-- ### SimpleInnerEditor

simple-inner-editor-text
  : SimpleInnerEditor
    view-stack-text
    event-stack-text
    Text
    Text
    Text
simple-inner-editor-text
  = record
  { editor
    = simple-editor-text
  ; state-encoding
    = encoding-text (const true)
  ; encoding
    = encoding-identity Text
  ; split-functor
    = simple-split-functor-text
  }

-- ### SimplePartialEditor

simple-partial-editor-text
  : SimplePartialEditor
    view-stack-text
    event-stack-text
    Text
simple-partial-editor-text
  = SimpleInnerEditor.partial-editor
  $ simple-inner-editor-text

-- ### SimpleSplitEditor

simple-split-editor-text
  : SimpleSplitEditor
    view-stack-text
    event-stack-text
    Text
simple-split-editor-text
  = SimpleInnerEditor.split-editor
  $ simple-inner-editor-text

-- ### SimpleMainEditor

simple-main-editor-text
  : SimpleMainEditor
    view-stack-text
    event-stack-text
    Text
simple-main-editor-text
  = SimpleInnerEditor.main-editor
  $ simple-inner-editor-text

