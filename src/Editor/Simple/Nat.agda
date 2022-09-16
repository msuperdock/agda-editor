module Editor.Simple.Nat where

open import Category.Simple.Split.Nat
  using (simple-split-functor-nat)
open import Data.Char
  using (Char)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)
open import Data.Text
  using (Text)
open import Editor.Simple
  using (SimpleInnerEditor; SimpleMainEditor; SimplePartialEditor;
    SimpleSplitEditor)
open import Editor.Simple.TextWith
  using (simple-editor-text-with)
open import Encoding.Identity
  using (encoding-identity)
open import Encoding.Text
  using (encoding-text)
open import Stack.Nat
  using (event-stack-nat)
open import Stack.Text
  using (view-stack-text)

-- ## Nondependent

-- ### SimpleInnerEditor

simple-inner-editor-nat
  : SimpleInnerEditor
    view-stack-text
    event-stack-nat
    Text
    ℕ
    ℕ
simple-inner-editor-nat
  = record
  { editor
    = simple-editor-text-with Char.is-digit
  ; state-encoding
    = encoding-text Char.is-digit
  ; encoding
    = encoding-identity ℕ
  ; split-functor
    = simple-split-functor-nat
  }

-- ### SimplePartialEditor

simple-partial-editor-nat
  : SimplePartialEditor
    view-stack-text
    event-stack-nat
    ℕ
simple-partial-editor-nat
  = SimpleInnerEditor.partial-editor
  $ simple-inner-editor-nat

-- ### SimpleSplitEditor

simple-split-editor-nat
  : SimpleSplitEditor
    view-stack-text
    event-stack-nat
    ℕ
simple-split-editor-nat
  = SimpleInnerEditor.split-editor
  $ simple-inner-editor-nat

-- ### SimpleMainEditor

simple-main-editor-nat
  : SimpleMainEditor
    view-stack-text
    event-stack-nat
    Text
simple-main-editor-nat
  = SimpleInnerEditor.main-editor
  $ simple-inner-editor-nat

