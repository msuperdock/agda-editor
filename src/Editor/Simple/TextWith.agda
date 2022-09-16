module Editor.Simple.TextWith where

open import Data.Bool
  using (Bool)
open import Data.Char
  using (Char)
open import Data.TextWith
  using (TextWith)
open import Editor.Simple
  using (SimpleEditor)
open import Editor.Simple.Base.TextWith
  using (simple-base-editor-text-with)
open import Editor.Simple.Lift
  using (simple-editor-lift)
open import Stack.Text
  using (view-stack-text)
open import Stack.TextWith
  using (event-stack-text-with)

-- ## Base

-- ### SimpleEditor

simple-editor-text-with
  : (p : Char → Bool)
  → SimpleEditor
    view-stack-text
    (event-stack-text-with p)
    (TextWith p)
simple-editor-text-with p
  = simple-editor-lift
    (simple-base-editor-text-with p)

