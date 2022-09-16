module Editor.Simple.Parent where

open import Data.Function
  using (_$_)
open import Editor.Base.Unit
  using (base-editor-unit)
open import Editor.Flat
  using (FlatEditor)
open import Editor.Parent
  using (editor-parent)
open import Editor.Simple
  using (SimpleEditor; editor-simple)
open import Editor.Simple.Base
  using (SimpleBaseEditor)
open import Stack.Base
  using (BaseEventStack; BaseViewStack)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack)
open import Stack.Parent
  using (event-stack-parent; view-stack-parent)

-- ## SimpleEditor

simple-editor-parent
  : {K A : Set}
  → {V : BaseViewStack}
  → {E : BaseEventStack}
  → (V' : K → FlatViewStack)
  → (E' : K → FlatEventStack)
  → SimpleBaseEditor V E A
  → ((k : K) → FlatEditor (V' k) (E' k) (BaseEventStack.Event E))
  → SimpleEditor
    (view-stack-parent V V')
    (event-stack-parent E E') A
simple-editor-parent V' E' e e'
  = editor-simple
  $ editor-parent V' E'
    (base-editor-unit e) e'

