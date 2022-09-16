module Editor.Simple.Lift where

open import Data.Function
  using (_∘_)
open import Editor.Base.Unit
  using (base-editor-unit)
open import Editor.Lift
  using (editor-lift)
open import Editor.Simple
  using (SimpleEditor; editor-simple)
open import Editor.Simple.Base
  using (SimpleBaseEditor)
open import Stack.Base
  using (BaseEventStack; BaseViewStack)
open import Stack.Lift
  using (event-stack-lift; view-stack-lift)

-- ## SimpleEditor

simple-editor-lift
  : {V : BaseViewStack}
  → {E : BaseEventStack}
  → {A : Set}
  → SimpleBaseEditor V E A
  → SimpleEditor
    (view-stack-lift V)
    (event-stack-lift E) A
simple-editor-lift
  = editor-simple
  ∘ editor-lift
  ∘ base-editor-unit

