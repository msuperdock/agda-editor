module Editor.Base.Unit where

open import Category.Core.Unit
  using (module ArrowUnit)
open import Category.State
  using (StateCategory)
open import Category.State.Unit
  using (state-category-unit)
open import Data.Sigma
  using (Σ; _,_)
open import Editor.Base
  using (BaseEditor)
open import Editor.Simple.Base
  using (SimpleBaseEditor)
open import Stack.Base
  using (BaseEventStack; BaseViewStack)

-- ### BaseEditor

module _
  {V : BaseViewStack}
  {E : BaseEventStack}
  {A : Set}
  where

  module BaseEditorUnit
    (e : SimpleBaseEditor V E A)
    where

    open BaseEventStack E

    open StateCategory (state-category-unit A)
      using () renaming
      ( Object
        to State
      ; Arrow
        to StateArrow
      )

    open SimpleBaseEditor e public
      hiding (handle)

    handle
      : (s : State)
      → StatePath s
      → Event
      → s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
    handle s sp e'
      with SimpleBaseEditor.handle e s sp e'
    ... | (s' , sp')
      = (s' , sp' , ArrowUnit.tt)

  base-editor-unit
    : SimpleBaseEditor V E A
    → BaseEditor V E
      (state-category-unit A)
  base-editor-unit e
    = record {BaseEditorUnit e}

