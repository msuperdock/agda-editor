module Editor.Unit where

open import Category
  using (ChainCategory)
open import Category.Core.Unit
  using (module ArrowUnit)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Split.Unit
  using (dependent-split-functor-unit)
open import Category.State
  using (StateCategory)
open import Category.State.Unit
  using (dependent-state-category-unit; state-category-unit)
open import Category.Unit
  using (category-unit; dependent-category-unit)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Editor
  using (DependentEditor; DependentInnerEditor; DependentSplitEditor; Editor;
    InnerEditor; SplitEditor)
open import Editor.Simple
  using (DependentSimpleEditor; DependentSimpleInnerEditor;
    DependentSimpleSplitEditor; SimpleEditor; SimpleInnerEditor;
    SimpleSplitEditor)
open import Encoding.Unit
  using (dependent-encoding-unit)
open import Encoding.State.Unit
  using (dependent-state-encoding-unit)
open import Stack
  using (EventStack; ViewStack)

-- ## Base

-- ### Editor

module _
  {V : ViewStack}
  {E : EventStack}
  {A : Set}
  where

  module EditorUnit
    (e : SimpleEditor V E A)
    where

    open EventStack E

    open StateCategory (state-category-unit A)
      using () renaming
      ( Object
        to State
      ; Arrow
        to StateArrow
      )

    open SimpleEditor e public
      hiding (handle; handle-escape; handle-return; handle-inner-return)

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle s sp e'
      with SimpleEditor.handle e s sp e'
    ... | ι₁ (s' , sp')
      = ι₁ (s' , sp' , ArrowUnit.tt)
    ... | ι₂ s'
      = ι₂ s'

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-escape s sp
      with SimpleEditor.handle-escape e s sp
    ... | nothing
      = nothing
    ... | just (ι₁ (s' , sp'))
      = just (ι₁ (s' , sp' , ArrowUnit.tt))
    ... | just (ι₂ s')
      = just (ι₂ s')

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-return s sp
      with SimpleEditor.handle-return e s sp
    ... | nothing
      = nothing
    ... | just (ι₁ (s' , sp'))
      = just (ι₁ (s' , sp' , ArrowUnit.tt))
    ... | just (ι₂ s')
      = just (ι₂ s')

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return s sp s' sp'
      with SimpleEditor.handle-inner-return e s sp s' sp'
    ... | ι₁ (s'' , sp'')
      = ι₁ (s'' , sp'' , ArrowUnit.tt)
    ... | ι₂ s''
      = ι₂ s''

  editor-unit
    : SimpleEditor V E A
    → Editor V E
      (state-category-unit A)
  editor-unit e
    = record {EditorUnit e}

-- ## Dependent

-- ### DependentEditor

dependent-editor-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → DependentSimpleEditor V E C'
  → DependentEditor V E
    (dependent-state-category-unit C')
dependent-editor-unit {n = zero} e
  = editor-unit e
dependent-editor-unit {n = suc _} e
  = record
  { tail
    = λ x → dependent-editor-unit
      (DependentSimpleEditor.tail e x)
  }

-- ### DependentSplitEditor

dependent-split-editor-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → DependentSimpleSplitEditor V E C'
  → DependentSplitEditor V E
    (dependent-category-unit C')
dependent-split-editor-unit e
  = record
  { editor
    = dependent-editor-unit
      (DependentSimpleSplitEditor.editor e)
  ; split-functor
    = dependent-split-functor-unit
      (DependentSimpleSplitEditor.split-functor e)
  }

-- ### DependentInnerEditor

dependent-inner-editor-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → DependentSimpleInnerEditor V E S P C'
  → DependentInnerEditor V E S P
    (dependent-category-unit C')
dependent-inner-editor-unit e
  = record
  { editor
    = dependent-editor-unit
      (DependentSimpleInnerEditor.editor e)
  ; state-encoding
    = dependent-state-encoding-unit
      (DependentSimpleInnerEditor.state-encoding e)
  ; encoding
    = dependent-encoding-unit
      (DependentSimpleInnerEditor.encoding e)
  ; split-functor
    = dependent-split-functor-unit
      (DependentSimpleInnerEditor.split-functor e)
  }

-- ## Nondependent

-- ### SplitEditor

split-editor-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → SimpleSplitEditor V E A
  → SplitEditor V E
    (category-unit A)
split-editor-unit
  = dependent-split-editor-unit

-- ### InnerEditor

inner-editor-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {S P A : Set}
  → SimpleInnerEditor V E S P A
  → InnerEditor V E S P
    (category-unit A)
inner-editor-unit
  = dependent-inner-editor-unit

