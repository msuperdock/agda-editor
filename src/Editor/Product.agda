module Editor.Product where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.Product
  using (category-product; dependent-category-product)
open import Category.Split.Product
  using (dependent-split-functor-product)
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Category.State.Product
  using (dependent-state-category-product; state-category-product)
open import Data.Direction
  using (Direction; _≟_dir)
open import Data.Empty
  using (⊥-elim)
open import Data.Equal
  using (_≡_; refl)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Relation
  using (no; yes)
open import Data.Sigma
  using (Σ; _×_; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Editor
  using (DependentEditor; DependentInnerEditor; DependentSplitEditor; Editor;
    InnerEditor; SplitEditor)
open import Encoding.Product
  using (dependent-encoding-product)
open import Encoding.State.Product
  using (dependent-state-encoding-product)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)
open import Stack.Product
  using (event-stack-product; view-stack-map-product; view-stack-product)

-- ## Base

-- ### Editor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {C₁ C₂ : StateCategory}
  where

  -- #### Module

  module EditorProduct
    (d : Direction)
    (e₁ : Editor V₁ E₁ C₁)
    (e₂ : Editor V₂ E₂ C₂)
    where

    -- ##### Types

    open EventStack (event-stack-product E₁ E₂)

    open StateCategory (state-category-product C₁ C₂)
      using () renaming
      ( Object
        to State
      ; Arrow
        to StateArrow
      )

    -- ##### State

    StateStack
      : ViewStack
    StateStack
      = view-stack-product
        (Editor.StateStack e₁)
        (Editor.StateStack e₂)

    open ViewStack StateStack public
      using () renaming
      ( ViewPath
        to StatePath
      ; ViewInner
        to StateInner
      ; ViewInnerPath
        to StateInnerPath
      )

    initial
      : State
    initial
      = Editor.initial e₁
      , Editor.initial e₂

    initial-path
      : (s : State)
      → StatePath s
    initial-path (s₁ , _)
      = ι₁ (Editor.initial-path e₁ s₁)

    initial-path-with
      : (s : State)
      → Direction
      → StatePath s
    initial-path-with (s₁ , s₂) d'
      with d' ≟ d dir
    ... | no _
      = ι₁ (Editor.initial-path-with e₁ s₁ d')
    ... | yes _
      = ι₂ (Editor.initial-path-with e₂ s₂ d')

    -- ##### Draw

    draw-stack
      : ViewStackMap StateStack (view-stack-product V₁ V₂)
    draw-stack
      = view-stack-map-product
        (Editor.draw-stack e₁)
        (Editor.draw-stack e₂)

    -- ##### Mode

    mode
      : (s : State)
      → StatePath s
      → Mode
    mode (s₁ , _) (ι₁ sp₁)
      = ι₁ (Editor.mode e₁ s₁ sp₁)
    mode (_ , s₂) (ι₂ sp₂)
      = ι₂ (Editor.mode e₂ s₂ sp₂)

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner
    mode-inner (s₁ , _) (ι₁ sp₁) s₁' sp₁'
      = ι₁ (Editor.mode-inner e₁ s₁ sp₁ s₁' sp₁')
    mode-inner (_ , s₂) (ι₂ sp₂) s₂' sp₂'
      = ι₂ (Editor.mode-inner e₂ s₂ sp₂ s₂' sp₂')

    -- ##### Handle

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle (s₁ , s₂) (ι₁ sp₁) e₁'
      with Editor.handle e₁ s₁ sp₁ e₁'
    ... | ι₁ (s₁' , sp₁' , f₁)
      = ι₁ ((s₁' , s₂) , ι₁ sp₁' , (f₁ , StateCategory.identity' C₂ s₂))
    ... | ι₂ s₁'
      = ι₂ s₁'
    handle (s₁ , s₂) (ι₂ sp₂) e₂'
      with Editor.handle e₂ s₂ sp₂ e₂'
    ... | ι₁ (s₂' , sp₂' , f₂)
      = ι₁ ((s₁ , s₂') , ι₂ sp₂' , (StateCategory.identity' C₁ s₁ , f₂))
    ... | ι₂ s₂'
      = ι₂ s₂'

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-escape (s₁ , s₂) (ι₁ sp₁)
      with Editor.handle-escape e₁ s₁ sp₁
    ... | nothing
      = nothing
    ... | just (ι₁ (s₁' , sp₁' , f₁))
      = just (ι₁ ((s₁' , s₂) , ι₁ sp₁' , (f₁ , StateCategory.identity' C₂ s₂)))
    ... | just (ι₂ s₁')
      = just (ι₂ s₁')
    handle-escape (s₁ , s₂) (ι₂ sp₂)
      with Editor.handle-escape e₂ s₂ sp₂
    ... | nothing
      = nothing
    ... | just (ι₁ (s₂' , sp₂' , f₂))
      = just (ι₁ ((s₁ , s₂') , ι₂ sp₂' , (StateCategory.identity' C₁ s₁ , f₂)))
    ... | just (ι₂ s₂')
      = just (ι₂ s₂')

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-return (s₁ , s₂) (ι₁ sp₁)
      with Editor.handle-return e₁ s₁ sp₁
    ... | nothing
      = nothing
    ... | just (ι₁ (s₁' , sp₁' , f₁))
      = just (ι₁ ((s₁' , s₂) , ι₁ sp₁' , (f₁ , StateCategory.identity' C₂ s₂)))
    ... | just (ι₂ s₁')
      = just (ι₂ s₁')
    handle-return (s₁ , s₂) (ι₂ sp₂)
      with Editor.handle-return e₂ s₂ sp₂
    ... | nothing
      = nothing
    ... | just (ι₁ (s₂' , sp₂' , f₂))
      = just (ι₁ ((s₁ , s₂') , ι₂ sp₂' , (StateCategory.identity' C₁ s₁ , f₂)))
    ... | just (ι₂ s₂')
      = just (ι₂ s₂')

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → Maybe (StatePath s)
    handle-direction (s₁ , s₂) (ι₁ sp₁) d'
      with Editor.handle-direction e₁ s₁ sp₁ d'
      | d' ≟ d dir
    ... | nothing | no _
      = nothing
    ... | nothing | yes _
      = just (ι₂ (Editor.initial-path-with e₂ s₂ (Direction.reverse d')))
    ... | just sp₁' | _
      = just (ι₁ sp₁')
    handle-direction (s₁ , s₂) (ι₂ sp₂) d'
      with Editor.handle-direction e₂ s₂ sp₂ d'
      | Direction.reverse d' ≟ d dir
    ... | nothing | no _
      = nothing
    ... | nothing | yes _
      = just (ι₁ (Editor.initial-path-with e₁ s₁ (Direction.reverse d')))
    ... | just sp₂' | _
      = just (ι₂ sp₂')

    handle-direction-valid
      : (s : State)
      → (d' : Direction)
      → handle-direction s (initial-path-with s d') d' ≡ nothing
    handle-direction-valid _ d'
      with d' ≟ d dir
      | inspect (_≟_dir d') d
    handle-direction-valid (s₁ , _) d' | no _ | [ _ ]
      with Editor.handle-direction e₁ s₁ (Editor.initial-path-with e₁ s₁ d') d'
      | Editor.handle-direction-valid e₁ s₁ d'
      | d' ≟ d dir
    handle-direction-valid _ _ _ | _ | [ refl ] | _ | refl | _
      = refl
    handle-direction-valid (_ , s₂) d' | yes refl | _
      with Editor.handle-direction e₂ s₂ (Editor.initial-path-with e₂ s₂ d') d'
      | Editor.handle-direction-valid e₂ s₂ d'
      | Direction.reverse d' ≟ d dir
    ... | _ | refl | no _
      = refl
    ... | _ | _ | yes p
      = ⊥-elim (Direction.reverse-≢ d' p)

    handle-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → EventInner (mode-inner s sp s' sp')
      → Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner (s₁ , _) (ι₁ sp₁)
      = Editor.handle-inner e₁ s₁ sp₁
    handle-inner (_ , s₂) (ι₂ sp₂)
      = Editor.handle-inner e₂ s₂ sp₂

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))
    handle-inner-escape (s₁ , _) (ι₁ sp₁)
      = Editor.handle-inner-escape e₁ s₁ sp₁
    handle-inner-escape (_ , s₂) (ι₂ sp₂)
      = Editor.handle-inner-escape e₂ s₂ sp₂

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return (s₁ , s₂) (ι₁ sp₁) s₁' sp₁'
      with Editor.handle-inner-return e₁ s₁ sp₁ s₁' sp₁'
    ... | ι₁ (s₁'' , sp₁'' , f₁)
      = ι₁ ((s₁'' , s₂) , ι₁ sp₁'' , (f₁ , StateCategory.identity' C₂ s₂))
    ... | ι₂ s₁''
      = ι₂ s₁''
    handle-inner-return (s₁ , s₂) (ι₂ sp₂) s₂' sp₂'
      with Editor.handle-inner-return e₂ s₂ sp₂ s₂' sp₂'
    ... | ι₁ (s₂'' , sp₂'' , f₂)
      = ι₁ ((s₁ , s₂'') , ι₂ sp₂'' , (StateCategory.identity' C₁ s₁ , f₂))
    ... | ι₂ s₂''
      = ι₂ s₂''

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'
    handle-inner-direction (s₁ , _) (ι₁ sp₁)
      = Editor.handle-inner-direction e₁ s₁ sp₁
    handle-inner-direction (_ , s₂) (ι₂ sp₂)
      = Editor.handle-inner-direction e₂ s₂ sp₂

  -- #### Function

  -- Takes direction from first to second component.
  editor-product
    : Direction
    → Editor V₁ E₁ C₁
    → Editor V₂ E₂ C₂
    → Editor
      (view-stack-product V₁ V₂)
      (event-stack-product E₁ E₂)
      (state-category-product C₁ C₂)
  editor-product d e₁ e₂
    = record {EditorProduct d e₁ e₂}

-- ## Dependent

-- ### DependentEditor

-- Takes direction from first to second component.
dependent-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentStateCategory C}
  → Direction
  → DependentEditor V₁ E₁ C₁'
  → DependentEditor V₂ E₂ C₂'
  → DependentEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (dependent-state-category-product C₁' C₂')
dependent-editor-product {n = zero} d e₁ e₂
  = editor-product d e₁ e₂
dependent-editor-product {n = suc _} d e₁ e₂
  = record
  { tail
    = λ x → dependent-editor-product d
      (DependentEditor.tail e₁ x)
      (DependentEditor.tail e₂ x)
  }

-- ### DependentSplitEditor

-- Takes direction from first to second component.
dependent-split-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → Direction
  → DependentSplitEditor V₁ E₁ C₁'
  → DependentSplitEditor V₂ E₂ C₂'
  → DependentSplitEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (dependent-category-product C₁' C₂')
dependent-split-editor-product d e₁ e₂
  = record
  { editor
    = dependent-editor-product d
      (DependentSplitEditor.editor e₁)
      (DependentSplitEditor.editor e₂)
  ; split-functor
    = dependent-split-functor-product
      (DependentSplitEditor.split-functor e₁)
      (DependentSplitEditor.split-functor e₂)
  }

-- ### DependentInnerEditor

-- Takes direction from first to second component.
dependent-inner-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ P₁ P₂ : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → Direction
  → DependentInnerEditor V₁ E₁ S₁ P₁ C₁'
  → DependentInnerEditor V₂ E₂ S₂ P₂ C₂'
  → DependentInnerEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (S₁ × S₂)
    (P₁ × P₂)
    (dependent-category-product C₁' C₂')
dependent-inner-editor-product d e₁ e₂
  = record
  { editor
    = dependent-editor-product d
      (DependentInnerEditor.editor e₁)
      (DependentInnerEditor.editor e₂)
  ; state-encoding
    = dependent-state-encoding-product
      (DependentInnerEditor.state-encoding e₁)
      (DependentInnerEditor.state-encoding e₂)
  ; encoding
    = dependent-encoding-product
      (DependentInnerEditor.encoding e₁)
      (DependentInnerEditor.encoding e₂)
  ; split-functor
    = dependent-split-functor-product
      (DependentInnerEditor.split-functor e₁)
      (DependentInnerEditor.split-functor e₂)
  }

-- ## Nondependent

-- ### SplitEditor

-- Takes direction from first to second component.
split-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {C₁ C₂ : Category}
  → Direction
  → SplitEditor V₁ E₁ C₁
  → SplitEditor V₂ E₂ C₂
  → SplitEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (category-product C₁ C₂)
split-editor-product
  = dependent-split-editor-product

-- ### InnerEditor

-- Takes direction from first to second component.
inner-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ P₁ P₂ : Set}
  → {C₁ C₂ : Category}
  → Direction
  → InnerEditor V₁ E₁ S₁ P₁ C₁
  → InnerEditor V₂ E₂ S₂ P₂ C₂
  → InnerEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (S₁ × S₂)
    (P₁ × P₂)
    (category-product C₁ C₂)
inner-editor-product
  = dependent-inner-editor-product

