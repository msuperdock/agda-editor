module Editor.List where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.List
  using (category-list; dependent-category-list)
open import Category.Split.List
  using (dependent-split-functor-list)
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Category.State.List
  using (module StateCategoryList; dependent-state-category-list;
    state-category-list)
open import Data.Any
  using (any)
open import Data.Direction
  using (Direction; _≟_dir)
open import Data.Empty
  using (⊥-elim)
open import Data.Equal
  using (_≡_; refl; rewrite')
open import Data.Fin
  using (Fin; suc; zero)
open import Data.Inspect
  using ([_]; inspect)
open import Data.List
  using (List; []; _∷_; _!_)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Relation
  using (no; yes)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Data.Unit
  using (tt)
open import Editor
  using (DependentEditor; DependentInnerEditor; DependentSplitEditor; Editor;
    InnerEditor; SplitEditor)
open import Encoding.List
  using (dependent-encoding-list)
open import Encoding.State.List
  using (dependent-state-encoding-list)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)
open import Stack.List
  using (ListEvent; ListEvent₀; event-stack-list; view-stack-list;
    view-stack-map-list)

-- ## Base

-- ### Editor

module _
  {V : ViewStack}
  {E : EventStack}
  {C : StateCategory}
  where

  -- #### Module

  module EditorList
    (d : Direction)
    (e : Editor V E C)
    where

    -- ##### Types
  
    open EventStack (event-stack-list E)

    open StateCategory (state-category-list C)
      using () renaming
      ( Object
        to State
      ; Arrow
        to StateArrow
      ; identity'
        to state-identity
      )

    -- ##### State

    StateStack
      : ViewStack
    StateStack
      = view-stack-list
        (Editor.StateStack e)

    open ViewStack StateStack
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
      = []

    initial-path
      : (s : State)
      → StatePath s
    initial-path []
      = tt
    initial-path (s ∷ _)
      = (zero , Editor.initial-path e s)

    initial-path-with
      : (s : State)
      → Direction
      → StatePath s
    initial-path-with [] _
      = tt
    initial-path-with ss@(s ∷ ss') d'
      with d' ≟ d dir
    ... | no _
      = zero
      , Editor.initial-path-with e s d'
    ... | yes _
      = Fin.maximum (List.length ss')
      , Editor.initial-path-with e (ss ! Fin.maximum (List.length ss')) d'

    -- ##### Draw

    draw-stack
      : ViewStackMap StateStack (view-stack-list V)
    draw-stack
      = view-stack-map-list
        (Editor.draw-stack e)

    -- ##### Mode

    mode
      : (s : State)
      → StatePath s
      → Mode
    mode (any {zero} _) _
      = nothing
    mode ss@(any {suc _} _) (k , sp)
      = just (Editor.mode e (ss ! k) sp)

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner
    mode-inner ss@(_ ∷ _) (k , sp)
      = Editor.mode-inner e (ss ! k) sp

    -- ##### Handle

    handle-insert
      : (s : State)
      → Fin (suc (List.length s))
      → s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
    handle-insert ss k
      = List.insert ss k (Editor.initial e)
      , (k , rewrite'
        (Editor.StatePath e)
        (List.lookup-insert ss k (Editor.initial e))
        (Editor.initial-path' e))
      , StateCategoryList.insert C ss k (Editor.initial e)

    handle-update
      : (s : State)
      → (k : Fin (List.length s))
      → (s' : StateCategory.Object C)
      → (sp' : Editor.StatePath e s')
      → StateCategory.Arrow C (s ! k) s'
      → s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
    handle-update ss@(_ ∷ _) k s' sp' f
      = List.update ss k s'
      , (k , rewrite'
        (Editor.StatePath e)
        (List.lookup-update ss k s') sp')
      , StateCategoryList.update C ss k f

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)

    handle ss@[] _ ListEvent₀.insert
      = ι₁ (handle-insert ss zero)
    handle ss@(_ ∷ _) (k , _) (ι₂ ListEvent.insert-before)
      = ι₁ (handle-insert ss (Fin.lift k))
    handle ss@(_ ∷ _) (k , _) (ι₂ ListEvent.insert-after)
      = ι₁ (handle-insert ss (suc k))

    handle ss@(_ ∷ _) (k , sp) (ι₁ e')
      with Editor.handle e (ss ! k) sp e'
    ... | ι₁ (s' , sp' , f)
      = ι₁ (handle-update ss k s' sp' f)
    ... | ι₂ s'
      = ι₂ s'

    handle ss@(_ ∷ []) _ (ι₂ ListEvent.delete)
      = ι₁ ([]
        , tt
        , StateCategoryList.delete C ss zero)
    handle ss@(_ ∷ ss'@(s ∷ _)) (zero , _) (ι₂ ListEvent.delete)
      = ι₁ (ss'
        , (zero , Editor.initial-path e s)
        , StateCategoryList.delete C ss zero)
    handle ss@(_ ∷ _ ∷ _) (suc k , _) (ι₂ ListEvent.delete)
      = ι₁ (List.delete ss (suc k)
        , (k , Editor.initial-path e (List.delete ss (suc k) ! k))
        , StateCategoryList.delete C ss (suc k))

    handle ss@(_ ∷ _) sp@(zero , _) (ι₂ ListEvent.move-previous)
      = ι₁ (ss , sp , state-identity ss)
    handle (s ∷ ss) (suc k , sp) (ι₂ ListEvent.move-previous)
      = ι₁ (List.swap s ss k
        , (Fin.lift k , rewrite'
          (Editor.StatePath e)
          (List.lookup-swap₁ s ss k) sp)
        , StateCategoryList.swap C s ss k)

    handle (_ ∷ _) (k , _) (ι₂ ListEvent.move-next)
      with Fin.drop k
      | inspect Fin.drop k
    handle ss sp _ | nothing | _
      = ι₁ (ss , sp , state-identity ss)
    handle (s ∷ ss) (k , sp) _ | just k' | [ p ]
      = ι₁ (List.swap s ss k'
        , (suc k' , rewrite'
          (Editor.StatePath e)
          (List.lookup-swap₂' s ss k p) sp)
        , StateCategoryList.swap C s ss k')

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-escape [] _
      = nothing
    handle-escape ss@(_ ∷ _) (k , sp)
      with Editor.handle-escape e (ss ! k) sp
    ... | nothing
      = nothing
    ... | just (ι₁ (s' , sp' , f))
      = just (ι₁ (handle-update ss k s' sp' f))
    ... | just (ι₂ s')
      = just (ι₂ s')

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-return [] _
      = nothing
    handle-return ss@(_ ∷ _) (k , sp)
      with Editor.handle-return e (ss ! k) sp
    ... | nothing
      = nothing
    ... | just (ι₁ (s' , sp' , f))
      = just (ι₁ (handle-update ss k s' sp' f))
    ... | just (ι₂ s')
      = just (ι₂ s')

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → Maybe (StatePath s)
    handle-direction [] _ _
      = nothing
    handle-direction ss@(_ ∷ _) (k , sp) d'
      with Editor.handle-direction e (ss ! k) sp d'
      | d' ≟ d dir
      | Direction.reverse d' ≟ d dir
      | Fin.increment k
      | Fin.decrement k
    ... | nothing | yes _ | _ | just k' | _
      = just (k' , Editor.initial-path-with e (ss ! k') (Direction.reverse d'))
    ... | nothing | _ | yes _ | _ | just k'
      = just (k' , Editor.initial-path-with e (ss ! k') d')
    ... | nothing | _ | _ | _ | _
      = nothing
    ... | just sp' | _ | _ | _ | _
      = just (k , sp')

    handle-direction-valid
      : (s : State)
      → (d' : Direction)
      → handle-direction s (initial-path-with s d') d' ≡ nothing
    handle-direction-valid [] _
      = refl
    handle-direction-valid (_ ∷ _) d'
      with d' ≟ d dir
    handle-direction-valid (s ∷ _) d' | no _
      with Editor.handle-direction e s
        (Editor.initial-path-with e s d') d'
      | Editor.handle-direction-valid e s d'
      | Direction.reverse d' ≟ d dir
    ... | _ | refl | no _
      = refl
    ... | _ | refl | yes _
      = refl
    handle-direction-valid ss@(_ ∷ ss') d' | yes refl
      with Editor.handle-direction e (ss ! Fin.maximum (List.length ss'))
        (Editor.initial-path-with e (ss ! Fin.maximum (List.length ss')) d') d'
      | Editor.handle-direction-valid e (ss ! Fin.maximum (List.length ss')) d'
      | Fin.increment (Fin.maximum (List.length ss'))
      | Fin.increment-maximum (List.length ss')
      | Direction.reverse d' ≟ d dir
    ... | _ | refl | _ | refl | no _
      = refl
    ... | _ | _ | _ | _ | yes p
      = ⊥-elim (Direction.reverse-≢ d' p)

    handle-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → EventInner (mode-inner s sp s' sp')
      → Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner ss@(_ ∷ _) (k , sp)
      = Editor.handle-inner e (ss ! k) sp

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))
    handle-inner-escape ss@(_ ∷ _) (k , sp)
      = Editor.handle-inner-escape e (ss ! k) sp

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return ss@(_ ∷ _) (k , sp) s' sp'
      with Editor.handle-inner-return e (ss ! k) sp s' sp'
    ... | ι₁ (s'' , sp'' , f)
      = ι₁ (handle-update ss k s'' sp'' f)
    ... | ι₂ s''
      = ι₂ s''

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'
    handle-inner-direction ss@(_ ∷ _) (k , sp)
      = Editor.handle-inner-direction e (ss ! k) sp

  -- #### Function

  -- Takes direction from earlier to later elements.
  editor-list
    : Direction
    → Editor V E C
    → Editor
      (view-stack-list V)
      (event-stack-list E)
      (state-category-list C)
  editor-list d e
    = record {EditorList d e}

-- ## Dependent

-- ### DependentEditor

-- Takes direction from earlier to later elements.
dependent-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → Direction
  → DependentEditor V E C'
  → DependentEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-state-category-list C')
dependent-editor-list {n = zero} d e
  = editor-list d e
dependent-editor-list {n = suc _} d e
  = record
  { tail
    = λ x → dependent-editor-list d
      (DependentEditor.tail e x)
  }

-- ### DependentSplitEditor

-- Takes direction from earlier to later elements.
dependent-split-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → Direction
  → DependentSplitEditor V E C'
  → DependentSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-category-list C')
dependent-split-editor-list d e
  = record
  { editor
    = dependent-editor-list d
      (DependentSplitEditor.editor e)
  ; split-functor
    = dependent-split-functor-list
      (DependentSplitEditor.split-functor e)
  }

-- ### DependentInnerEditor

-- Takes direction from earlier to later elements.
dependent-inner-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → Direction
  → DependentInnerEditor V E S P C'
  → DependentInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (dependent-category-list C')
dependent-inner-editor-list d e
  = record
  { editor
    = dependent-editor-list d
      (DependentInnerEditor.editor e)
  ; state-encoding
    = dependent-state-encoding-list
      (DependentInnerEditor.state-encoding e)
  ; encoding
    = dependent-encoding-list
      (DependentInnerEditor.encoding e)
  ; split-functor
    = dependent-split-functor-list
      (DependentInnerEditor.split-functor e)
  }

-- ## Nondependent

-- ### SplitEditor

-- Takes direction from earlier to later elements.
split-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {C : Category}
  → Direction
  → SplitEditor V E C
  → SplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (category-list C)
split-editor-list
  = dependent-split-editor-list

-- ### InnerEditor

-- Takes direction from earlier to later elements.
inner-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C : Category}
  → Direction
  → InnerEditor V E S P C
  → InnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (category-list C)
inner-editor-list
  = dependent-inner-editor-list

