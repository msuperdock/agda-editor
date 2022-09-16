module Editor.Sigma where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.Core.Sigma.Sum
  using (module ArrowSigmaSum)
open import Category.Sigma
  using (dependent-category-sigma)
open import Category.Snoc
  using (chain-category-snoc)
open import Category.Split.Sigma
  using (dependent-split-functor-sigma)
open import Category.State
  using (DependentStateCategory; DependentStateCategory₁; StateCategory)
open import Category.State.Sigma.Sum
  using (dependent-state-category-sigma-sum; state-category-sigma-sum)
open import Data.Direction
  using (Direction; _≟_dir)
open import Data.Empty
  using (⊥-elim)
open import Data.Equal
  using (_≡_; refl)
open import Data.Function
  using (id)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (Maybe; just; maybe; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Relation
  using (no; yes)
open import Data.Sigma
  using (Σ; _×_; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Editor
  using (DependentEditor; DependentEditor₁; DependentInnerEditor;
    DependentSplitEditor; Editor; SplitEditor)
open import Encoding.Sigma
  using (dependent-encoding-sigma)
open import Encoding.State.Sigma.Sum
  using (dependent-state-encoding-sigma-sum)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)
open import Stack.Sigma
  using (event-stack-sigma; view-stack-sigma)

-- ## Base

-- ### Editor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {C₁ : Category}
  {C₂ : DependentStateCategory₁ C₁}
  where

  -- #### Module

  module EditorSigma
    (d : Direction)
    (e₁ : SplitEditor V₁ E₁ C₁)
    (e₂ : DependentEditor₁ V₂ E₂ C₁ C₂)
    where

    -- ##### Types

    open ViewStack (view-stack-sigma V₁ V₂)
    open EventStack (event-stack-sigma E₁ E₂)

    state-category
      : StateCategory
    state-category
      = state-category-sigma-sum C₂
        (SplitEditor.split-functor e₁)

    open StateCategory state-category
      using () renaming
      ( Object
        to State
      ; Arrow
        to StateArrow
      )

    -- ##### State

    StatePath
      : State
      → Set
    StatePath (ι₁ s₁)
      = SplitEditor.StatePath e₁ s₁
    StatePath (ι₂ (x₁ , s₂))
      = SplitEditor.StatePath e₁ (SplitEditor.unbase e₁ x₁)
      ⊔ DependentEditor₁.StatePath C₁ e₂ s₂

    StateInner
      : (s : State)
      → StatePath s
      → Set
    StateInner (ι₁ s₁) sp₁
      = SplitEditor.StateInner e₁ s₁ sp₁
    StateInner (ι₂ (x₁ , _)) (ι₁ _)
      = s₁ ∈ SplitEditor.State e₁
      × f₁ ∈ SplitEditor.StateArrow e₁ (SplitEditor.unbase e₁ x₁) s₁
      × Maybe (Σ (SplitEditor.StatePath e₁ s₁) (SplitEditor.StateInner e₁ s₁))
    StateInner (ι₂ (_ , s₂)) (ι₂ sp₂)
      = DependentEditor₁.StateInner C₁ e₂ s₂ sp₂

    StateInnerPath
      : (s : State)
      → (sp : StatePath s)
      → StateInner s sp
      → Set
    StateInnerPath (ι₁ s₁) sp₁ s₁'
      = SplitEditor.StateInnerPath e₁ s₁ sp₁ s₁'
    StateInnerPath (ι₂ _) (ι₁ _) (s₁ , _ , nothing)
      = SplitEditor.StatePath e₁ s₁
    StateInnerPath (ι₂ _) (ι₁ _) (s₁ , _ , just (sp₁ , s₁'))
      = SplitEditor.StateInnerPath e₁ s₁ sp₁ s₁'
    StateInnerPath (ι₂ (_ , s₂)) (ι₂ sp₂) s₂'
      = DependentEditor₁.StateInnerPath C₁ e₂ s₂ sp₂ s₂'

    StateStack
      : ViewStack
    StateStack
      = record
      { View
        = State
      ; ViewPath
        = StatePath
      ; ViewInner
        = StateInner
      ; ViewInnerPath
        = StateInnerPath
      }

    initial
      : State
    initial
      = ι₁ (SplitEditor.initial e₁)

    initial-path
      : (s : State)
      → StatePath s
    initial-path (ι₁ s₁)
      = SplitEditor.initial-path e₁ s₁
    initial-path (ι₂ (x₁ , _))
      = ι₁ (SplitEditor.initial-path e₁ (SplitEditor.unbase e₁ x₁))

    initial-path-with
      : (s : State)
      → Direction
      → StatePath s
    initial-path-with (ι₁ s₁) d'
      = SplitEditor.initial-path-with e₁ s₁ d'
    initial-path-with (ι₂ (x₁ , s₂)) d'
      with d' ≟ d dir
    ... | no _
      = ι₁ (SplitEditor.initial-path-with e₁ (SplitEditor.unbase e₁ x₁) d')
    ... | yes _
      = ι₂ (DependentEditor₁.initial-path-with C₁ e₂ s₂ d')

    -- ##### Draw

    draw
      : State
      → View
    draw (ι₁ s₁)
      = (SplitEditor.draw e₁ s₁ , nothing)
    draw (ι₂ (x₁ , s₂))
      = (SplitEditor.draw e₁ (SplitEditor.unbase e₁ x₁)
        , just (DependentEditor₁.draw C₁ e₂ s₂))
  
    draw-with
      : (s : State)
      → StatePath s
      → View
    draw-with (ι₁ s₁) sp₁
      = (SplitEditor.draw-with e₁ s₁ sp₁ , nothing)
    draw-with (ι₂ (x₁ , s₂)) (ι₁ sp₁)
      = (SplitEditor.draw-with e₁ (SplitEditor.unbase e₁ x₁) sp₁
        , just (DependentEditor₁.draw C₁ e₂ s₂))
    draw-with (ι₂ (x₁ , s₂)) (ι₂ sp₂)
      = (SplitEditor.draw e₁ (SplitEditor.unbase e₁ x₁)
        , just (DependentEditor₁.draw-with C₁ e₂ s₂ sp₂))

    draw-path
      : (s : State)
      → (sp : StatePath s)
      → ViewPath (draw-with s sp)
    draw-path (ι₁ s₁) sp₁
      = SplitEditor.draw-path e₁ s₁ sp₁
    draw-path (ι₂ (x₁ , _)) (ι₁ sp₁)
      = ι₁ (SplitEditor.draw-path e₁ (SplitEditor.unbase e₁ x₁) sp₁)
    draw-path (ι₂ (_ , s₂)) (ι₂ sp₂)
      = ι₂ (DependentEditor₁.draw-path C₁ e₂ s₂ sp₂)

    draw-inner-with
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ViewInner (draw-with s sp) (draw-path s sp)
    draw-inner-with (ι₁ s₁) sp₁ s₁' sp₁'
      = SplitEditor.draw-inner-with e₁ s₁ sp₁ s₁' sp₁'
    draw-inner-with (ι₂ _) (ι₁ _) (s₁ , _ , nothing) sp₁
      = (SplitEditor.draw-with e₁ s₁ sp₁ , nothing)
    draw-inner-with (ι₂ _) (ι₁ _) (s₁' , _ , just (sp₁' , s₁'')) sp₁''
      = (SplitEditor.draw-with e₁ s₁' sp₁'
        , just (SplitEditor.draw-path e₁ s₁' sp₁'
          , SplitEditor.draw-inner-with e₁ s₁' sp₁' s₁'' sp₁''))
    draw-inner-with (ι₂ (_ , s₂)) (ι₂ sp₂) s₂' sp₂'
      = DependentEditor₁.draw-inner-with C₁ e₂ s₂ sp₂ s₂' sp₂'

    draw-inner-path
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → ViewInnerPath
        (draw-with s sp)
        (draw-path s sp)
        (draw-inner-with s sp s' sp')
    draw-inner-path (ι₁ s₁) sp₁ s₁'
      = SplitEditor.draw-inner-path e₁ s₁ sp₁ s₁'
    draw-inner-path (ι₂ _) (ι₁ _) (s₁ , _ , nothing)
      = SplitEditor.draw-path e₁ s₁
    draw-inner-path (ι₂ _) (ι₁ _) (s₁ , _ , just (sp₁ , s₁'))
      = SplitEditor.draw-inner-path e₁ s₁ sp₁ s₁'
    draw-inner-path (ι₂ (_ , s₂)) (ι₂ sp₂) s₂'
      = DependentEditor₁.draw-inner-path C₁ e₂ s₂ sp₂ s₂'

    draw-stack
      : ViewStackMap
        StateStack
        (view-stack-sigma V₁ V₂)
    draw-stack
      = record
      { view
        = draw
      ; view-with
        = draw-with
      ; view-path
        = draw-path
      ; view-inner-with
        = draw-inner-with
      ; view-inner-path
        = draw-inner-path
      }

    -- ##### Mode

    mode
      : (s : State)
      → StatePath s
      → Mode
    mode (ι₁ s₁) sp₁
      = ι₁ (SplitEditor.mode e₁ s₁ sp₁)
    mode (ι₂ (x₁ , _)) (ι₁ sp₁)
      = ι₁ (SplitEditor.mode e₁ (SplitEditor.unbase e₁ x₁) sp₁)
    mode (ι₂ (_ , s₂)) (ι₂ sp₂)
      = ι₂ (DependentEditor₁.mode C₁ e₂ s₂ sp₂)

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner
    mode-inner (ι₁ s₁) sp₁ s₁' sp₁'
      = ι₂ (ι₁ (SplitEditor.mode-inner e₁ s₁ sp₁ s₁' sp₁'))
    mode-inner (ι₂ _) (ι₁ _) (s₁ , _ , nothing) sp₁
      = ι₁ (SplitEditor.mode e₁ s₁ sp₁)
    mode-inner (ι₂ _) (ι₁ _) (s₁ , _ , just (sp₁ , s₁')) sp₁'
      = ι₂ (ι₁ (SplitEditor.mode-inner e₁ s₁ sp₁ s₁' sp₁'))
    mode-inner (ι₂ (_ , s₂)) (ι₂ sp₂) s₂' sp₂'
      = ι₂ (ι₂ (DependentEditor₁.mode-inner C₁ e₂ s₂ sp₂ s₂' sp₂'))

    -- ##### Handle

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle (ι₁ s₁) sp₁ e₁'
      with SplitEditor.handle e₁ s₁ sp₁ e₁'
    ... | ι₁ (s₁' , sp₁' , f₁)
      = ι₁ (ι₁ s₁' , sp₁' , ArrowSigmaSum.arrow₁ f₁)
    ... | ι₂ s₁'
      = ι₂ s₁'
    handle (ι₂ (x₁ , _)) (ι₁ sp₁) e₁'
      with SplitEditor.handle e₁ (SplitEditor.unbase e₁ x₁) sp₁ e₁'
    ... | ι₁ (s₁' , sp₁' , f₁)
      = ι₂ ((s₁' , f₁ , nothing) , sp₁')
    ... | ι₂ (s₁' , sp₁')
      = ι₂ ((SplitEditor.unbase e₁ x₁
        , SplitEditor.state-identity e₁ (SplitEditor.unbase e₁ x₁)
        , just (sp₁ , s₁'))
        , sp₁')
    handle (ι₂ (x₁ , s₂)) (ι₂ sp₂) e₂'
      with DependentEditor₁.handle C₁ e₂ s₂ sp₂ e₂'
    ... | ι₁ (s₂' , sp₂' , f₂)
      = ι₁ (ι₂ (x₁ , s₂')
        , ι₂ sp₂'
        , ArrowSigmaSum.arrow₂
          (SplitEditor.state-identity e₁ (SplitEditor.unbase e₁ x₁)) f₂)
    ... | ι₂ s₂'
      = ι₂ s₂'

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-escape (ι₁ s₁) sp₁
      with SplitEditor.handle-escape e₁ s₁ sp₁
    ... | nothing
      = nothing
    ... | just (ι₁ (s₁' , sp₁' , f₁))
      = just (ι₁ (ι₁ s₁' , sp₁' , ArrowSigmaSum.arrow₁ f₁))
    ... | just (ι₂ s₁')
      = just (ι₂ s₁')
    handle-escape (ι₂ (x₁ , _)) (ι₁ sp₁)
      with SplitEditor.handle-escape e₁ (SplitEditor.unbase e₁ x₁) sp₁
    ... | nothing
      = just (ι₁ (ι₁ (SplitEditor.unbase e₁ x₁)
        , sp₁
        , ArrowSigmaSum.arrow₁
          (SplitEditor.state-identity e₁ (SplitEditor.unbase e₁ x₁))))
    ... | just (ι₁ (s₁' , sp₁' , f₁))
      = just (ι₁ (ι₁ s₁' , sp₁' , ArrowSigmaSum.arrow₁ f₁))
    ... | just (ι₂ (s₁' , sp₁'))
      = just (ι₂ ((SplitEditor.unbase e₁ x₁
        , SplitEditor.state-identity e₁ (SplitEditor.unbase e₁ x₁)
        , just (sp₁ , s₁'))
        , sp₁'))
    handle-escape (ι₂ (x₁ , s₂)) (ι₂ sp₂)
      with DependentEditor₁.handle-escape C₁ e₂ s₂ sp₂
    ... | nothing
      = just (ι₁ (ι₁ (SplitEditor.unbase e₁ x₁)
        , SplitEditor.initial-path e₁ (SplitEditor.unbase e₁ x₁)
        , ArrowSigmaSum.arrow₁
          (SplitEditor.state-identity e₁ (SplitEditor.unbase e₁ x₁))))
    ... | just (ι₁ (s₂' , sp₂' , f₂))
      = just (ι₁ (ι₂ (x₁ , s₂')
        , ι₂ sp₂'
        , ArrowSigmaSum.arrow₂
          (SplitEditor.state-identity e₁ (SplitEditor.unbase e₁ x₁)) f₂))
    ... | just (ι₂ s₂')
      = just (ι₂ s₂')

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-return (ι₁ s₁) sp₁
      with SplitEditor.handle-return e₁ s₁ sp₁
      | SplitEditor.base' e₁ s₁
      | inspect (SplitEditor.base' e₁) s₁
    ... | nothing | nothing | _
      = nothing
    ... | nothing | just x₁ | [ p₁ ]
      = just (ι₁ (ι₂ (x₁ , DependentEditor₁.initial C₁ e₂)
        , ι₂ (DependentEditor₁.initial-path' C₁ e₂)
        , ArrowSigmaSum.arrow₁ (SplitEditor.normalize-arrow e₁ s₁ p₁)))
    ... | just (ι₁ (s₁' , sp₁' , f₁)) | _ | _
      = just (ι₁ (ι₁ s₁' , sp₁' , ArrowSigmaSum.arrow₁ f₁))
    ... | just (ι₂ s₁') | _ | _
      = just (ι₂ s₁')
    handle-return (ι₂ (x₁ , _)) (ι₁ sp₁)
      with SplitEditor.handle-return e₁ (SplitEditor.unbase e₁ x₁) sp₁
    ... | nothing
      = nothing
    ... | just (ι₁ (s₁' , sp₁' , f₁))
      = just (ι₂ ((s₁' , f₁ , nothing) , sp₁'))
    ... | just (ι₂ (s₁' , sp₁'))
      = just (ι₂ ((SplitEditor.unbase e₁ x₁
        , SplitEditor.state-identity e₁ (SplitEditor.unbase e₁ x₁)
        , just (sp₁ , s₁'))
        , sp₁'))
    handle-return (ι₂ (x₁ , s₂)) (ι₂ sp₂)
      with DependentEditor₁.handle-return C₁ e₂ s₂ sp₂
    ... | nothing
      = nothing
    ... | just (ι₁ (s₂' , sp₂' , f₂))
      = just (ι₁ (ι₂ (x₁ , s₂')
        , ι₂ sp₂'
        , ArrowSigmaSum.arrow₂
          (SplitEditor.state-identity e₁ (SplitEditor.unbase e₁ x₁)) f₂))
    ... | just (ι₂ s₂')
      = just (ι₂ s₂')

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → Maybe (StatePath s)
    handle-direction (ι₁ s₁) sp₁ d'
      = SplitEditor.handle-direction e₁ s₁ sp₁ d'
    handle-direction (ι₂ (x₁ , s₂)) (ι₁ sp₁) d'
      with SplitEditor.handle-direction e₁ (SplitEditor.unbase e₁ x₁) sp₁ d'
      | d' ≟ d dir
    ... | nothing | no _
      = nothing
    ... | nothing | yes _
      = just (ι₂ (DependentEditor₁.initial-path-with C₁ e₂ s₂
        (Direction.reverse d')))
    ... | just sp₁' | _
      = just (ι₁ sp₁')
    handle-direction (ι₂ (x₁ , s₂)) (ι₂ sp₂) d'
      with DependentEditor₁.handle-direction C₁ e₂ s₂ sp₂ d'
      | Direction.reverse d' ≟ d dir
    ... | nothing | no _
      = nothing
    ... | nothing | yes _
      = just (ι₁ (SplitEditor.initial-path-with e₁ (SplitEditor.unbase e₁ x₁)
        (Direction.reverse d')))
    ... | just sp₂' | _
      = just (ι₂ sp₂')

    handle-direction-valid
      : (s : State)
      → (d : Direction)
      → handle-direction s (initial-path-with s d) d ≡ nothing
    handle-direction-valid (ι₁ s₁) d'
      = SplitEditor.handle-direction-valid e₁ s₁ d'
    handle-direction-valid (ι₂ _) d'
      with d' ≟ d dir
      | inspect (_≟_dir d') d
    handle-direction-valid (ι₂ (x₁ , _)) d' | no _ | [ _ ]
      with SplitEditor.handle-direction e₁ (SplitEditor.unbase e₁ x₁)
        (SplitEditor.initial-path-with e₁ (SplitEditor.unbase e₁ x₁) d') d'
      | SplitEditor.handle-direction-valid e₁ (SplitEditor.unbase e₁ x₁) d'
      | d' ≟ d dir
    handle-direction-valid _ _ _ | _ | [ refl ] | _ | refl | _
      = refl
    handle-direction-valid (ι₂ (_ , s₂)) d' | yes refl | _
      with DependentEditor₁.handle-direction C₁ e₂ s₂
        (DependentEditor₁.initial-path-with C₁ e₂ s₂ d') d'
      | DependentEditor₁.handle-direction-valid C₁ e₂ s₂ d'
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
    handle-inner (ι₁ s₁) sp₁ s₁' sp₁' e₁'
      = SplitEditor.handle-inner e₁ s₁ sp₁ s₁' sp₁' e₁'
    handle-inner (ι₂ _) (ι₁ _) (s₁ , f₁ , nothing) sp₁ e₁'
      with SplitEditor.handle e₁ s₁ sp₁ e₁'
    ... | ι₁ (s₁' , sp₁' , f₁')
      = ((s₁' , SplitEditor.state-compose e₁ f₁' f₁ , nothing) , sp₁')
    ... | ι₂ (s₁' , sp₁')
      = ((s₁ , f₁ , just (sp₁ , s₁')) , sp₁')
    handle-inner (ι₂ _) (ι₁ _) (s₁ , f₁ , just (sp₁ , s₁')) sp₁' e₁'
      with SplitEditor.handle-inner e₁ s₁ sp₁ s₁' sp₁' e₁'
    ... | (s₁'' , sp₁'')
      = ((s₁ , f₁ , just (sp₁ , s₁'')) , sp₁'')
    handle-inner (ι₂ (_ , s₂)) (ι₂ sp₂) s₂' sp₂' e₂'
      = DependentEditor₁.handle-inner C₁ e₂ s₂ sp₂ s₂' sp₂' e₂'

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))
    handle-inner-escape (ι₁ s₁) sp₁ s₁' sp₁'
      = SplitEditor.handle-inner-escape e₁ s₁ sp₁ s₁' sp₁'
    handle-inner-escape (ι₂ _) (ι₁ _) (s₁ , f₁ , nothing) sp₁
      with SplitEditor.handle-escape e₁ s₁ sp₁
    ... | nothing
      = nothing
    ... | just (ι₁ (s₁' , sp₁' , f₁'))
      = just ((s₁' , SplitEditor.state-compose e₁ f₁' f₁ , nothing) , sp₁')
    ... | just (ι₂ (s₁' , sp₁'))
      = just ((s₁ , f₁ , just (sp₁ , s₁')) , sp₁')
    handle-inner-escape (ι₂ _) (ι₁ _) (s₁ , f₁ , just (sp₁ , s₁')) sp₁'
      with SplitEditor.handle-inner-escape e₁ s₁ sp₁ s₁' sp₁'
    ... | nothing
      = just ((s₁ , f₁ , nothing) , sp₁)
    ... | just (s₁'' , sp₁'')
      = just ((s₁ , f₁ , just (sp₁ , s₁'')) , sp₁'')
    handle-inner-escape (ι₂ (_ , s₂)) (ι₂ sp₂) s₂' sp₂'
      = DependentEditor₁.handle-inner-escape C₁ e₂ s₂ sp₂ s₂' sp₂'

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return (ι₁ s₁) sp₁ s₁' sp₁'
      with SplitEditor.handle-inner-return e₁ s₁ sp₁ s₁' sp₁'
    ... | ι₁ (s₁'' , sp₁'' , f₁)
      = ι₁ (ι₁ s₁'' , sp₁'' , ArrowSigmaSum.arrow₁ f₁)
    ... | ι₂ s₁''
      = ι₂ s₁''
    handle-inner-return (ι₂ (x₁ , s₂)) (ι₁ _) (s₁ , f₁ , nothing) sp₁
      with SplitEditor.handle-return e₁ s₁ sp₁
      | SplitEditor.base' e₁ s₁
      | inspect (SplitEditor.base' e₁) s₁
    ... | nothing | nothing | _
      = ι₁ (ι₁ s₁ , sp₁ , ArrowSigmaSum.arrow₁ f₁)
    ... | nothing | just x₁' | [ p₁ ]
      = ι₁ (ι₂ (x₁' , s₂')
        , ι₂ (DependentEditor₁.initial-path-with C₁ e₂ s₂'
          (Direction.reverse d))
        , ArrowSigmaSum.arrow₂
          (SplitEditor.state-compose e₁
            (SplitEditor.normalize-arrow e₁ s₁ p₁) f₁) f₂)
      where
        f₁' = SplitEditor.map' e₁ (SplitEditor.base-unbase e₁ x₁) p₁ f₁
        s₂' = DependentStateCategory₁.base C₁ C₂ f₁' s₂
        f₂ = DependentStateCategory₁.map C₁ C₂ f₁' s₂

    ... | just (ι₁ (s₁' , sp₁' , f₁')) | _ | _
      = ι₂ ((s₁' , SplitEditor.state-compose e₁ f₁' f₁ , nothing) , sp₁')
    ... | just (ι₂ (s₁' , sp₁')) | _ | _
      = ι₂ ((s₁ , f₁ , just (sp₁ , s₁')) , sp₁')
    handle-inner-return (ι₂ _) (ι₁ _) (s₁ , f₁ , just (sp₁ , s₁')) sp₁'
      with SplitEditor.handle-inner-return e₁ s₁ sp₁ s₁' sp₁'
    ... | ι₁ (s₁'' , sp₁'' , f₁')
      = ι₂ ((s₁'' , SplitEditor.state-compose e₁ f₁' f₁ , nothing) , sp₁'')
    ... | ι₂ (s₁'' , sp₁'')
      = ι₂ ((s₁ , f₁ , just (sp₁ , s₁'')) , sp₁'')
    handle-inner-return (ι₂ (x₁ , s₂)) (ι₂ sp₂) s₂' sp₂'
      with DependentEditor₁.handle-inner-return C₁ e₂ s₂ sp₂ s₂' sp₂'
    ... | ι₁ (s₂'' , sp₂'' , f₂)
      = ι₁ (ι₂ (x₁ , s₂'')
        , ι₂ sp₂''
        , ArrowSigmaSum.arrow₂
          (SplitEditor.state-identity e₁ (SplitEditor.unbase e₁ x₁)) f₂)
    ... | ι₂ s₂''
      = ι₂ s₂''

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'
    handle-inner-direction (ι₁ s₁) sp₁ s₁' sp₁' d'
      = SplitEditor.handle-inner-direction e₁ s₁ sp₁ s₁' sp₁' d'
    handle-inner-direction (ι₂ _) (ι₁ _) (s₁ , _ , nothing) sp₁ d'
      = maybe (SplitEditor.handle-direction e₁ s₁ sp₁ d') sp₁ id
    handle-inner-direction (ι₂ _) (ι₁ _) (s₁ , _ , just (sp₁ , s₁')) sp₁' d'
      = SplitEditor.handle-inner-direction e₁ s₁ sp₁ s₁' sp₁' d'
    handle-inner-direction (ι₂ (_ , s₂)) (ι₂ sp₂) s₂' sp₂' d'
      = DependentEditor₁.handle-inner-direction C₁ e₂ s₂ sp₂ s₂' sp₂' d'

  -- #### Function

  -- Takes direction from first to second component.
  editor-sigma
    : Direction
    → (e₁ : SplitEditor V₁ E₁ C₁)
    → DependentEditor V₂ E₂ C₂
    → Editor
      (view-stack-sigma V₁ V₂)
      (event-stack-sigma E₁ E₂)
      (state-category-sigma-sum C₂
        (SplitEditor.split-functor e₁))
  editor-sigma d e₁ e₂
    = record {EditorSigma d e₁ e₂}

-- ## Dependent

-- ### DependentEditor

-- Takes direction from first to second component.
dependent-editor-sigma
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentStateCategory (chain-category-snoc C₁')}
  → Direction
  → (e₁ : DependentSplitEditor V₁ E₁ C₁')
  → DependentEditor V₂ E₂ C₂'
  → DependentEditor
    (view-stack-sigma V₁ V₂)
    (event-stack-sigma E₁ E₂)
    (dependent-state-category-sigma-sum C₂'
      (DependentSplitEditor.split-functor e₁))
dependent-editor-sigma {n = zero} d e₁ e₂
  = editor-sigma d e₁ e₂
dependent-editor-sigma {n = suc _} d e₁ e₂
  = record
  { tail
    = λ x → dependent-editor-sigma d
      (DependentSplitEditor.tail e₁ x)
      (DependentEditor.tail e₂ x)
  }

-- ### DependentSplitEditor

-- Takes direction from first to second component.
dependent-split-editor-sigma
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentCategory (chain-category-snoc C₁')}
  → Direction
  → DependentSplitEditor V₁ E₁ C₁'
  → DependentSplitEditor V₂ E₂ C₂'
  → DependentSplitEditor
    (view-stack-sigma V₁ V₂)
    (event-stack-sigma E₁ E₂)
    (dependent-category-sigma C₁' C₂')
dependent-split-editor-sigma d e₁ e₂
  = record
  { editor
    = dependent-editor-sigma d e₁
      (DependentSplitEditor.editor e₂)
  ; split-functor
    = dependent-split-functor-sigma
      (DependentSplitEditor.split-functor e₁)
      (DependentSplitEditor.split-functor e₂)
  }

-- ### DependentInnerEditor

-- Takes direction from first to second component.
dependent-inner-editor-sigma
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ P₁ P₂ : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentCategory (chain-category-snoc C₁')}
  → Direction
  → DependentInnerEditor V₁ E₁ S₁ P₁ C₁'
  → DependentInnerEditor V₂ E₂ S₂ P₂ C₂'
  → DependentInnerEditor
    (view-stack-sigma V₁ V₂)
    (event-stack-sigma E₁ E₂)
    (S₁ ⊔ P₁ × S₂)
    (P₁ × P₂)
    (dependent-category-sigma C₁' C₂')
dependent-inner-editor-sigma d e₁ e₂
  = record
  { editor
    = dependent-editor-sigma d
      (DependentInnerEditor.split-editor e₁)
      (DependentInnerEditor.editor e₂)
  ; state-encoding
    = dependent-state-encoding-sigma-sum
      (DependentInnerEditor.split-functor e₁)
      (DependentInnerEditor.state-encoding e₁)
      (DependentInnerEditor.encoding e₁)
      (DependentInnerEditor.state-encoding e₂)
  ; encoding
    = dependent-encoding-sigma
      (DependentInnerEditor.encoding e₁)
      (DependentInnerEditor.encoding e₂)
  ; split-functor
    = dependent-split-functor-sigma
      (DependentInnerEditor.split-functor e₁)
      (DependentInnerEditor.split-functor e₂)
  }

