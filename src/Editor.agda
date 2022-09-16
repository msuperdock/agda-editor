module Editor where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.Bool
  using (DependentBoolFunction)
open import Category.Split
  using (DependentSplitFunctor; SplitFunctor)
open import Category.State
  using (DependentStateCategory; DependentStateCategory₁; StateCategory)
open import Data.Direction
  using (Direction)
open import Data.Equal
  using (_≡_)
open import Data.Maybe
  using (Maybe; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ)
open import Data.Sum
  using (_⊔_)
open import Encoding as _
  using (DependentEncoding; Encoding)
open import Encoding.State
  using (DependentStateEncoding)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)

-- ## Base

-- ### Editor

record Editor
  (V : ViewStack)
  (E : EventStack)
  (C : StateCategory)
  : Set₁
  where
 
  -- #### Types

  open EventStack E

  open StateCategory C
    using () renaming
    ( Object
      to State
    ; Arrow
      to StateArrow
    )

  -- #### State

  field

    StatePath
      : State
      → Set

    StateInner
      : (s : State)
      → StatePath s
      → Set

    StateInnerPath
      : (s : State)
      → (sp : StatePath s)
      → StateInner s sp
      → Set

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

  field

    initial
      : State

    initial-path
      : (s : State)
      → StatePath s

  initial-path'
    : StatePath initial
  initial-path'
    = initial-path initial

  field

    -- The initial path when entering from the given direction.
    initial-path-with
      : (s : State)
      → Direction
      → StatePath s

  -- #### Draw

  field

    draw-stack
      : ViewStackMap StateStack V

  open ViewStackMap draw-stack public
    using () renaming
    ( view
      to draw
    ; view-with
      to draw-with
    ; view-path
      to draw-path
    ; view-inner-with
      to draw-inner-with
    ; view-inner-path
      to draw-inner-path
    )

  -- #### Mode

  field

    mode
      : (s : State)
      → StatePath s
      → Mode

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner

  -- #### Handle

  field

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → Maybe (StatePath s)

    handle-direction-valid
      : (s : State)
      → (d : Direction)
      → handle-direction s (initial-path-with s d) d ≡ nothing

    handle-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → EventInner (mode-inner s sp s' sp')
      → Σ (StateInner s sp) (StateInnerPath s sp)

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'

-- ## Dependent

-- ### DependentEditor

-- #### Types

DependentEditor
  : ViewStack
  → EventStack
  → {n : ℕ}
  → {C : ChainCategory n}
  → DependentStateCategory C
  → Set₁

record DependentEditor'
  (V : ViewStack)
  (E : EventStack)
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentStateCategory C)
  : Set₁

-- #### Definitions

DependentEditor V E {n = zero}
  = Editor V E
DependentEditor V E {n = suc _}
  = DependentEditor' V E

record DependentEditor' V E {_ C} C' where

  inductive

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentEditor V E
        (DependentStateCategory.tail C' x)

module DependentEditor
  = DependentEditor'

-- ### DependentSplitEditor

-- #### Definition

record DependentSplitEditor'
  (V : ViewStack)
  (E : EventStack)
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentCategory C)
  : Set₁
  where

  field

    {state-category}
      : DependentStateCategory C

    editor
      : DependentEditor V E state-category

    split-functor
      : DependentSplitFunctor state-category C'

  bool-function
    : DependentBoolFunction state-category
  bool-function
    = DependentSplitFunctor.bool-function split-functor

DependentSplitEditor
  = DependentSplitEditor'

-- #### Module

module DependentSplitEditor
  {V : ViewStack}
  {E : EventStack}
  where

  open module DependentSplitEditor'' {n C C'} e
    = DependentSplitEditor' {V} {E} {n} {C} {C'} e public

  tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → DependentSplitEditor V E C'
    → (x : ChainCategory.Object C)
    → DependentSplitEditor V E
      (DependentCategory.tail C' x)
  tail e x
    = record
    { editor
      = DependentEditor.tail (editor e) x
    ; split-functor
      = DependentSplitFunctor.tail (split-functor e) x
    }

-- ### DependentInnerEditor

record DependentInnerEditor
  (V : ViewStack)
  (E : EventStack)
  (S P : Set)
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentCategory C)
  : Set₁
  where

  field

    {state-category}
      : DependentStateCategory C

    editor
      : DependentEditor V E state-category

    state-encoding
      : DependentStateEncoding state-category S

    encoding
      : DependentEncoding C' P

    split-functor
      : DependentSplitFunctor state-category C'
  
  split-editor
    : DependentSplitEditor V E C'
  split-editor
    = record
    { editor
      = editor
    ; split-functor
      = split-functor
    }

  bool-function
    : DependentBoolFunction state-category
  bool-function
    = DependentSplitFunctor.bool-function split-functor

-- ## Nondependent

-- ### SplitEditor

-- #### Definition

SplitEditor
  : ViewStack
  → EventStack
  → Category
  → Set₁
SplitEditor V E
  = DependentSplitEditor V E

-- #### Module

module SplitEditor
  {V : ViewStack}
  {E : EventStack}
  {C : Category}
  (e : SplitEditor V E C)
  where

  open DependentSplitEditor' e public

  open StateCategory state-category public
    using () renaming
    ( Object
      to State
    ; Arrow
      to StateArrow
    ; identity'
      to state-identity
    )

  state-compose
    : {s t u : State}
    → StateArrow t u
    → StateArrow s t
    → StateArrow s u
  state-compose f g
    = StateCategory.simplify' state-category
      (StateCategory.compose' state-category f g)

  open Editor editor public

  open SplitFunctor split-functor public

-- ### InnerEditor

-- #### Definition

InnerEditor
  : ViewStack
  → EventStack
  → Set
  → Set
  → Category
  → Set₁
InnerEditor V E S P
  = DependentInnerEditor V E S P

-- #### Module

module InnerEditor
  {V : ViewStack}
  {E : EventStack}
  {S P : Set}
  {C : Category}
  (e : InnerEditor V E S P C)
  where

  open DependentInnerEditor e public

  open StateCategory state-category public
    using () renaming
    ( Object
      to State
    ; Arrow
      to StateArrow
    ; identity'
      to state-identity
    )

  state-compose
    : {s t u : State}
    → StateArrow t u
    → StateArrow s t
    → StateArrow s u
  state-compose f g
    = StateCategory.simplify' state-category
      (StateCategory.compose' state-category f g)

  open Editor editor public

  open Encoding state-encoding public
    using () renaming
    ( encode
      to state-encode
    ; decode
      to state-decode
    ; decode-encode
      to state-decode-encode
    )

  open Encoding encoding public

  open SplitFunctor split-functor public

-- ## Dependent₁

-- ### DependentEditor₁

-- #### Definition

DependentEditor₁
  : ViewStack
  → EventStack
  → (C : Category)
  → DependentStateCategory₁ C
  → Set₁
DependentEditor₁ V E _
  = DependentEditor V E

-- #### Module

module DependentEditor₁
  {V : ViewStack}
  {E : EventStack}
  (C : Category)
  {C' : DependentStateCategory₁ C}
  (e : DependentEditor₁ V E C C')
  where

  open DependentEditor e public

  open module Editor' {x}
    = Editor (tail x) public

