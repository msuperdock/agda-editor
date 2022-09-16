module Editor.Simple where

open import Category
  using (ChainCategory; chain-category₀)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory; simple-category)
open import Category.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Category.Simple.Partial
  using (DependentSimplePartialFunction)
open import Category.Simple.Split
  using (DependentSimpleSplitFunctor; SimpleSplitFunctor)
open import Category.Simple.State
  using (DependentSimpleStateCategory; SimpleStateCategory;
    dependent-state-category-simple)
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Data.Direction
  using (Direction)
open import Data.Equal
  using (_≡_)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Editor as _
  using (DependentEditor; Editor)
open import Encoding as _
  using (Encoding)
open import Encoding.Simple
  using (DependentSimpleEncoding)
open import Encoding.Simple.State
  using (DependentSimpleStateEncoding)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)

-- ## Base

-- ### SimpleEditor

-- #### Definition

record SimpleEditor
  (V : ViewStack)
  (E : EventStack)
  (A : Set)
  : Set₁
  where

  -- ##### Types

  open EventStack E

  private

    State
      : Set
    State
      = A

  -- ##### State

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

  -- ##### Draw

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

  -- ##### Mode

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

  -- ##### Handle

  field

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → Σ State StatePath
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (Σ State StatePath
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (Σ State StatePath
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
      → Σ State StatePath
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'

-- #### Conversion

module _
  {V : ViewStack}
  {E : EventStack}
  {C : StateCategory}
  where

  module EditorSimple
    (e : Editor V E C)
    where

    open EventStack E

    open StateCategory C
      using () renaming
      ( Object
        to State
      )

    open Editor e public
      hiding (handle; handle-escape; handle-return; handle-inner-return)

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → Σ State StatePath
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle s sp e'
      with Editor.handle e s sp e'
    ... | ι₁ (s' , sp' , _)
      = ι₁ (s' , sp')
    ... | ι₂ s'
      = ι₂ s'

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (Σ State StatePath
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-escape s sp
      with Editor.handle-escape e s sp
    ... | nothing
      = nothing
    ... | just (ι₁ (s' , sp' , _))
      = just (ι₁ (s' , sp'))
    ... | just (ι₂ s')
      = just (ι₂ s')

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (Σ State StatePath
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-return s sp
      with Editor.handle-return e s sp
    ... | nothing
      = nothing
    ... | just (ι₁ (s' , sp' , _))
      = just (ι₁ (s' , sp'))
    ... | just (ι₂ s')
      = just (ι₂ s')

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Σ State StatePath
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return s sp s' sp'
      with Editor.handle-inner-return e s sp s' sp'
    ... | ι₁ (s'' , sp'' , _)
      = ι₁ (s'' , sp'')
    ... | ι₂ s''
      = ι₂ s''

  editor-simple
    : Editor V E C
    → SimpleEditor V E
      (StateCategory.Object C)
  editor-simple e
    = record {EditorSimple e}

-- ## Dependent

-- ### DependentSimpleEditor

-- #### Types

DependentSimpleEditor
  : ViewStack
  → EventStack
  → {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleStateCategory C
  → Set₁

record DependentSimpleEditor'
  (V : ViewStack)
  (E : EventStack)
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSimpleStateCategory C)
  : Set₁

-- #### Definitions

DependentSimpleEditor V E {n = zero} C'
  = SimpleEditor V E (SimpleStateCategory.Object C')
DependentSimpleEditor V E {n = suc _} C'
  = DependentSimpleEditor' V E C'

record DependentSimpleEditor' V E {_ C} C' where

  inductive

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentSimpleEditor V E
        (DependentSimpleStateCategory.tail C' x)

module DependentSimpleEditor
  = DependentSimpleEditor'

-- #### Conversion

dependent-editor-simple
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → DependentEditor V E C'
  → DependentSimpleEditor V E
    (dependent-state-category-simple C')

dependent-editor-simple {n = zero} e
  = editor-simple e

dependent-editor-simple {n = suc _} e
  = record
  { tail
    = λ x → dependent-editor-simple
      (DependentEditor.tail e x)
  }

-- ### DependentSimplePartialEditor

record DependentSimplePartialEditor
  (V : ViewStack)
  (E : EventStack)
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentSet C)
  : Set₁
  where

  field
  
    {state-category}
      : DependentSimpleStateCategory C

    editor
      : DependentSimpleEditor V E state-category

    partial-function
      : DependentSimplePartialFunction state-category C'

  bool-function
    : DependentSimpleBoolFunction state-category
  bool-function
    = DependentSimplePartialFunction.bool-function partial-function

-- ### DependentSimpleSplitEditor

record DependentSimpleSplitEditor
  (V : ViewStack)
  (E : EventStack)
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentSimpleCategory C)
  : Set₁
  where

  field

    {state-category}
      : DependentSimpleStateCategory C

    editor
      : DependentSimpleEditor V E state-category

    split-functor
      : DependentSimpleSplitFunctor state-category C'

  partial-editor
    : DependentSimplePartialEditor V E
      (DependentSimpleCategory.set C')
  partial-editor
    = record
    { editor
      = editor
    ; partial-function
      = DependentSimpleSplitFunctor.partial-function split-functor
    }

  bool-function
    : DependentSimpleBoolFunction state-category
  bool-function
    = DependentSimpleSplitFunctor.bool-function split-functor

-- ### DependentSimpleMainEditor

record DependentSimpleMainEditor
  (V : ViewStack)
  (E : EventStack)
  (S : Set)
  {n : ℕ}
  (C : ChainCategory n)
  : Set₁
  where

  field

    {state-category}
      : DependentSimpleStateCategory C

    editor
      : DependentSimpleEditor V E state-category

    state-encoding
      : DependentSimpleStateEncoding state-category S

    bool-function
      : DependentSimpleBoolFunction state-category

-- ### DependentSimpleInnerEditor

record DependentSimpleInnerEditor
  (V : ViewStack)
  (E : EventStack)
  (S P : Set)
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentSimpleCategory C)
  : Set₁
  where

  field

    {state-category}
      : DependentSimpleStateCategory C

    editor
      : DependentSimpleEditor V E state-category

    state-encoding
      : DependentSimpleStateEncoding state-category S

    encoding
      : DependentSimpleEncoding C' P

    split-functor
      : DependentSimpleSplitFunctor state-category C'

  split-editor
    : DependentSimpleSplitEditor V E C'
  split-editor
    = record
    { editor
      = editor
    ; split-functor
      = split-functor
    }

  partial-editor
    : DependentSimplePartialEditor V E
      (DependentSimpleCategory.set C')
  partial-editor
    = record
    { editor
      = editor
    ; partial-function
      = DependentSimpleSplitFunctor.partial-function split-functor
    }

  bool-function
    : DependentSimpleBoolFunction state-category
  bool-function
    = DependentSimpleSplitFunctor.bool-function split-functor

  main-editor
    : DependentSimpleMainEditor V E S C
  main-editor
    = record
    { editor
      = editor
    ; state-encoding
      = state-encoding
    ; bool-function
      = bool-function
    }

-- ## Nondependent

-- ### SimplePartialEditor

SimplePartialEditor
  : ViewStack
  → EventStack
  → Set
  → Set₁
SimplePartialEditor V E
  = DependentSimplePartialEditor V E

module SimplePartialEditor
  {V : ViewStack}
  {E : EventStack}
  {A : Set}
  (e : SimplePartialEditor V E A)
  where

  open DependentSimplePartialEditor e public

  open SimpleStateCategory state-category public
    using () renaming
    ( Object
      to State
    )

-- ### SimpleSplitEditor

-- #### Definition

SimpleSplitEditor
  : ViewStack
  → EventStack
  → Set
  → Set₁
SimpleSplitEditor V E A
  = DependentSimpleSplitEditor V E
    (simple-category A)

-- #### Module

module SimpleSplitEditor
  {V : ViewStack}
  {E : EventStack}
  {A : Set}
  (e : SimpleSplitEditor V E A)
  where

  open DependentSimpleSplitEditor e public

  open SimpleStateCategory state-category public
    using () renaming
    ( Object
      to State
    )

  open SimpleSplitFunctor split-functor public

  draw-pure
    : A
    → ViewStack.View V
  draw-pure x
    = SimpleEditor.draw editor (unbase x)

-- ### SimpleMainEditor

-- #### Definition

SimpleMainEditor
  : ViewStack
  → EventStack
  → Set
  → Set₁
SimpleMainEditor V E S
  = DependentSimpleMainEditor V E S
    chain-category₀

-- #### Module

module SimpleMainEditor
  {V : ViewStack}
  {E : EventStack}
  {S : Set}
  (e : SimpleMainEditor V E S)
  where

  open DependentSimpleMainEditor e public

  open SimpleStateCategory state-category public
    using () renaming
    ( Object
      to State
    )

  open Encoding state-encoding public
    using () renaming
    ( encode
      to state-encode
    ; decode
      to state-decode
    ; decode-encode
      to state-decode-encode
    )

-- ### SimpleInnerEditor

-- #### Definition

SimpleInnerEditor
  : ViewStack
  → EventStack
  → Set
  → Set
  → Set
  → Set₁
SimpleInnerEditor V E S P A
  = DependentSimpleInnerEditor V E S P
    (simple-category A)

-- #### Module

module SimpleInnerEditor
  {V : ViewStack}
  {E : EventStack}
  {S P A : Set}
  (e : SimpleInnerEditor V E S P A)
  where

  open DependentSimpleInnerEditor e public

  open SimpleStateCategory state-category public
    using () renaming
    ( Object
      to State
    )

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

  open SimpleSplitFunctor split-functor public

  draw-pure
    : A
    → ViewStack.View V
  draw-pure x
    = SimpleEditor.draw editor (unbase x)

