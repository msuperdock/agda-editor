module Editor.Simple.List where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory)
open import Category.Simple.Bool.List
  using (dependent-simple-bool-function-list)
open import Category.Simple.List
  using (dependent-set-list; dependent-simple-category-list)
open import Category.Simple.Partial.List
  using (dependent-simple-partial-function-list)
open import Category.Simple.Split.List
  using (dependent-simple-split-functor-list)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.List
  using (dependent-simple-state-category-list)
open import Data.Direction
  using (Direction)
open import Data.Function
  using (_$_)
open import Data.List
  using (List)
open import Data.Nat
  using (ℕ)
open import Editor.List
  using (dependent-editor-list)
open import Editor.Simple
  using (DependentSimpleEditor; DependentSimpleInnerEditor;
    DependentSimpleMainEditor; DependentSimplePartialEditor;
    DependentSimpleSplitEditor; SimpleInnerEditor; SimpleMainEditor;
    SimplePartialEditor; SimpleSplitEditor; dependent-editor-simple)
open import Editor.Unit
  using (dependent-editor-unit)
open import Encoding.Simple.List
  using (dependent-simple-encoding-list)
open import Encoding.Simple.State.List
  using (dependent-simple-state-encoding-list)
open import Stack
  using (EventStack; ViewStack)
open import Stack.List
  using (event-stack-list; view-stack-list)

-- ## Dependent

-- ### DependentSimpleEditor

-- Takes direction from earlier to later elements.
dependent-simple-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → Direction
  → DependentSimpleEditor V E C'
  → DependentSimpleEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-simple-state-category-list C')
dependent-simple-editor-list d e
  = dependent-editor-simple
  $ dependent-editor-list d
    (dependent-editor-unit e)

-- ### DependentSimplePartialEditor

-- Takes direction from earlier to later elements.
dependent-simple-partial-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → Direction
  → DependentSimplePartialEditor V E C'
  → DependentSimplePartialEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-set-list C')
dependent-simple-partial-editor-list d e
  = record
  { editor
    = dependent-simple-editor-list d
      (DependentSimplePartialEditor.editor e)
  ; partial-function
    = dependent-simple-partial-function-list
      (DependentSimplePartialEditor.partial-function e)
  }

-- ### DependentSimpleSplitEditor

-- Takes direction from earlier to later elements.
dependent-simple-split-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → Direction
  → DependentSimpleSplitEditor V E C'
  → DependentSimpleSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-simple-category-list C')
dependent-simple-split-editor-list d e
  = record
  { editor
    = dependent-simple-editor-list d
      (DependentSimpleSplitEditor.editor e)
  ; split-functor
    = dependent-simple-split-functor-list
      (DependentSimpleSplitEditor.split-functor e)
  }

-- ### DependentSimpleMainEditor

-- Takes direction from earlier to later elements.
dependent-simple-main-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {S : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → Direction
  → DependentSimpleMainEditor V E S C
  → DependentSimpleMainEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S) C
dependent-simple-main-editor-list d e
  = record
  { editor
    = dependent-simple-editor-list d
      (DependentSimpleMainEditor.editor e)
  ; state-encoding
    = dependent-simple-state-encoding-list
      (DependentSimpleMainEditor.state-encoding e)
  ; bool-function
    = dependent-simple-bool-function-list
      (DependentSimpleMainEditor.bool-function e)
  }

-- ### DependentSimpleInnerEditor

-- Takes direction from earlier to later elements.
dependent-simple-inner-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → Direction
  → DependentSimpleInnerEditor V E S P C'
  → DependentSimpleInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (dependent-simple-category-list C')
dependent-simple-inner-editor-list d e
  = record
  { editor
    = dependent-simple-editor-list d
      (DependentSimpleInnerEditor.editor e)
  ; state-encoding
    = dependent-simple-state-encoding-list
      (DependentSimpleInnerEditor.state-encoding e)
  ; encoding
    = dependent-simple-encoding-list
      (DependentSimpleInnerEditor.encoding e)
  ; split-functor
    = dependent-simple-split-functor-list
      (DependentSimpleInnerEditor.split-functor e)
  }

-- ## Nondependent

-- ### SimplePartialEditor

-- Takes direction from earlier to later elements.
simple-partial-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → Direction
  → SimplePartialEditor V E A
  → SimplePartialEditor
    (view-stack-list V)
    (event-stack-list E)
    (List A)
simple-partial-editor-list
  = dependent-simple-partial-editor-list

-- ### SimpleSplitEditor

-- Takes direction from earlier to later elements.
simple-split-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → Direction
  → SimpleSplitEditor V E A
  → SimpleSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (List A)
simple-split-editor-list
  = dependent-simple-split-editor-list

-- ### SimpleMainEditor

-- Takes direction from earlier to later elements.
simple-main-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {S : Set}
  → Direction
  → SimpleMainEditor V E S
  → SimpleMainEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
simple-main-editor-list
  = dependent-simple-main-editor-list

-- ### SimpleInnerEditor

-- Takes direction from earlier to later elements.
simple-inner-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {S P A : Set}
  → Direction
  → SimpleInnerEditor V E S P A
  → SimpleInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (List A)
simple-inner-editor-list
  = dependent-simple-inner-editor-list

