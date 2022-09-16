module Editor.List.Unit where

open import Category
  using (ChainCategory)
open import Category.List.Unit
  using (category-list-unit; dependent-category-list-unit)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Split.List.Unit
  using (dependent-split-functor-list-unit)
open import Data.Direction
  using (Direction)
open import Data.Function
  using (_∘_)
open import Data.List
  using (List)
open import Data.Nat
  using (ℕ)
open import Editor
  using (DependentInnerEditor; DependentSplitEditor; InnerEditor; SplitEditor)
open import Editor.List
  using (dependent-inner-editor-list; dependent-split-editor-list)
open import Editor.Map
  using (dependent-inner-editor-map; dependent-split-editor-map)
open import Editor.Simple
  using (DependentSimpleInnerEditor; DependentSimpleSplitEditor;
    SimpleInnerEditor; SimpleSplitEditor)
open import Editor.Unit
  using (dependent-inner-editor-unit; dependent-split-editor-unit)
open import Stack
  using (EventStack; ViewStack)
open import Stack.List
  using (event-stack-list; view-stack-list)

-- ## Dependent

-- ### DependentSplitEditor

-- Takes direction from earlier to later elements.
dependent-split-editor-list-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → Direction
  → DependentSimpleSplitEditor V E C'
  → DependentSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-category-list-unit C')
dependent-split-editor-list-unit {C' = C'} d
  = dependent-split-editor-map (dependent-split-functor-list-unit C')
  ∘ dependent-split-editor-list d
  ∘ dependent-split-editor-unit

-- ### DependentInnerEditor

-- Takes direction from earlier to later elements.
dependent-inner-editor-list-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → Direction
  → DependentSimpleInnerEditor V E S P C'
  → DependentInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (dependent-category-list-unit C')
dependent-inner-editor-list-unit {C' = C'} d
  = dependent-inner-editor-map (dependent-split-functor-list-unit C')
  ∘ dependent-inner-editor-list d
  ∘ dependent-inner-editor-unit

-- ## Nondependent

-- ### SplitEditor

-- Takes direction from earlier to later elements.
split-editor-list-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → Direction
  → SimpleSplitEditor V E A
  → SplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (category-list-unit A)
split-editor-list-unit
  = dependent-split-editor-list-unit

-- ### InnerEditor

-- Takes direction from earlier to later elements.
inner-editor-list-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {S P A : Set}
  → Direction
  → SimpleInnerEditor V E S P A
  → InnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (category-list-unit A)
inner-editor-list-unit
  = dependent-inner-editor-list-unit

