module Editor.Collection.Unit where

open import Category
  using (ChainCategory)
open import Category.Collection.Unit
  using (category-collection-unit; dependent-category-collection-unit)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Relation
  using (DependentSimpleDecidable; DependentSimpleRelation; simple-decidable)
open import Category.Split.Collection.Unit
  using (dependent-split-functor-collection-unit)
open import Data.Direction
  using (Direction)
open import Data.Function
  using (_∘_)
open import Data.List
  using (List)
open import Data.Nat
  using (ℕ)
open import Data.Relation
  using (Decidable; Relation)
open import Editor
  using (DependentInnerEditor; DependentSplitEditor; InnerEditor; SplitEditor)
open import Editor.List.Unit
  using (dependent-inner-editor-list-unit; dependent-split-editor-list-unit)
open import Editor.Map
  using (dependent-inner-editor-map; dependent-split-editor-map)
open import Editor.Simple
  using (DependentSimpleInnerEditor; DependentSimpleSplitEditor;
    SimpleInnerEditor; SimpleSplitEditor)
open import Stack
  using (EventStack; ViewStack)
open import Stack.List
  using (event-stack-list; view-stack-list)

-- ## Dependent

-- ### DependentSplitEditor

-- Takes direction from earlier to later elements.
dependent-split-editor-collection-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → (d : DependentSimpleDecidable R)
  → Direction
  → DependentSimpleSplitEditor V E C'
  → DependentSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-category-collection-unit d)
dependent-split-editor-collection-unit d d'
  = dependent-split-editor-map (dependent-split-functor-collection-unit d)
  ∘ dependent-split-editor-list-unit d'

-- ### DependentInnerEditor

-- Takes direction from earlier to later elements.
dependent-inner-editor-collection-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → (d : DependentSimpleDecidable R)
  → Direction
  → DependentSimpleInnerEditor V E S P C'
  → DependentInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (dependent-category-collection-unit d)
dependent-inner-editor-collection-unit d d'
  = dependent-inner-editor-map (dependent-split-functor-collection-unit d)
  ∘ dependent-inner-editor-list-unit d'

-- ## Nondependent

-- ### SplitEditor

-- Takes direction from earlier to later elements.
split-editor-collection-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → (R : Relation A)
  → (d : Decidable R)
  → Direction
  → SimpleSplitEditor V E A
  → SplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (category-collection-unit R d)
split-editor-collection-unit R d
  = dependent-split-editor-collection-unit (simple-decidable R d)

-- ### InnerEditor

-- Takes direction from earlier to later elements.
inner-editor-collection-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {S P A : Set}
  → (R : Relation A)
  → (d : Decidable R)
  → Direction
  → SimpleInnerEditor V E S P A
  → InnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (category-collection-unit R d)
inner-editor-collection-unit R d
  = dependent-inner-editor-collection-unit (simple-decidable R d)

