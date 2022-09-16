module Editor.Collection where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.Collection
  using (category-collection; dependent-category-collection)
open import Category.Relation
  using (DependentDecidable; DependentRelation; decidable)
open import Category.Split.Collection
  using (dependent-split-functor-collection)
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
open import Editor.List
  using (dependent-inner-editor-list; dependent-split-editor-list)
open import Editor.Map
  using (dependent-inner-editor-map; dependent-split-editor-map)
open import Stack
  using (EventStack; ViewStack)
open import Stack.List
  using (event-stack-list; view-stack-list)

-- ## Dependent

-- ### DependentSplitEditor

dependent-split-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {R : DependentRelation C'}
  → (d : DependentDecidable R)
  → Direction
  → DependentSplitEditor V E C'
  → DependentSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-category-collection d)
dependent-split-editor-collection d d'
  = dependent-split-editor-map (dependent-split-functor-collection d)
  ∘ dependent-split-editor-list d'

-- ### DependentInnerEditor

dependent-inner-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {R : DependentRelation C'}
  → (d : DependentDecidable R)
  → Direction
  → DependentInnerEditor V E S P C'
  → DependentInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (dependent-category-collection d)
dependent-inner-editor-collection d d'
  = dependent-inner-editor-map (dependent-split-functor-collection d)
  ∘ dependent-inner-editor-list d'

-- ## Nondependent

-- ### SplitEditor

-- Takes direction from earlier to later elements.
split-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {C : Category}
  → (R : Relation (Category.Object C))
  → (d : Decidable R)
  → Direction
  → SplitEditor V E C
  → SplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (category-collection C R d)
split-editor-collection {C = C} R d
  = dependent-split-editor-collection (decidable C R d)

-- ### InnerEditor

-- Takes direction from earlier to later elements.
inner-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C : Category}
  → (R : Relation (Category.Object C))
  → (d : Decidable R)
  → Direction
  → InnerEditor V E S P C
  → InnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (category-collection C R d)
inner-editor-collection {C = C} R d
  = dependent-inner-editor-collection (decidable C R d)

