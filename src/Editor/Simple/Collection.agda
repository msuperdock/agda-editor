module Editor.Simple.Collection where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory)
open import Category.Simple.Collection
  using (dependent-set-collection; dependent-simple-category-collection)
open import Category.Simple.Partial.Collection
  using (dependent-simple-partial-function-collection)
open import Category.Simple.Relation
  using (DependentDecidable; DependentRelation;
    DependentSimpleDecidable; DependentSimpleRelation; simple-decidable)
open import Category.Simple.Split.Collection
  using (dependent-simple-split-functor-collection)
open import Data.Collection
  using (Collection)
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
open import Editor.Simple
  using (DependentSimpleInnerEditor; DependentSimplePartialEditor;
    DependentSimpleSplitEditor; SimpleInnerEditor; SimplePartialEditor;
    SimpleSplitEditor)
open import Editor.Simple.List
  using (dependent-simple-inner-editor-list;
    dependent-simple-partial-editor-list; dependent-simple-split-editor-list)
open import Editor.Simple.Map
  using (dependent-simple-inner-editor-map; dependent-simple-partial-editor-map;
    dependent-simple-split-editor-map)
open import Stack
  using (EventStack; ViewStack)
open import Stack.List
  using (event-stack-list; view-stack-list)

-- ## Dependent

-- ### DependentSimplePartialEditor

dependent-simple-partial-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → {R : DependentRelation C'}
  → DependentDecidable C' R
  → Direction
  → DependentSimplePartialEditor V E C'
  → DependentSimplePartialEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-set-collection R)
dependent-simple-partial-editor-collection d d'
  = dependent-simple-partial-editor-map
    (dependent-simple-partial-function-collection d)
  ∘ dependent-simple-partial-editor-list d'

-- ### DependentSimpleSplitEditor

dependent-simple-split-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → (d : DependentSimpleDecidable R)
  → Direction
  → DependentSimpleSplitEditor V E C'
  → DependentSimpleSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-simple-category-collection d)
dependent-simple-split-editor-collection d d'
  = dependent-simple-split-editor-map
    (dependent-simple-split-functor-collection d)
  ∘ dependent-simple-split-editor-list d'

-- ### DependentSimpleInnerEditor

dependent-simple-inner-editor-collection
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
  → DependentSimpleInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (dependent-simple-category-collection d)
dependent-simple-inner-editor-collection d d'
  = dependent-simple-inner-editor-map
    (dependent-simple-split-functor-collection d)
  ∘ dependent-simple-inner-editor-list d'

-- ## Nondependent

-- ### SimplePartialEditor

-- Takes direction from earlier to later elements.
simple-partial-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → (R : Relation A)
  → Decidable R
  → Direction
  → SimplePartialEditor V E A
  → SimplePartialEditor
    (view-stack-list V)
    (event-stack-list E)
    (Collection R)
simple-partial-editor-collection _
  = dependent-simple-partial-editor-collection

-- ### SimpleSplitEditor

-- Takes direction from earlier to later elements.
simple-split-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → (R : Relation A)
  → Decidable R
  → Direction
  → SimpleSplitEditor V E A
  → SimpleSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (Collection R)
simple-split-editor-collection R d
  = dependent-simple-split-editor-collection (simple-decidable R d)

-- ### SimpleInnerEditor

-- Takes direction from earlier to later elements.
simple-inner-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {S P A : Set}
  → (R : Relation A)
  → Decidable R
  → Direction
  → SimpleInnerEditor V E S P A
  → SimpleInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (Collection R)
simple-inner-editor-collection R d
  = dependent-simple-inner-editor-collection (simple-decidable R d)

