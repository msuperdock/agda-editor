module Editor.Simple.Product where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory)
open import Category.Simple.Bool.Product
  using (dependent-simple-bool-function-product)
open import Category.Simple.Partial.Product
  using (dependent-simple-partial-function-product)
open import Category.Simple.Product
  using (dependent-set-product; dependent-simple-category-product)
open import Category.Simple.Split.Product
  using (dependent-simple-split-functor-product)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.Product
  using (dependent-simple-state-category-product)
open import Data.Direction
  using (Direction)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)
open import Data.Sigma
  using (_×_)
open import Editor.Product
  using (dependent-editor-product)
open import Editor.Simple
  using (DependentSimpleEditor; DependentSimpleInnerEditor;
    DependentSimpleMainEditor; DependentSimplePartialEditor;
    DependentSimpleSplitEditor; SimpleInnerEditor; SimpleMainEditor;
    SimplePartialEditor; SimpleSplitEditor; dependent-editor-simple)
open import Editor.Unit
  using (dependent-editor-unit)
open import Encoding.Simple.Product
  using (dependent-simple-encoding-product)
open import Encoding.Simple.State.Product
  using (dependent-simple-state-encoding-product)
open import Stack
  using (EventStack; ViewStack)
open import Stack.Product
  using (event-stack-product; view-stack-product)

-- ## Dependent

-- ### DependentSimpleEditor

-- Takes direction from first to second component.
dependent-simple-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleStateCategory C}
  → Direction
  → DependentSimpleEditor V₁ E₁ C₁'
  → DependentSimpleEditor V₂ E₂ C₂'
  → DependentSimpleEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (dependent-simple-state-category-product C₁' C₂')
dependent-simple-editor-product d e₁ e₂
  = dependent-editor-simple
  $ dependent-editor-product d
    (dependent-editor-unit e₁)
    (dependent-editor-unit e₂)

-- ### DependentSimplePartialEditor

-- Takes direction from first to second component.
dependent-simple-partial-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSet C}
  → Direction
  → DependentSimplePartialEditor V₁ E₁ C₁'
  → DependentSimplePartialEditor V₂ E₂ C₂'
  → DependentSimplePartialEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (dependent-set-product C₁' C₂')
dependent-simple-partial-editor-product d e₁ e₂
  = record
  { editor
    = dependent-simple-editor-product d
      (DependentSimplePartialEditor.editor e₁)
      (DependentSimplePartialEditor.editor e₂)
  ; partial-function
    = dependent-simple-partial-function-product
      (DependentSimplePartialEditor.partial-function e₁)
      (DependentSimplePartialEditor.partial-function e₂)
  }

-- ### DependentSimpleSplitEditor

-- Takes direction from first to second component.
dependent-simple-split-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleCategory C}
  → Direction
  → DependentSimpleSplitEditor V₁ E₁ C₁'
  → DependentSimpleSplitEditor V₂ E₂ C₂'
  → DependentSimpleSplitEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (dependent-simple-category-product C₁' C₂')
dependent-simple-split-editor-product d e₁ e₂
  = record
  { editor
    = dependent-simple-editor-product d
      (DependentSimpleSplitEditor.editor e₁)
      (DependentSimpleSplitEditor.editor e₂)
  ; split-functor
    = dependent-simple-split-functor-product
      (DependentSimpleSplitEditor.split-functor e₁)
      (DependentSimpleSplitEditor.split-functor e₂)
  }

-- ### DependentSimpleMainEditor

-- Takes direction from first to second component.
dependent-simple-main-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → Direction
  → DependentSimpleMainEditor V₁ E₁ S₁ C
  → DependentSimpleMainEditor V₂ E₂ S₂ C
  → DependentSimpleMainEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (S₁ × S₂) C
dependent-simple-main-editor-product d e₁ e₂
  = record
  { editor
    = dependent-simple-editor-product d
      (DependentSimpleMainEditor.editor e₁)
      (DependentSimpleMainEditor.editor e₂)
  ; state-encoding
    = dependent-simple-state-encoding-product
      (DependentSimpleMainEditor.state-encoding e₁)
      (DependentSimpleMainEditor.state-encoding e₂)
  ; bool-function
    = dependent-simple-bool-function-product
      (DependentSimpleMainEditor.bool-function e₁)
      (DependentSimpleMainEditor.bool-function e₂)
  }

-- ### DependentSimpleInnerEditor

-- Takes direction from first to second component.
dependent-simple-inner-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ P₁ P₂ : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleCategory C}
  → Direction
  → DependentSimpleInnerEditor V₁ E₁ S₁ P₁ C₁'
  → DependentSimpleInnerEditor V₂ E₂ S₂ P₂ C₂'
  → DependentSimpleInnerEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (S₁ × S₂)
    (P₁ × P₂)
    (dependent-simple-category-product C₁' C₂')
dependent-simple-inner-editor-product d e₁ e₂
  = record
  { editor
    = dependent-simple-editor-product d
      (DependentSimpleInnerEditor.editor e₁)
      (DependentSimpleInnerEditor.editor e₂)
  ; state-encoding
    = dependent-simple-state-encoding-product
      (DependentSimpleInnerEditor.state-encoding e₁)
      (DependentSimpleInnerEditor.state-encoding e₂)
  ; encoding
    = dependent-simple-encoding-product
      (DependentSimpleInnerEditor.encoding e₁)
      (DependentSimpleInnerEditor.encoding e₂)
  ; split-functor
    = dependent-simple-split-functor-product
      (DependentSimpleInnerEditor.split-functor e₁)
      (DependentSimpleInnerEditor.split-functor e₂)
  }

-- ## Nondependent

-- ### SimplePartialEditor

-- Takes direction from first to second component.
simple-partial-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {A₁ A₂ : Set}
  → Direction
  → SimplePartialEditor V₁ E₁ A₁
  → SimplePartialEditor V₂ E₂ A₂
  → SimplePartialEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (A₁ × A₂)
simple-partial-editor-product
  = dependent-simple-partial-editor-product

-- ### SimpleSplitEditor

-- Takes direction from first to second component.
simple-split-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {A₁ A₂ : Set}
  → Direction
  → SimpleSplitEditor V₁ E₁ A₁
  → SimpleSplitEditor V₂ E₂ A₂
  → SimpleSplitEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (A₁ × A₂)
simple-split-editor-product
  = dependent-simple-split-editor-product

-- ### SimpleMainEditor

-- Takes direction from first to second component.
simple-main-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ : Set}
  → Direction
  → SimpleMainEditor V₁ E₁ S₁
  → SimpleMainEditor V₂ E₂ S₂
  → SimpleMainEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (S₁ × S₂)
simple-main-editor-product
  = dependent-simple-main-editor-product

-- ### SimpleInnerEditor

-- Takes direction from first to second component.
simple-inner-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ P₁ P₂ A₁ A₂ : Set}
  → Direction
  → SimpleInnerEditor V₁ E₁ S₁ P₁ A₁
  → SimpleInnerEditor V₂ E₂ S₂ P₂ A₂
  → SimpleInnerEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (S₁ × S₂)
    (P₁ × P₂)
    (A₁ × A₂)
simple-inner-editor-product
  = dependent-simple-inner-editor-product

