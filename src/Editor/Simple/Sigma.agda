module Editor.Simple.Sigma where

open import Editor
  using (DependentInnerEditor; DependentSplitEditor)
open import Category
  using (ChainCategory; DependentCategory)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory)
open import Category.Simple.Bool.Sigma
  using (dependent-simple-bool-function-sigma)
open import Category.Simple.Partial.Sigma
  using (dependent-simple-partial-function-sigma)
open import Category.Simple.Sigma
  using (dependent-set-sigma; dependent-simple-category-sigma)
open import Category.Simple.Split.Sigma
  using (dependent-simple-split-functor-sigma)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.Sigma.Sum
  using (dependent-simple-state-category-sigma-sum)
open import Category.Snoc
  using (chain-category-snoc)
open import Data.Direction
  using (Direction)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ)
open import Data.Sigma
  using (_×_)
open import Data.Sum
  using (_⊔_)
open import Editor.Sigma
  using (dependent-editor-sigma)
open import Editor.Simple
  using (DependentSimpleEditor; DependentSimpleInnerEditor;
    DependentSimpleMainEditor; DependentSimplePartialEditor;
    DependentSimpleSplitEditor; dependent-editor-simple)
open import Editor.Unit
  using (dependent-editor-unit)
open import Encoding.Simple.Sigma
  using (dependent-simple-encoding-sigma)
open import Encoding.Simple.State.Sigma.Sum
  using (dependent-simple-state-encoding-sigma-sum)
open import Stack
  using (EventStack; ViewStack)
open import Stack.Sigma
  using (event-stack-sigma; view-stack-sigma)

-- ## Dependent

-- ### DependentSimpleEditor

-- Takes direction from first to second component.
dependent-simple-editor-sigma
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentSimpleStateCategory (chain-category-snoc C₁')}
  → Direction
  → (e₁ : DependentSplitEditor V₁ E₁ C₁')
  → DependentSimpleEditor V₂ E₂ C₂'
  → DependentSimpleEditor
    (view-stack-sigma V₁ V₂)
    (event-stack-sigma E₁ E₂)
    (dependent-simple-state-category-sigma-sum C₂'
      (DependentSplitEditor.split-functor e₁))
dependent-simple-editor-sigma d e₁ e₂
  = dependent-editor-simple
  $ dependent-editor-sigma d e₁
    (dependent-editor-unit e₂)

-- ### DependentSimplePartialEditor

-- Takes direction from first to second component.
dependent-simple-partial-editor-sigma
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentSet (chain-category-snoc C₁')}
  → Direction
  → DependentSplitEditor V₁ E₁ C₁'
  → DependentSimplePartialEditor V₂ E₂ C₂'
  → DependentSimplePartialEditor
    (view-stack-sigma V₁ V₂)
    (event-stack-sigma E₁ E₂)
    (dependent-set-sigma C₁' C₂')
dependent-simple-partial-editor-sigma d e₁ e₂
  = record
  { editor
    = dependent-simple-editor-sigma d e₁
      (DependentSimplePartialEditor.editor e₂)
  ; partial-function
    = dependent-simple-partial-function-sigma
      (DependentSplitEditor.split-functor e₁)
      (DependentSimplePartialEditor.partial-function e₂)
  }

-- ### DependentSimpleSplitEditor

-- Takes direction from first to second component.
dependent-simple-split-editor-sigma
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentSimpleCategory (chain-category-snoc C₁')}
  → Direction
  → DependentSplitEditor V₁ E₁ C₁'
  → DependentSimpleSplitEditor V₂ E₂ C₂'
  → DependentSimpleSplitEditor
    (view-stack-sigma V₁ V₂)
    (event-stack-sigma E₁ E₂)
    (dependent-simple-category-sigma C₁' C₂')
dependent-simple-split-editor-sigma d e₁ e₂
  = record
  { editor
    = dependent-simple-editor-sigma d e₁
      (DependentSimpleSplitEditor.editor e₂)
  ; split-functor
    = dependent-simple-split-functor-sigma
      (DependentSplitEditor.split-functor e₁)
      (DependentSimpleSplitEditor.split-functor e₂)
  }

-- ### DependentSimpleMainEditor

-- Takes direction from first to second component.
dependent-simple-main-editor-sigma
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ P₁ : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → Direction
  → DependentInnerEditor V₁ E₁ S₁ P₁ C₁'
  → DependentSimpleMainEditor V₂ E₂ S₂ (chain-category-snoc C₁')
  → DependentSimpleMainEditor
    (view-stack-sigma V₁ V₂)
    (event-stack-sigma E₁ E₂)
    (S₁ ⊔ P₁ × S₂) C
dependent-simple-main-editor-sigma d e₁ e₂
  = record
  { editor
    = dependent-simple-editor-sigma d
      (DependentInnerEditor.split-editor e₁)
      (DependentSimpleMainEditor.editor e₂)
  ; state-encoding
    = dependent-simple-state-encoding-sigma-sum
      (DependentInnerEditor.split-functor e₁)
      (DependentInnerEditor.state-encoding e₁)
      (DependentInnerEditor.encoding e₁)
      (DependentSimpleMainEditor.state-encoding e₂)
  ; bool-function
    = dependent-simple-bool-function-sigma
      (DependentInnerEditor.split-functor e₁)
      (DependentSimpleMainEditor.bool-function e₂)
  }

-- ### DependentSimpleInnerEditor

-- Takes direction from first to second component.
dependent-simple-inner-editor-sigma
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ P₁ P₂ : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentSimpleCategory (chain-category-snoc C₁')}
  → Direction
  → DependentInnerEditor V₁ E₁ S₁ P₁ C₁'
  → DependentSimpleInnerEditor V₂ E₂ S₂ P₂ C₂'
  → DependentSimpleInnerEditor
    (view-stack-sigma V₁ V₂)
    (event-stack-sigma E₁ E₂)
    (S₁ ⊔ P₁ × S₂)
    (P₁ × P₂)
    (dependent-simple-category-sigma C₁' C₂')
dependent-simple-inner-editor-sigma d e₁ e₂
  = record
  { editor
    = dependent-simple-editor-sigma d
      (DependentInnerEditor.split-editor e₁)
      (DependentSimpleInnerEditor.editor e₂)
  ; state-encoding
    = dependent-simple-state-encoding-sigma-sum
      (DependentInnerEditor.split-functor e₁)
      (DependentInnerEditor.state-encoding e₁)
      (DependentInnerEditor.encoding e₁)
      (DependentSimpleInnerEditor.state-encoding e₂)
  ; encoding
    = dependent-simple-encoding-sigma
      (DependentInnerEditor.encoding e₁)
      (DependentSimpleInnerEditor.encoding e₂)
  ; split-functor
    = dependent-simple-split-functor-sigma
      (DependentInnerEditor.split-functor e₁)
      (DependentSimpleInnerEditor.split-functor e₂)
  }

