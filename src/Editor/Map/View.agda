module Editor.Map.View where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.Function
  using (DependentFunction)
open import Category.Function.Compose
  using (dependent-function-compose)
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Data.Bool
  using (Bool)
open import Data.Function
  using (const)
open import Data.Nat
  using (ℕ; suc; zero)
open import Editor as _
  using (DependentEditor; DependentInnerEditor; DependentSplitEditor;
    DependentSplitEditor'; Editor; InnerEditor; SplitEditor)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)
open import Stack.Compose
  using (view-stack-map-compose-with)

-- ## Base

-- ### Editor

editor-map-view-with
  : {V W : ViewStack}
  → {E : EventStack}
  → {C : StateCategory}
  → (StateCategory.Object C → ViewStackMap V W)
  → Editor V E C
  → Editor W E C
editor-map-view-with F e
  = record
  { Editor e
  ; draw-stack
    = view-stack-map-compose-with F
      (Editor.draw-stack e)
  }

-- ## Dependent

-- ### DependentEditor

dependent-editor-map-view-with
  : {V W : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → DependentFunction C' (ViewStackMap V W)
  → DependentEditor V E C'
  → DependentEditor W E C'
dependent-editor-map-view-with {n = zero} F e
  = editor-map-view-with F e
dependent-editor-map-view-with {n = suc _} F e
  = record
  { tail
    = λ x → dependent-editor-map-view-with
      (DependentFunction.tail F x)
      (DependentEditor.tail e x)
  }

-- ### DependentSplitEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  where

  dependent-split-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → DependentSplitEditor V E C'
    → DependentSplitEditor W E C'
  dependent-split-editor-map-view-with F e
    = record
    { DependentSplitEditor' e
    ; editor
      = dependent-editor-map-view-with
        (dependent-function-compose F
          (DependentSplitEditor.bool-function e))
        (DependentSplitEditor.editor e)
    }

  dependent-split-editor-map-view
    : ViewStackMap V W
    → DependentSplitEditor V E C'
    → DependentSplitEditor W E C'
  dependent-split-editor-map-view F
    = dependent-split-editor-map-view-with (const F)

-- ### DependentInnerEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  where

  dependent-inner-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → DependentInnerEditor V E S P C'
    → DependentInnerEditor W E S P C'
  dependent-inner-editor-map-view-with F e
    = record
    { DependentInnerEditor e
    ; editor
      = dependent-editor-map-view-with
        (dependent-function-compose F
          (DependentInnerEditor.bool-function e))
        (DependentInnerEditor.editor e)
    }

  dependent-inner-editor-map-view
    : ViewStackMap V W
    → DependentInnerEditor V E S P C'
    → DependentInnerEditor W E S P C'
  dependent-inner-editor-map-view F
    = dependent-inner-editor-map-view-with (const F)

-- ## Nondependent

-- ### SplitEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {C : Category}
  where

  split-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → SplitEditor V E C
    → SplitEditor W E C
  split-editor-map-view-with
    = dependent-split-editor-map-view-with

  split-editor-map-view
    : ViewStackMap V W
    → SplitEditor V E C
    → SplitEditor W E C
  split-editor-map-view
    = dependent-split-editor-map-view

-- ### InnerEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S P : Set}
  {C : Category}
  where

  inner-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → InnerEditor V E S P C
    → InnerEditor W E S P C
  inner-editor-map-view-with
    = dependent-inner-editor-map-view-with

  inner-editor-map-view
    : ViewStackMap V W
    → InnerEditor V E S P C
    → InnerEditor W E S P C
  inner-editor-map-view
    = dependent-inner-editor-map-view

