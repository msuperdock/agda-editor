module Editor.Simple.Map.View where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory)
open import Category.Simple.Function
  using (DependentSimpleFunction)
open import Category.Simple.Function.Compose
  using (dependent-simple-function-compose)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Data.Bool
  using (Bool)
open import Data.Function
  using (_∘_; const)
open import Data.Nat
  using (ℕ; suc; zero)
open import Editor.Map.View
  using (editor-map-view-with)
open import Editor.Simple
  using (DependentSimpleEditor; DependentSimpleInnerEditor;
    DependentSimpleMainEditor; DependentSimplePartialEditor;
    DependentSimpleSplitEditor; SimpleEditor; SimpleInnerEditor;
    SimpleMainEditor; SimplePartialEditor; SimpleSplitEditor; editor-simple)
open import Editor.Unit
  using (editor-unit)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)

-- ## Base

-- ### SimpleEditor

simple-editor-map-view-with
  : {V W : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → (A → ViewStackMap V W)
  → SimpleEditor V E A
  → SimpleEditor W E A
simple-editor-map-view-with F
  = editor-simple
  ∘ editor-map-view-with F
  ∘ editor-unit
  
simple-editor-map-view
  : {V W : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → ViewStackMap V W
  → SimpleEditor V E A
  → SimpleEditor W E A
simple-editor-map-view F
  = simple-editor-map-view-with (const F)

-- ## Dependent

-- ### DependentSimpleEditor

dependent-simple-editor-map-view-with
  : {V W : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → DependentSimpleFunction C' (ViewStackMap V W)
  → DependentSimpleEditor V E C'
  → DependentSimpleEditor W E C'
dependent-simple-editor-map-view-with {n = zero} F e
  = simple-editor-map-view-with F e
dependent-simple-editor-map-view-with {n = suc _} F e
  = record
  { tail
    = λ x → dependent-simple-editor-map-view-with
      (DependentSimpleFunction.tail F x)
      (DependentSimpleEditor.tail e x)
  }

-- ### DependentSimplePartialEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentSet C}
  where

  dependent-simple-partial-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → DependentSimplePartialEditor V E C'
    → DependentSimplePartialEditor W E C'
  dependent-simple-partial-editor-map-view-with F e
    = record
    { DependentSimplePartialEditor e
    ; editor
      = dependent-simple-editor-map-view-with
        (dependent-simple-function-compose F
          (DependentSimplePartialEditor.bool-function e))
        (DependentSimplePartialEditor.editor e)
    }

  dependent-simple-partial-editor-map-view
    : ViewStackMap V W
    → DependentSimplePartialEditor V E C'
    → DependentSimplePartialEditor W E C'
  dependent-simple-partial-editor-map-view F
    = dependent-simple-partial-editor-map-view-with (const F)

-- ### DependentSimpleSplitEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentSimpleCategory C}
  where

  dependent-simple-split-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → DependentSimpleSplitEditor V E C'
    → DependentSimpleSplitEditor W E C'
  dependent-simple-split-editor-map-view-with F e
    = record
    { DependentSimpleSplitEditor e
    ; editor
      = dependent-simple-editor-map-view-with
        (dependent-simple-function-compose F
          (DependentSimpleSplitEditor.bool-function e))
        (DependentSimpleSplitEditor.editor e)
    }

  dependent-simple-split-editor-map-view
    : ViewStackMap V W
    → DependentSimpleSplitEditor V E C'
    → DependentSimpleSplitEditor W E C'
  dependent-simple-split-editor-map-view F
    = dependent-simple-split-editor-map-view-with (const F)

-- ### DependentSimpleMainEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {S : Set}
  {C : ChainCategory n}
  where

  dependent-simple-main-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → DependentSimpleMainEditor V E S C
    → DependentSimpleMainEditor W E S C
  dependent-simple-main-editor-map-view-with F e
    = record
    { DependentSimpleMainEditor e
    ; editor
      = dependent-simple-editor-map-view-with
        (dependent-simple-function-compose F
          (DependentSimpleMainEditor.bool-function e))
        (DependentSimpleMainEditor.editor e)
    }

  dependent-simple-main-editor-map-view
    : ViewStackMap V W
    → DependentSimpleMainEditor V E S C
    → DependentSimpleMainEditor W E S C
  dependent-simple-main-editor-map-view F
    = dependent-simple-main-editor-map-view-with (const F)

-- ### DependentSimpleInnerEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentSimpleCategory C}
  where

  dependent-simple-inner-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → DependentSimpleInnerEditor V E S P C'
    → DependentSimpleInnerEditor W E S P C'
  dependent-simple-inner-editor-map-view-with F e
    = record
    { DependentSimpleInnerEditor e
    ; editor
      = dependent-simple-editor-map-view-with
        (dependent-simple-function-compose F
          (DependentSimpleInnerEditor.bool-function e))
        (DependentSimpleInnerEditor.editor e)
    }

  dependent-simple-inner-editor-map-view
    : ViewStackMap V W
    → DependentSimpleInnerEditor V E S P C'
    → DependentSimpleInnerEditor W E S P C'
  dependent-simple-inner-editor-map-view F
    = dependent-simple-inner-editor-map-view-with (const F)

-- ## Nondependent

-- ### SimplePartialEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {A : Set}
  where

  simple-partial-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → SimplePartialEditor V E A
    → SimplePartialEditor W E A
  simple-partial-editor-map-view-with
    = dependent-simple-partial-editor-map-view-with

  simple-partial-editor-map-view
    : ViewStackMap V W
    → SimplePartialEditor V E A
    → SimplePartialEditor W E A
  simple-partial-editor-map-view
    = dependent-simple-partial-editor-map-view

-- ### SimpleSplitEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {A : Set}
  where

  simple-split-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → SimpleSplitEditor V E A
    → SimpleSplitEditor W E A
  simple-split-editor-map-view-with
    = dependent-simple-split-editor-map-view-with

  simple-split-editor-map-view
    : ViewStackMap V W
    → SimpleSplitEditor V E A
    → SimpleSplitEditor W E A
  simple-split-editor-map-view
    = dependent-simple-split-editor-map-view

-- ### SimpleMainEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S : Set}
  where

  simple-main-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → SimpleMainEditor V E S
    → SimpleMainEditor W E S
  simple-main-editor-map-view-with
    = dependent-simple-main-editor-map-view-with

  simple-main-editor-map-view
    : ViewStackMap V W
    → SimpleMainEditor V E S
    → SimpleMainEditor W E S
  simple-main-editor-map-view
    = dependent-simple-main-editor-map-view

-- ### SimpleInnerEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S P A : Set}
  where

  simple-inner-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → SimpleInnerEditor V E S P A
    → SimpleInnerEditor W E S P A
  simple-inner-editor-map-view-with
    = dependent-simple-inner-editor-map-view-with

  simple-inner-editor-map-view
    : ViewStackMap V W
    → SimpleInnerEditor V E S P A
    → SimpleInnerEditor W E S P A
  simple-inner-editor-map-view
    = dependent-simple-inner-editor-map-view

