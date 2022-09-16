module Editor.Simple.Formula where

open import Category
  using (ChainCategory)
open import Category.Symbol
  using (DependentSymbolCategory; SymbolCategory)
open import Data.Any
  using (Any)
open import Data.Formula
  using (Formula)
open import Data.Formula.State
  using (SandboxState)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Symbol
  using (Symbol')
open import Editor.Flat
  using (FlatEditor)
open import Editor.Simple
  using (DependentSimpleEditor; DependentSimpleInnerEditor;
    DependentSimpleMainEditor; DependentSimplePartialEditor;
    DependentSimpleSplitEditor; SimpleEditor; SimpleInnerEditor;
    SimpleMainEditor; SimplePartialEditor; SimpleSplitEditor)
open import Editor.Simple.Map.Event
  using (simple-editor-map-event)
open import Editor.Simple.Parent
  using (simple-editor-parent)
open import Event.Formula
  using (FormulaEvent)
open import Stack.Base
  using (BaseEventStack; base-event-stack-map)
open import Stack.Base.RichText
  using (base-view-stack-rich-text)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack)
open import Stack.Parent
  using (event-stack-map-parent; event-stack-parent; view-stack-parent)

-- ## Base

-- ### FormulaEditor

record FormulaEditor
  {K S : Set}
  (V' : K → FlatViewStack)
  (E : BaseEventStack)
  (E' : K → FlatEventStack)
  (S' : Symbol' S)
  : Set₁
  where

  field

    event
      : BaseEventStack.Event E
      → FormulaEvent S'

    flat-editor
      : (k : K)
      → FlatEditor (V' k) (E' k) (FormulaEvent S')

-- ### SimpleEditor

simple-editor-formula
  : {K S : Set}
  → {V' : K → FlatViewStack}
  → {E : BaseEventStack}
  → {E' : K → FlatEventStack}
  → {S' : Symbol' S}
  → FormulaEditor V' E E' S'
  → SimpleEditor
    (view-stack-parent (base-view-stack-rich-text S) V')
    (event-stack-parent E E')
    (Any (SandboxState S'))
simple-editor-formula {V' = V'} {E' = E'} e
  = simple-editor-map-event
    (event-stack-map-parent E' (base-event-stack-map (FormulaEditor.event e)))
  $ simple-editor-parent V' E'
    ?
    (FormulaEditor.flat-editor e)

-- ## Dependent

-- ### DependentFormulaEditor

-- #### Types

DependentFormulaEditor
  : {K S : Set}
  → (V' : K → FlatViewStack)
  → (E : BaseEventStack)
  → (E' : K → FlatEventStack)
  → {n : ℕ}
  → {C : ChainCategory n}
  → DependentSymbolCategory S C
  → Set₁

record DependentFormulaEditor'
  {K S : Set}
  (V' : K → FlatViewStack)
  (E : BaseEventStack)
  (E' : K → FlatEventStack)
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSymbolCategory S C)
  : Set₁

-- #### Definitions

DependentFormulaEditor V' E E' {n = zero} C'
  = FormulaEditor V' E E' (SymbolCategory.symbol C')
DependentFormulaEditor V' E E' {n = suc _} C'
  = DependentFormulaEditor' V' E E' C'

record DependentFormulaEditor' V' E E' {C = C} C' where

  inductive

  field
  
    tail
      : (x : ChainCategory.Object C)
      → DependentFormulaEditor V' E E'
        (DependentSymbolCategory.tail C' x)

module DependentFormulaEditor
  = DependentFormulaEditor'

-- ### DependentSimpleEditor

dependent-simple-editor-formula
  : {K S : Set}
  → {V' : K → FlatViewStack}
  → {E : BaseEventStack}
  → {E' : K → FlatEventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSymbolCategory S C}
  → DependentFormulaEditor V' E E' C'
  → DependentSimpleEditor
    (view-stack-parent (base-view-stack-rich-text S) V')
    (event-stack-parent E E')
    ?
dependent-simple-editor-formula
  = ?

-- ### DependentSimplePartialEditor

dependent-simple-partial-editor-formula
  : {K S : Set}
  → {V' : K → FlatViewStack}
  → {E : BaseEventStack}
  → {E' : K → FlatEventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSymbolCategory S C}
  → DependentFormulaEditor V' E E' C'
  → DependentSimplePartialEditor
    (view-stack-parent (base-view-stack-rich-text S) V')
    (event-stack-parent E E')
    ?
dependent-simple-partial-editor-formula
  = ?

-- ### DependentSimpleSplitEditor

dependent-simple-split-editor-formula
  : {K S : Set}
  → {V' : K → FlatViewStack}
  → {E : BaseEventStack}
  → {E' : K → FlatEventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSymbolCategory S C}
  → DependentFormulaEditor V' E E' C'
  → DependentSimpleSplitEditor
    (view-stack-parent (base-view-stack-rich-text S) V')
    (event-stack-parent E E')
    ?
dependent-simple-split-editor-formula
  = ?

-- ### DependentSimpleMainEditor

dependent-simple-main-editor-formula
  : {K S : Set}
  → {V' : K → FlatViewStack}
  → {E : BaseEventStack}
  → {E' : K → FlatEventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSymbolCategory S C}
  → DependentFormulaEditor V' E E' C'
  → DependentSimpleMainEditor
    (view-stack-parent (base-view-stack-rich-text S) V')
    (event-stack-parent E E')
    ? C
dependent-simple-main-editor-formula
  = ?

-- ### DependentSimpleInnerEditor

dependent-simple-inner-editor-formula
  : {K S : Set}
  → {V' : K → FlatViewStack}
  → {E : BaseEventStack}
  → {E' : K → FlatEventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSymbolCategory S C}
  → DependentFormulaEditor V' E E' C'
  → DependentSimpleInnerEditor
    (view-stack-parent (base-view-stack-rich-text S) V')
    (event-stack-parent E E')
    ?
    ?
    ?
dependent-simple-inner-editor-formula
  = ?

-- ## Nondependent

-- ### SimplePartialEditor

simple-partial-editor-formula
  : {K S : Set}
  → {V' : K → FlatViewStack}
  → {E : BaseEventStack}
  → {E' : K → FlatEventStack}
  → {S' : Symbol' S}
  → FormulaEditor V' E E' S'
  → SimplePartialEditor
    (view-stack-parent (base-view-stack-rich-text S) V')
    (event-stack-parent E E')
    (Formula S')
simple-partial-editor-formula
  = ?

-- ### SimpleSplitEditor

simple-split-editor-formula
  : {K S : Set}
  → {V' : K → FlatViewStack}
  → {E : BaseEventStack}
  → {E' : K → FlatEventStack}
  → {S' : Symbol' S}
  → FormulaEditor V' E E' S'
  → SimpleSplitEditor
    (view-stack-parent (base-view-stack-rich-text S) V')
    (event-stack-parent E E')
    (Formula S')
simple-split-editor-formula
  = ?

-- ### SimpleMainEditor

simple-main-editor-formula
  : {K S : Set}
  → {V' : K → FlatViewStack}
  → {E : BaseEventStack}
  → {E' : K → FlatEventStack}
  → {S' : Symbol' S}
  → FormulaEditor V' E E' S'
  → SimpleMainEditor
    (view-stack-parent (base-view-stack-rich-text S) V')
    (event-stack-parent E E')
    ?
simple-main-editor-formula
  = ?

-- ### SimpleInnerEditor

simple-inner-editor-formula
  : {K S : Set}
  → {V' : K → FlatViewStack}
  → {E : BaseEventStack}
  → {E' : K → FlatEventStack}
  → {S' : Symbol' S}
  → FormulaEditor V' E E' S'
  → SimpleInnerEditor
    (view-stack-parent (base-view-stack-rich-text S) V')
    (event-stack-parent E E')
    ?
    ?
    (Formula S')
simple-inner-editor-formula
  = ?

