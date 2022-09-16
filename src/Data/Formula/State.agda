module Data.Formula.State where

open import Data.Any
  using (Any; any)
open import Data.Bool
  using (Bool; false; true)
open import Data.Symbol
  using (Symbol')
open import Data.If
  using (If; just; nothing)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; π₁)
open import Data.Vec
  using (Vec)

-- ## Definitions

module _
  {S : Set}
  where

  data FormulaState
    (S' : Symbol' S)
    : Set

  data SandboxState
    (S' : Symbol' S)
    : ℕ
    → Set

  data FormulaStateLeftClosed
    {S' : Symbol' S}
    : FormulaState S'
    → Set

  data FormulaStateRightClosed
    {S' : Symbol' S}
    : FormulaState S'
    → Set

  formula-state-root
    : {S' : Symbol' S}
    → FormulaState S'
    → Maybe (Symbol'.Symbol S')

  sandbox-state-head
    : {S' : Symbol' S}
    → Any (SandboxState S')
    → FormulaState S'

  data FormulaState S' where

    hole
      : FormulaState S'

    symbol
      : {l r : Bool}
      → {n : ℕ}
      → (s : Symbol'.SymbolWith S' l r n)
      → If (f ∈ FormulaState S'
        × Symbol'.LeftValid S' s (formula-state-root f)) l
      → If (f ∈ FormulaState S'
        × Symbol'.RightValid S' s (formula-state-root f)) r
      → Vec (Any (SandboxState S')) n
      → FormulaState S'

  data SandboxState S' where

    singleton
      : FormulaState S'
      → SandboxState S' zero

    cons
      : (f : FormulaState S')
      → FormulaStateRightClosed f
      → (s : Any (SandboxState S'))
      → FormulaStateLeftClosed (sandbox-state-head s)
      → SandboxState S' (suc (Any.index s))

  data FormulaStateLeftClosed {S'} where

    nothing
      : {r : Bool}
      → {n : ℕ}
      → {s : Symbol'.SymbolWith S' false r n}
      → {r' : If (f ∈ FormulaState S'
        × Symbol'.RightValid S' s (formula-state-root f)) r}
      → {ss : Vec (Any (SandboxState S')) n}
      → FormulaStateLeftClosed (symbol s nothing r' ss)

    just
      : {r : Bool}
      → {n : ℕ}
      → (s : Symbol'.SymbolWith S' true r n)
      → {l' : f ∈ FormulaState S'
        × Symbol'.LeftValid S' s (formula-state-root f)}
      → {r' : If (f ∈ FormulaState S'
        × Symbol'.RightValid S' s (formula-state-root f)) r}
      → {ss : Vec (Any (SandboxState S')) n}
      → FormulaStateLeftClosed (π₁ l')
      → FormulaStateLeftClosed (symbol s (just l') r' ss)

  data FormulaStateRightClosed {S'} where

    nothing
      : {l : Bool}
      → {n : ℕ}
      → {s : Symbol'.SymbolWith S' l false n}
      → {l' : If (f ∈ FormulaState S'
        × Symbol'.LeftValid S' s (formula-state-root f)) l}
      → {ss : Vec (Any (SandboxState S')) n}
      → FormulaStateRightClosed (symbol s l' nothing ss)

    just
      : {l : Bool}
      → {n : ℕ}
      → (s : Symbol'.SymbolWith S' l true n)
      → {l' : If (f ∈ FormulaState S'
        × Symbol'.LeftValid S' s (formula-state-root f)) l}
      → {r' : f ∈ FormulaState S'
        × Symbol'.RightValid S' s (formula-state-root f)}
      → {ss : Vec (Any (SandboxState S')) n}
      → FormulaStateRightClosed (π₁ r')
      → FormulaStateRightClosed (symbol s l' (just r') ss)

  formula-state-root hole
    = nothing
  formula-state-root (symbol (Symbol'.symbol-with s) _ _ _)
    = just s

  sandbox-state-head (any (singleton f))
    = f
  sandbox-state-head (any (cons f _ _ _))
    = f

