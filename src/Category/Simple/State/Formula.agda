module Category.Simple.State.Formula where

open import Category
  using (ChainCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Symbol
  using (DependentSymbol)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-simple-state-category-formula
  : {S : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → DependentSymbol S C
  → DependentSimpleStateCategory C
dependent-simple-state-category-formula _
  = record
  { lift
    = ?
  }

