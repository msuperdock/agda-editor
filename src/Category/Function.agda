module Category.Function where

open import Category
  using (ChainCategory)
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Dependent

-- ### Types

DependentFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentStateCategory C
  → Set
  → Set

record DependentFunction'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentStateCategory C)
  (A : Set)
  : Set

-- ### Definitions

DependentFunction {n = zero} C' A
  = StateCategory.Object C' → A
DependentFunction {n = suc _} C' A
  = DependentFunction' C' A

record DependentFunction' {_ C} C' A where

  inductive

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentFunction
        (DependentStateCategory.tail C' x) A

module DependentFunction
  = DependentFunction'

