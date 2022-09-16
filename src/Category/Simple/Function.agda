module Category.Simple.Function where

open import Category
  using (ChainCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory; SimpleStateCategory)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Dependent

-- ### Types

DependentSimpleFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleStateCategory C
  → Set
  → Set

record DependentSimpleFunction'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSimpleStateCategory C)
  (A : Set)
  : Set

-- ### Definitions

DependentSimpleFunction {n = zero} C' A
  = SimpleStateCategory.Object C' → A
DependentSimpleFunction {n = suc _} C' A
  = DependentSimpleFunction' C' A

record DependentSimpleFunction' {_ C} C' A where

  inductive

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentSimpleFunction
        (DependentSimpleStateCategory.tail C' x) A

module DependentSimpleFunction
  = DependentSimpleFunction'

