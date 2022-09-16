module Encoding.State where

open import Category
  using (ChainCategory)
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Data.Nat
  using (ℕ; suc; zero)
open import Encoding
  using (Encoding)

-- ## Dependent

-- ### Types

DependentStateEncoding
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentStateCategory C
  → Set
  → Set

record DependentStateEncoding'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentStateCategory C)
  (A : Set)
  : Set

-- ### Definitions

DependentStateEncoding {n = zero} C'
  = Encoding (StateCategory.Object C')
DependentStateEncoding {n = suc _} C'
  = DependentStateEncoding' C'

record DependentStateEncoding' {_ C} C' A where

  inductive

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentStateEncoding
        (DependentStateCategory.tail C' x) A

module DependentStateEncoding
  = DependentStateEncoding'

