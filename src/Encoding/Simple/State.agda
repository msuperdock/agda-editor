module Encoding.Simple.State where

open import Category
  using (ChainCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory; SimpleStateCategory;
    dependent-state-category-simple)
open import Category.State
  using (DependentStateCategory)
open import Data.Nat
  using (ℕ; suc; zero)
open import Encoding
  using (Encoding)
open import Encoding.State
  using (DependentStateEncoding)

-- ## Dependent

-- ### Types

DependentSimpleStateEncoding
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleStateCategory C
  → Set
  → Set

record DependentSimpleStateEncoding'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSimpleStateCategory C)
  (A : Set)
  : Set

-- ### Definitions

DependentSimpleStateEncoding {n = zero} C'
  = Encoding (SimpleStateCategory.Object C')
DependentSimpleStateEncoding {n = suc _} C'
  = DependentSimpleStateEncoding' C'

record DependentSimpleStateEncoding' {_ C} C' A where

  inductive

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentSimpleStateEncoding
        (DependentSimpleStateCategory.tail C' x) A

module DependentSimpleStateEncoding
  = DependentSimpleStateEncoding'

-- ### Conversion

dependent-state-encoding-simple
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → {A : Set}
  → DependentStateEncoding C' A
  → DependentSimpleStateEncoding
    (dependent-state-category-simple C') A
dependent-state-encoding-simple {n = zero} e
  = e
dependent-state-encoding-simple {n = suc _} e
  = record
  { tail
    = λ x → dependent-state-encoding-simple
      (DependentStateEncoding.tail e x)
  }

