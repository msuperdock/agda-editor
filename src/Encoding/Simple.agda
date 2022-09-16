module Encoding.Simple where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Simple
  using (DependentSimpleCategory; SimpleCategory; dependent-category-simple)
open import Data.Nat
  using (ℕ; suc; zero)
open import Encoding
  using (DependentEncoding; Encoding)

-- ## Dependent

-- ### Types

DependentSimpleEncoding
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → Set
  → Set

record DependentSimpleEncoding'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSimpleCategory C)
  (A : Set)
  : Set

-- ### Definitions

DependentSimpleEncoding {n = zero} C'
  = Encoding (SimpleCategory.Object C')
DependentSimpleEncoding {n = suc _} C'
  = DependentSimpleEncoding' C'

record DependentSimpleEncoding' {_ C} C' A where

  inductive

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentSimpleEncoding
        (DependentSimpleCategory.tail C' x) A

module DependentSimpleEncoding
  = DependentSimpleEncoding'

-- ### Conversion

dependent-encoding-simple
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {A : Set}
  → DependentEncoding C' A
  → DependentSimpleEncoding
    (dependent-category-simple C') A
dependent-encoding-simple {n = zero} e
  = e
dependent-encoding-simple {n = suc _} e
  = record
  { tail
    = λ x → dependent-encoding-simple
      (DependentEncoding.tail e x)
  }

