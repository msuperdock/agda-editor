module Encoding.Unit where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Unit
  using (dependent-category-unit)
open import Data.Nat
  using (ℕ; suc; zero)
open import Encoding
  using (DependentEncoding)
open import Encoding.Simple
  using (DependentSimpleEncoding)

-- ## Dependent

dependent-encoding-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {A : Set}
  → DependentSimpleEncoding C' A
  → DependentEncoding
    (dependent-category-unit C') A
dependent-encoding-unit {n = zero} e
  = e
dependent-encoding-unit {n = suc _} e
  = record
  { tail
    = λ x → dependent-encoding-unit
      (DependentSimpleEncoding.tail e x)
  }

