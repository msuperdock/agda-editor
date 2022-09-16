module Encoding.State.Unit where

open import Category
  using (ChainCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.State.Unit
  using (dependent-state-category-unit)
open import Data.Nat
  using (ℕ; suc; zero)
open import Encoding.Simple.State
  using (DependentSimpleStateEncoding)
open import Encoding.State
  using (DependentStateEncoding)

-- ## Dependent

dependent-state-encoding-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → {A : Set}
  → DependentSimpleStateEncoding C' A
  → DependentStateEncoding
    (dependent-state-category-unit C') A
dependent-state-encoding-unit {n = zero} e
  = e
dependent-state-encoding-unit {n = suc _} e
  = record
  { tail
    = λ x → dependent-state-encoding-unit
      (DependentSimpleStateEncoding.tail e x)
  }

