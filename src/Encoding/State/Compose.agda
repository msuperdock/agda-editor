module Encoding.State.Compose where

open import Category
  using (ChainCategory)
open import Category.State
  using (DependentStateCategory)
open import Data.Nat
  using (ℕ; suc; zero)
open import Encoding
  using (Encoding)
open import Encoding.Compose
  using (encoding-compose)
open import Encoding.State
  using (DependentStateEncoding)

-- ## Dependent

dependent-state-encoding-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → {A B : Set}
  → Encoding A B
  → DependentStateEncoding C' A
  → DependentStateEncoding C' B
dependent-state-encoding-compose {n = zero} e f
  = encoding-compose e f
dependent-state-encoding-compose {n = suc _} e f
  = record
  { tail
    = λ x → dependent-state-encoding-compose e
      (DependentStateEncoding.tail f x)
  }

