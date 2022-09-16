module Encoding.Simple.State.Compose where

open import Category
  using (ChainCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Data.Nat
  using (ℕ; suc; zero)
open import Encoding
  using (Encoding)
open import Encoding.Compose
  using (encoding-compose)
open import Encoding.Simple.State
  using (DependentSimpleStateEncoding)

-- ## Dependent

dependent-simple-state-encoding-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → {A B : Set}
  → Encoding A B
  → DependentSimpleStateEncoding C' A
  → DependentSimpleStateEncoding C' B
dependent-simple-state-encoding-compose {n = zero} e f
  = encoding-compose e f
dependent-simple-state-encoding-compose {n = suc _} e f
  = record
  { tail
    = λ x → dependent-simple-state-encoding-compose e
      (DependentSimpleStateEncoding.tail f x)
  }

