module Encoding.State.List where

open import Category
  using (ChainCategory)
open import Category.State
  using (DependentStateCategory)
open import Category.State.List
  using (dependent-state-category-list)
open import Data.List
  using (List)
open import Data.Nat
  using (ℕ; suc; zero)
open import Encoding.List
  using (encoding-list)
open import Encoding.State
  using (DependentStateEncoding)

-- ## Dependent

dependent-state-encoding-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → {A : Set}
  → DependentStateEncoding C' A
  → DependentStateEncoding
    (dependent-state-category-list C')
    (List A)
dependent-state-encoding-list {n = zero} e
  = encoding-list e
dependent-state-encoding-list {n = suc _} e
  = record
  { tail
    = λ x → dependent-state-encoding-list
      (DependentStateEncoding.tail e x)
  }

