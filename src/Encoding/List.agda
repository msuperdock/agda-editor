module Encoding.List where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.List
  using (dependent-category-list)
open import Category.Split.Core.List
  using (split-base-list)
open import Data.Function
  using (_$_)
open import Data.List
  using (List)
open import Data.Nat
  using (ℕ; suc; zero)
open import Encoding
  using (DependentEncoding; Encoding; split-base-encoding)

-- ## Base

encoding-list
  : {A B : Set}
  → Encoding A B
  → Encoding (List A) (List B)
encoding-list e
  = split-base-encoding
  $ split-base-list
    (Encoding.split-base e)

-- ## Dependent

dependent-encoding-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {A : Set}
  → DependentEncoding C' A
  → DependentEncoding
    (dependent-category-list C')
    (List A)
dependent-encoding-list {n = zero} e
  = encoding-list e
dependent-encoding-list {n = suc _} e
  = record
  { tail
    = λ x → dependent-encoding-list
      (DependentEncoding.tail e x)
  }

