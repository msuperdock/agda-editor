module Encoding.Compose where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Core
  using (Object')
open import Category.Split
  using (DependentSplitFunctor'; SplitFunctor')
open import Category.Split.Core
  using (SplitBase)
open import Category.Split.Core.Compose
  using (split-base-compose)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ; suc; zero)
open import Encoding
  using (DependentEncoding; Encoding; split-base-encoding)

-- ## Base

encoding-compose
  : {A B C : Set}
  → Encoding B C
  → Encoding A B
  → Encoding A C
encoding-compose e f
  = split-base-encoding
  $ split-base-compose
    (Encoding.split-base f)
    (Encoding.split-base e)

encoding-compose'
  : {X X' : Object'}
  → {A : Set}
  → SplitBase X X'
  → Encoding (Object'.Object X) A
  → Encoding (Object'.Object X') A
encoding-compose' a e
  = split-base-encoding
  $ split-base-compose a
    (Encoding.split-base e)

-- ## Dependent

dependent-encoding-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {A B : Set}
  → Encoding A B
  → DependentEncoding C' A
  → DependentEncoding C' B
dependent-encoding-compose {n = zero} e f
  = encoding-compose e f
dependent-encoding-compose {n = suc _} e f
  = record
  { tail
    = λ x → dependent-encoding-compose e
      (DependentEncoding.tail f x)
  }

dependent-encoding-compose'
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentCategory C}
  → {A : Set}
  → DependentSplitFunctor' C' D'
  → DependentEncoding C' A
  → DependentEncoding D' A
dependent-encoding-compose' {n = zero} F e
  = encoding-compose' (SplitFunctor'.base F) e
dependent-encoding-compose' {n = suc _} F e
  = record
  { tail
    = λ x → dependent-encoding-compose'
      (DependentSplitFunctor'.tail F x)
      (DependentEncoding.tail e x)
  }

