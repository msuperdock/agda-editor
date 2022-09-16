module Encoding.Simple.Compose where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Split
  using (DependentSimpleSplitFunctor'; SimpleSplitFunctor')
open import Data.Nat
  using (ℕ; suc; zero)
open import Encoding
  using (Encoding)
open import Encoding.Compose
  using (encoding-compose; encoding-compose')
open import Encoding.Simple
  using (DependentSimpleEncoding)

-- ## Dependent

dependent-simple-encoding-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {A B : Set}
  → Encoding A B
  → DependentSimpleEncoding C' A
  → DependentSimpleEncoding C' B
dependent-simple-encoding-compose {n = zero} e f
  = encoding-compose e f
dependent-simple-encoding-compose {n = suc _} e f
  = record
  { tail
    = λ x → dependent-simple-encoding-compose e
      (DependentSimpleEncoding.tail f x)
  }

dependent-simple-encoding-compose'
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentSimpleCategory C}
  → {A : Set}
  → DependentSimpleSplitFunctor' C' D'
  → DependentSimpleEncoding C' A
  → DependentSimpleEncoding D' A
dependent-simple-encoding-compose' {n = zero} F e
  = encoding-compose' (SimpleSplitFunctor'.base F) e
dependent-simple-encoding-compose' {n = suc _} F e
  = record
  { tail
    = λ x → dependent-simple-encoding-compose'
      (DependentSimpleSplitFunctor'.tail F x)
      (DependentSimpleEncoding.tail e x)
  }

