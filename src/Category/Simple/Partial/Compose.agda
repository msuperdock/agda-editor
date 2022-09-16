module Category.Simple.Partial.Compose where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSet)
open import Category.Simple.Partial
  using (DependentSimplePartialFunction; DependentSimplePartialFunction')
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

partial-function-compose
  : {A B C : Set}
  → (B → Maybe C)
  → (A → Maybe B)
  → (A → Maybe C)
partial-function-compose f g x
  with g x
... | nothing
  = nothing
... | just x'
  = f x'

-- ## Dependent

dependent-simple-partial-function-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → {D' E' : DependentSet C}
  → DependentSimplePartialFunction' D' E'
  → DependentSimplePartialFunction C' D'
  → DependentSimplePartialFunction C' E'
dependent-simple-partial-function-compose {n = zero} F G
  = partial-function-compose F G
dependent-simple-partial-function-compose {n = suc _} F G
  = record
  { tail
    = λ x → dependent-simple-partial-function-compose
      (DependentSimplePartialFunction'.tail F x)
      (DependentSimplePartialFunction.tail G x)
  }

