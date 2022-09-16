module Category.Simple.Partial.List where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSet)
open import Category.Simple.Partial
  using (DependentSimplePartialFunction)
open import Category.Simple.List
  using (dependent-set-list)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.List
  using (dependent-simple-state-category-list)
open import Data.List
  using (List; []; _∷_)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

partial-function-list
  : {A B : Set}
  → (A → Maybe B)
  → (List A → Maybe (List B))
partial-function-list _ []
  = just []
partial-function-list f (x ∷ xs)
  with f x
  | partial-function-list f xs
... | nothing | _
  = nothing
... | _ | nothing
  = nothing
... | just x' | just xs'
  = just (x' ∷ xs')

-- ## Dependent

dependent-simple-partial-function-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → {D' : DependentSet C}
  → DependentSimplePartialFunction C' D'
  → DependentSimplePartialFunction
    (dependent-simple-state-category-list C')
    (dependent-set-list D')
dependent-simple-partial-function-list {n = zero} F
  = partial-function-list F
dependent-simple-partial-function-list {n = suc _} F
  = record
  { tail
    = λ x → dependent-simple-partial-function-list
      (DependentSimplePartialFunction.tail F x)
  }

