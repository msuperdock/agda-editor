module Category.Function.Compose where

open import Category
  using (ChainCategory)
open import Category.Function
  using (DependentFunction)
open import Category.State
  using (DependentStateCategory)
open import Data.Function
  using (_∘_)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Dependent

dependent-function-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → {A B : Set}
  → (A → B)
  → DependentFunction C' A
  → DependentFunction C' B
dependent-function-compose {n = zero} f g
  = f ∘ g
dependent-function-compose {n = suc _} f G
  = record
  { tail
    = λ x → dependent-function-compose f
      (DependentFunction.tail G x)
  }

