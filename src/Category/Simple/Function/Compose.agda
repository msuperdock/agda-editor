module Category.Simple.Function.Compose where

open import Category
  using (ChainCategory)
open import Category.Simple.Function
  using (DependentSimpleFunction)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Data.Function
  using (_∘_)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Dependent

dependent-simple-function-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → {A B : Set}
  → (A → B)
  → DependentSimpleFunction C' A
  → DependentSimpleFunction C' B
dependent-simple-function-compose {n = zero} f g
  = f ∘ g
dependent-simple-function-compose {n = suc _} f G
  = record
  { tail
    = λ x → dependent-simple-function-compose f
      (DependentSimpleFunction.tail G x)
  }

