module Category.Simple.Bool.List where

open import Category
  using (ChainCategory)
open import Category.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.List
  using (dependent-simple-state-category-list)
open import Data.Bool
  using (Bool; _∧_; true)
open import Data.List
  using (List; []; _∷_)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

bool-function-list
  : {A : Set}
  → (A → Bool)
  → (List A → Bool)
bool-function-list _ []
  = true
bool-function-list f (x ∷ xs)
  = f x ∧ bool-function-list f xs

-- ## Dependent

dependent-simple-bool-function-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → DependentSimpleBoolFunction C'
  → DependentSimpleBoolFunction
    (dependent-simple-state-category-list C')
dependent-simple-bool-function-list {n = zero} F
  = bool-function-list F
dependent-simple-bool-function-list {n = suc _} F
  = record
  { tail
    = λ x → dependent-simple-bool-function-list
      (DependentSimpleBoolFunction.tail F x)
  }

