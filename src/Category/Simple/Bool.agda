module Category.Simple.Bool where

open import Category
  using (ChainCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.Function
  using (DependentSimpleFunction)
open import Data.Bool
  using (Bool)
open import Data.Nat
  using (ℕ)

-- ## Dependent

DependentSimpleBoolFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleStateCategory C
  → Set
DependentSimpleBoolFunction C'
  = DependentSimpleFunction C' Bool

module DependentSimpleBoolFunction
  = DependentSimpleFunction

