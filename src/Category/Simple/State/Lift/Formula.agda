module Category.Simple.State.Lift.Formula where

open import Category
  using (ChainCategory)
open import Category.Simple.State.Lift
  using (DependentSimpleStateLift)
open import Data.Nat
  using (ℕ)

-- ## Dependent

dependent-simple-state-lift-formula
  : {S : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → ?
  → DependentSimpleStateLift ? ? ?
dependent-simple-state-lift-formula
  = ?

