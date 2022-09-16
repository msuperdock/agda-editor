module Category.Snoc where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Core.Snoc
  using (chain-compose-snoc; chain-identity-snoc)
open import Category.Lift.Snoc
  using (chain-lift-snoc)
open import Data.Nat
  using (ℕ; suc)

-- ### Chain

chain-category-snoc
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → ChainCategory (suc n)
chain-category-snoc {C = C} C'
  = record
  { identity
    = chain-identity-snoc
      (ChainCategory.identity C)
      (DependentCategory.identity C')
  ; compose
    = chain-compose-snoc
      (ChainCategory.compose C)
      (DependentCategory.compose C')
  ; lift
    = chain-lift-snoc
      (DependentCategory.lift C')
  }

