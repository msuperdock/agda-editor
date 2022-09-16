module Category.Symbol where

open import Category
  using (ChainCategory; chain-category₀)
open import Category.Core.Symbol
  using (dependent-compose-symbol; dependent-identity-symbol)
open import Category.Lift
  using (DependentLift)
open import Category.Symbol.Core
  using (DependentSymbol)
open import Data.Nat
  using (ℕ; suc)
open import Data.Symbol
  using (Symbol')

-- ## Dependent

-- ### Definition

record DependentSymbolCategory'
  (S : Set)
  {n : ℕ}
  (C : ChainCategory n)
  : Set₁
  where

  field

    symbol
      : DependentSymbol S
        (ChainCategory.object C)

    lift
      : DependentLift
        (ChainCategory.identity C)
        (dependent-identity-symbol symbol)
        (ChainCategory.compose C)
        (dependent-compose-symbol symbol symbol symbol)
        (ChainCategory.lift C)

DependentSymbolCategory
  = DependentSymbolCategory'

-- ### Module

module DependentSymbolCategory where

  open module DependentSymbolCategory'' {S n C} C'
    = DependentSymbolCategory' {S} {n} {C} C' public

  tail
    : {S : Set}
    → {n : ℕ}
    → {C : ChainCategory (suc n)}
    → DependentSymbolCategory S C
    → (x : ChainCategory.Object C)
    → DependentSymbolCategory S
      (ChainCategory.tail C x)
  tail C' x
    = record
    { symbol
      = DependentSymbol.tail (symbol C') x
    ; lift
      = DependentLift.tail (lift C') x
    }

-- ## Nondependent

-- ### Definition

SymbolCategory
  : Set
  → Set₁
SymbolCategory S
  = DependentSymbolCategory S
    chain-category₀

-- ### Module

module SymbolCategory
  {S : Set}
  (C : SymbolCategory S)
  where

  open DependentSymbolCategory' C public

  open Symbol' symbol public

